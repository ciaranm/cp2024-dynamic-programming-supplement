import argparse
from functools import cache
from pathlib import Path


class ProofManager:
    def __init__(self, n_vertices, edges, flow_cons, target_path):
        self.target_path = target_path
        self.n_vertices = n_vertices
        self.edges = edges
        self.big_m = 2 * sum(abs(w) for _, _, w in self.edges)
        self.flow_cons = flow_cons
        self.at_most_ones = dict()
        self.counter = max(flow_cons.values())
        self.write_line('pseudo-Boolean proof version 1.2', is_constraint=False)
        self.write_line(f'f {self.counter} 0', is_constraint=False)


    def run(self):
        self.derive_at_most_ones()
        score, path, bound = self.generate_proof(self.n_vertices - 1)
        remove_big_m = self.write_line('rup', f'1 d[{self.n_vertices - 1}]', '>= 1', ';')
        final_bound = self.write_line('pol', f'{bound} 1 *', f'{remove_big_m} {self.big_m} *', '+')
        if score is not None:
            self.write_line('output NONE', is_constraint=False)
            self.write_line(f'conclusion BOUNDS {score} : {final_bound} {score} : ' +
                            ' '.join(f'x[{u}][{v}]' if (u, v) in path else f'~x[{u}][{v}]' for u, v, _ in self.edges), is_constraint=False)
            self.write_line('end pseudo-Boolean proof', is_constraint=False)
        else:
            contradiction = self.write_line('rup', '>=', '1', ';')
            self.write_line('c', f'{contradiction}')


    @cache
    def generate_proof(self, target):
        if target == 0:
            return 0, list(), None
        vertices_in = {
            u: w
            for (u, v, w) in self.edges
            if v == target
        }
        inbounds = {v: self.generate_proof(v) for v in vertices_in}
        dist, path = None, None
        for v, (dist_v, path_v, _) in inbounds.items():
            if dist_v is not None:
                total_dist_v = dist_v + vertices_in[v]
                if dist is None or total_dist_v < dist:
                    dist, path = total_dist_v, path_v + [(v, target)]
        bound = None
        if dist is None:
            bound = self.write_line('rup', f'1 ~d[{target}]', '>= 1', ';')
        else:
            edge_bounds = dict()
            for v in inbounds:
                if v > 0:
                    self.write_line('rup', f'1 ~d[{target}]', f'1 ~x[{v}][{target}]', f'1 d[{v}]', '>= 1', ';')
                edge_bounds[v] = self.write_line(
                    'red',
                    f'{self.big_m} ~d[{target}]',
                    f'{self.big_m} ~x[{v}][{target}]',
                    *[f'{w} x[{u}][{v}]'for u, v, w in self.edges if v <= target],
                    '>=', f'{dist}', ';',
                    f'd[{target}] -> 1', f'x[{v}][{target}] -> 1',
                )
        
            bound_pos = self.write_line(
                'red',
                f'{self.big_m} ~q[{target}]',
                *[f'{w} x[{u}][{v}]'for u, v, w in self.edges if v <= target],
                '>=', f'{dist}', ';',
                f'q[{target}] -> 0',
            )
            bound_neg = self.write_line(
                'red',
                f'{self.big_m} q[{target}]',
                *[f'{-w} x[{u}][{v}]'for u, v, w in self.edges if v <= target],
                '>=', f'{1 - dist}', ';',
                f'q[{target}] -> 1',
            )
            for v, edge_bound in edge_bounds.items():
                self.write_line('pol', f'{bound_neg} 1 *', f'{edge_bound} 1 *', '+')
            impl = self.write_line('rup', f'1 ~d[{target}]', f'1 q[{target}]', '>= 1', ';')
            bound = self.write_line('pol', f'{impl} {self.big_m} *', f'{bound_pos} 1 *', '+')
        self.write_line(f'* Justified the bound {dist} for path segment to {target}', is_constraint=False)
        return dist, path, bound


    def derive_at_most_ones(self):
        cum_sum = list()
        for target in range(self.n_vertices - 1, -1, -1):
            # Show that for any vertex there is at most one incoming edge
            cum_sum.append(f'{self.flow_cons[(target, ">=")]} 1 *')
            if len(cum_sum) > 1:
                cum_sum.append('+')
            vertices_in = [
                u
                for (u, v, _) in self.edges
                if v == target
            ]
            self.at_most_ones[target] = self.write_line('pol', *cum_sum)
            # Introduce d[v] := v has an incoming edge
            self.write_line(
                'red',
                f'-1 d[{target}]',
                *[
                    f'1 x[{v}][{target}]'
                    for v in vertices_in
                ],
                '>= 0',
                ';',
                f'd[{target}] -> 0'
            )
            self.write_line(
                'red',
                f'1 d[{target}]',
                *[
                    f'-1 x[{v}][{target}]'
                    for v in vertices_in
                ],
                '>= 0',
                ';',
                f'd[{target}] -> 1'
            )
            self.write_line(f'* Introduced variable d[{target}] = [{target} has an incoming edge]', is_constraint=False)


    def write_line(self, *line, is_constraint=True):
        with self.target_path.open('a') as f:
            f.write(' '.join(line) + '\n')
        if is_constraint:
            self.counter += 1
            return self.counter



def parse_instance(path):
    with path.open() as f:
        n_vertices = int(f.readline().strip())
        g = [dict() for _ in range(n_vertices)]
        for line in f:
            f, t, w = [int(x) for x in line.strip().split()]
            g[f][t] = w
    return g


def generate_formula(g, path):
    edges = [
        (source, target, weight)
        for source, out_edges in enumerate(g)    
        for target, weight in out_edges.items()
    ]
    flow_cons = dict()
    cnt = 1
    with path.open('w') as f:
        f.write(' '.join(['min:', *[f'{w} x[{u}][{v}]' for u, v, w in edges]]) + '\n')
        for ix in range(len(g)):
            bal = +1 if ix == 0 else -1 if ix == len(g) - 1 else 0
            in_edge_list = [
                e
                for e in edges
                if e[1] == ix
            ]
            out_edge_list = [
                e
                for e in edges
                if e[0] == ix
            ]
            f.write(
                ' '.join([
                    ' '.join(
                        f'-1 x[{u}][{v}]'
                        for u, v, _ in in_edge_list
                    ),
                    ' '.join(
                        f'1 x[{u}][{v}]'
                        for u, v, _ in out_edge_list
                    ),
                    f'>= {bal};'
                ]) + '\n'
            )
            flow_cons[(ix, '>=')] = cnt
            cnt += 1
            f.write(
                ' '.join([
                    ' '.join(
                        f'1 x[{u}][{v}]'
                        for u, v, _ in in_edge_list
                    ),
                    ' '.join(
                        f'-1 x[{u}][{v}]'
                        for u, v, _ in out_edge_list
                    ),
                    f'>= {-bal};'
                ]) + '\n'
            )
            flow_cons[(ix, '<=')] = cnt
            cnt += 1
    return edges, flow_cons


def prepare_dirs(formula_path, proof_path):
    formula_path.unlink(missing_ok=True)
    proof_path.unlink(missing_ok=True)


def main(instance_path):
    formula_path = instance_path.with_suffix('.opb')
    proof_path = instance_path.with_suffix('.veripb')
    prepare_dirs(formula_path, proof_path)
    g = parse_instance(instance_path)
    edges, flow_cons = generate_formula(g, formula_path)
    ProofManager(len(g), edges, flow_cons, proof_path).run()
    
    
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'instance_path', help='Instance path'
    )
    args = parser.parse_args()
    main(Path(args.instance_path))