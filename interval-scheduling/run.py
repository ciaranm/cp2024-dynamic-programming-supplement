import argparse
from functools import cache
from pathlib import Path
import sys


class ProofManager:
    def __init__(self, instance, pairs, target_path):
        self.target_path = target_path
        self.instance = instance
        self.pairs = pairs
        self.counter = max(pairs.values())
        self.write_line('pseudo-Boolean proof version 1.2', is_constraint=False)
        self.write_line(f'f {self.counter} 0', is_constraint=False)


    def run(self):
        self.big_m = 20 * sum(w for _, _, w in self.instance)
        self.intervals_sorted = [(ix, *i) for ix, i in enumerate(self.instance)]
        self.intervals_sorted.sort(key=lambda x: x[2]) # sort by finish time
        score, items, bound = self.generate_proof(len(self.intervals_sorted) - 1)
        self.write_line('output NONE', is_constraint=False)
        self.write_line(f'conclusion BOUNDS {-score} : {bound} {-score} : ' +
                        ' '.join(f'x[{ix}]' if ix in items else f'~x[{ix}]' for ix in range(len(self.instance))), is_constraint=False)
        self.write_line('end pseudo-Boolean proof', is_constraint=False)


    def next_available(self, ix):
        _, last_start, _, _ = self.intervals_sorted[ix]
        last_avail_index = ix - 1
        while last_avail_index >= 0:
            _, _, candidate_finish, _ = self.intervals_sorted[last_avail_index]
            if candidate_finish <= last_start:
                break
            else:
                last_avail_index -= 1
        return last_avail_index


    @cache
    def generate_proof(self, prefix):
        if prefix < 0:
            return 0, list(), None
        last_avail_index = self.next_available(prefix)
        self.write_line(f'* Splitting prefix {prefix} into subproblems for prefixes {prefix - 1} and {last_avail_index}', is_constraint=False)
        score_no_take, items_no_take, _ = self.generate_proof(prefix - 1)
        score_take, items_take, _ = self.generate_proof(last_avail_index)
        return self.declare_merge(
            prefix, score_take, score_no_take, items_take, items_no_take
        )


    def declare_merge(self, prefix, score_take, score_no_take, items_take, items_no_take):
        last_index, _, _, last_weight = self.intervals_sorted[prefix]
        take_opt = score_take + last_weight >= score_no_take
        score = score_take + last_weight if take_opt else score_no_take
        items = items_take + [last_index] if take_opt else items_no_take
        self.write_line(*[
            f'red',
            *[f'{-w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix]],
            f'{self.big_m} x[{last_index}]',
            f'>= {-score_no_take} ;',
            f'x[{last_index}] -> 0'
        ])
        self.write_line(*[
            f'red',
            *[f'{-w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix]],
            f'{self.big_m} ~x[{last_index}]',
            f'>= {-score_take} ;',
            f'x[{last_index}] -> 1'
        ])
        full_bound_no_take = self.write_line(*[
            f'red',
            *[f'{-w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix+1]],
            f'{self.big_m} x[{last_index}]',
            f'>= {-score} ;',
            f'x[{last_index}] -> 0'
        ])
        full_bound_take = self.write_line(*[
            f'red',
            *[f'{-w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix+1]],
            f'{self.big_m} ~x[{last_index}]',
            f'>= {-score} ;',
            f'x[{last_index}] -> 1'
        ])
        lhs_neg = self.write_line(*[
            f'red',
            *[f'{-w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix+1]],
            f'{self.big_m} ~z[{last_index}]',
            f'>= {-score} ;',
            f'z[{last_index}] -> 0'
        ])
        lhs_pos = self.write_line(*[
            f'red',
            *[f'{w} x[{ix}]' for ix, _, _, w in self.intervals_sorted[:prefix+1]],
            f'{self.big_m} z[{last_index}]',
            f'>= {1 + score} ;',
            f'z[{last_index}] -> 1'
        ])
        self.write_line('pol', f'{lhs_pos} 1 *', f'{full_bound_no_take} 1 *', '+')
        self.write_line('pol', f'{lhs_pos} 1 *', f'{full_bound_take} 1 *', '+')
        aux_bd = self.write_line('rup', f'1 z[{last_index}] >= 1 ;')
        full_bound = self.write_line('pol', f'{aux_bd} {self.big_m} *', f'{lhs_neg} 1 *', '+')
        self.write_line(f'* Justified the bound for prefix {prefix}', is_constraint=False)
        return score, items, full_bound


    def write_line(self, *line, is_constraint=True):
        with self.target_path.open('a') as f:
            f.write(' '.join(line) + '\n')
        if is_constraint:
            self.counter += 1
            return self.counter



def parse_instance(path):
    with path.open() as f:
        n_intervals = int(f.readline().strip())
        res = [[int(x) for x in line.strip().split()] for line in f]
        assert len(res) == n_intervals
        return res


def generate_formula(intervals, path):
    pairs = dict()
    cnt = 1
    with path.open('w') as f:
        f.write('min: ' + ' '.join(f'{-w} x[{ix}]' for ix, (_, _, w) in enumerate(intervals)) + '\n')
        for ix, (s1, f1, _) in enumerate(intervals):
            for jx, (s2, f2, _) in enumerate(intervals[ix:], ix):
                if max(s1, s2) < min(f1, f2):
                    pairs[(ix, jx)] = cnt
                    pairs[(jx, ix)] = cnt
                    cnt += 1
                    if ix < jx:
                        f.write(f'-1 x[{ix}] -1 x[{jx}] >= -1 ;\n')
                    else:
                        f.write(f'-1 x[{ix}] >= -1 ;\n')
    return pairs


def prepare_dirs(formula_path, proof_path):
    formula_path.unlink(missing_ok=True)
    proof_path.unlink(missing_ok=True)


def main(instance_path):
    formula_path = instance_path.with_suffix('.opb')
    proof_path = instance_path.with_suffix('.veripb')
    prepare_dirs(formula_path, proof_path)
    intervals = parse_instance(instance_path)
    pairs = generate_formula(intervals, formula_path)
    ProofManager(intervals, pairs, proof_path).run()
    
    
if __name__ == '__main__':
    sys.setrecursionlimit(10_000)
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'instance_path', help='Instance path'
    )
    args = parser.parse_args()
    main(Path(args.instance_path))