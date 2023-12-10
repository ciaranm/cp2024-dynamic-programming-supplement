import argparse
from pathlib import Path
import random


def percentage(x):
    x = int(x)
    if x < 0:
        raise argparse.ArgumentTypeError("Cannot have negative percentage")
    if x > 100:
        raise argparse.ArgumentTypeError("Cannot have > 100%")
    return x


def sample(n_edges, args, out_file):
    edge_proba = 0.01 * args.edge_probability_pct
    n_vertices = int((2 * n_edges / edge_proba) ** 0.5)
    out_file.write(f'{n_vertices}\n')
    edges = random.sample([(from_ix, to_ix)
                           for from_ix in range(n_vertices)
                           for to_ix in range(from_ix + 1, n_vertices)], n_edges)
    for from_ix, to_ix in edges:
        weight = random.randint(args.min_weight, args.max_weight)
        out_file.write(f'{from_ix} {to_ix} {weight}\n')


def main(args):
    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    max_len = len(str(args.num_samples))
    for ix in range(1, args.num_samples + 1):
        n_edges = args.min_size + int((ix - 1) * (args.max_size - args.min_size) / (args.num_samples - 1))
        file_name = f'{args.prefix}_{ix:0{max_len}}_{n_edges}.{args.extension}'
        out_path = out_dir / file_name
        with out_path.open('w') as out_file:
            sample(n_edges, args, out_file)
            


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Sample DAG shortest path problems"
    )
    parser.add_argument(
        "--output-dir",
        "-o",
        required=True,
        help="Output directory for instance files",
    )
    parser.add_argument(
        "--prefix",
        "-p",
        required=True,
        help="Filename prefix",
    )
    parser.add_argument(
        "--extension",
        required=False,
        default='txt',
        help="Filename extension",
    )
    parser.add_argument(
        "--num-samples",
        "-n",
        required=True,
        type=int,
        help="Number of samples",
    )
    parser.add_argument(
        "--seed",
        "-s",
        required=False,
        type=int,
        help="Random seed",
    )
    parser.add_argument(
        "--min-size",
        type=int,
        required=False,
        default=8,
        help="Minimum number of vertices in the graph",
    )
    parser.add_argument(
        "--max-size",
        type=int,
        required=False,
        default=16,
        help="Maximum number of vertices in the graph",
    )
    parser.add_argument(
        "--min-weight",
        type=int,
        required=False,
        default=1,
        help="Minimum edge weight",
    )
    parser.add_argument(
        "--max-weight",
        type=int,
        required=False,
        default=10,
        help="Maximum edge weight",
    )
    parser.add_argument(
        "--edge-probability-pct",
        type=percentage,
        required=False,
        default=50,
        help="Probability of choosing an edge, percents (>= 0, <= 100)",
    )
    args = parser.parse_args()
    if args.seed is not None:
        random.seed(args.seed)
    main(args)
