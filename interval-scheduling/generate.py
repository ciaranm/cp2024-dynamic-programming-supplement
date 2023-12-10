import argparse
from math import ceil
from pathlib import Path
import random


def sample(n_ints, args, out_file):
    max_time = random.randint(args.min_time, args.max_time)
    out_file.write(f'{n_ints}\n')
    for _ in range(n_ints):
        int_time = min(max_time, int(ceil(random.expovariate(1.0 / args.avg_time))))
        start = random.randint(0, max_time - int_time)
        finish = start + int_time
        weight = random.randint(args.min_weight, args.max_weight)
        out_file.write(f'{start} {finish} {weight}\n')


def main(args):
    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    max_len = len(str(args.num_samples))
    for ix in range(1, args.num_samples + 1):
        n_ints = args.min_size + int((ix - 1) * (args.max_size - args.min_size) / (args.num_samples - 1))
        file_name = f'{args.prefix}_{ix:0{max_len}}_{n_ints}.{args.extension}'
        out_path = out_dir / file_name
        with out_path.open('w') as out_file:
            sample(n_ints, args, out_file)


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
        help="Minimum number of intervals",
    )
    parser.add_argument(
        "--max-size",
        type=int,
        required=False,
        default=16,
        help="Maximum number of intervals",
    )
    parser.add_argument(
        "--min-time",
        type=int,
        required=False,
        default=10,
        help="Minimum total duration",
    )
    parser.add_argument(
        "--max-time",
        type=int,
        required=False,
        default=20,
        help="Maximum total duration",
    )
    parser.add_argument(
        "--min-weight",
        type=int,
        required=False,
        default=1,
        help="Minimum interval weight",
    )
    parser.add_argument(
        "--max-weight",
        type=int,
        required=False,
        default=10,
        help="Maximum edge weight",
    )
    parser.add_argument(
        "--avg-time",
        type=float,
        required=False,
        default=3,
        help="Average length of an interval",
    )
    args = parser.parse_args()
    if args.seed is not None:
        random.seed(args.seed)
    main(args)
