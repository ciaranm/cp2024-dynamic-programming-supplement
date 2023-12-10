#!/usr/bin/env bash
NUM_SAMPLES=$1
python interval-scheduling/generate.py --prefix "schedule" --output-dir samples/interval-scheduling --num-samples $NUM_SAMPLES --seed 0 --min-size 20 --max-size 600 --min-time 1000 --max-time 2000 --min-weight 1 --max-weight 100 --avg-time 200