#!/usr/bin/env bash
NUM_SAMPLES=$1
python dag/generate.py --prefix "pos" --output-dir samples/dag --num-samples $NUM_SAMPLES --seed 0 --min-size 50 --max-size 1000 --min-weight 1 --max-weight 75 --edge-probability-pct 15
python dag/generate.py --prefix "mixed" --output-dir samples/dag --num-samples $NUM_SAMPLES --seed 0 --min-size 50 --max-size 1000 --min-weight -75 --max-weight 75 --edge-probability-pct 15
