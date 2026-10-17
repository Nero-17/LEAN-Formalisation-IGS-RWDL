"""New, independently recorded critical DHL population-dynamics experiment.

This does not recover the historical simulation's code or seed. It approximates
the distributional series/diamond resistance recursion using an empirical
population, with replacement at every generation. Finite-population bias and
finite-generation error are not bounded by this experiment.

Example:
  python population_dynamics.py --output population_dynamics_results.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def run_seed(seed: int, size: int, generations: int) -> dict:
    started_utc = utc_now()
    started = time.perf_counter()
    rng = np.random.Generator(np.random.PCG64(seed))
    p = (math.sqrt(5.0) - 1.0) / 2.0
    diamond_probability = p**4 / (2.0 * p**2 - p**4)
    population = np.ones(size, dtype=np.float64)
    cumulative_log_scale = 0.0
    checkpoints = []
    checkpoint_levels = {1, 10, 100, 1000, 2500, 5000, 7500, generations}
    for generation in range(1, generations + 1):
        # Four independent empirical child samples for every new parent.
        # Sampling unused third/fourth children in the series case fixes a
        # simple, explicit random-number consumption convention.
        child_indices = rng.integers(0, size, size=(4, size), dtype=np.int64)
        first_sum = population[child_indices[0]] + population[child_indices[1]]
        second_sum = population[child_indices[2]] + population[child_indices[3]]
        diamond = rng.random(size) < diamond_probability
        parent = first_sum.copy()
        parent[diamond] = (
            first_sum[diamond] * second_sum[diamond]
            / (first_sum[diamond] + second_sum[diamond])
        )
        empirical_mean = float(np.mean(parent, dtype=np.float64))
        cumulative_log_scale += math.log(empirical_mean)
        population = parent / empirical_mean
        if generation in checkpoint_levels:
            if not np.all(np.isfinite(population)) or np.min(population) <= 0:
                raise ArithmeticError("Population must remain positive and finite")
            mean_log_normalized = float(np.mean(np.log(population)))
            normalized_mean = float(np.mean(population))
            log_mean_rate = (
                cumulative_log_scale + math.log(normalized_mean)
            ) / generation
            mean_log_rate = (
                cumulative_log_scale + mean_log_normalized
            ) / generation
            checkpoint = {
                "generation": generation,
                "empirical_log_mean_resistance_over_n": log_mean_rate,
                "empirical_mean_log_resistance_over_n": mean_log_rate,
                "empirical_jensen_gap_over_n": log_mean_rate - mean_log_rate,
                "cumulative_log_scale": cumulative_log_scale,
                "normalized_population_mean": normalized_mean,
                "normalized_population_min": float(np.min(population)),
                "normalized_population_max": float(np.max(population)),
                "normalized_population_cv": float(np.std(population)),
                "elapsed_seconds": time.perf_counter() - started,
            }
            checkpoints.append(checkpoint)
            print(json.dumps({"seed": seed, **checkpoint}), flush=True)
    return {
        "seed": seed,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "elapsed_seconds": time.perf_counter() - started,
        "checkpoints": checkpoints,
        "final": checkpoints[-1],
    }


def describe(values: list[float]) -> dict:
    return {
        "values": values,
        "mean": float(np.mean(values)),
        "minimum": min(values),
        "maximum": max(values),
        "range": max(values) - min(values),
        "sample_standard_deviation": (
            float(np.std(values, ddof=1)) if len(values) > 1 else None
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--population", type=int, default=32768)
    parser.add_argument("--generations", type=int, default=10000)
    parser.add_argument("--seeds", type=int, nargs="+",
                        default=[20261017, 20261018, 20261019, 20261020])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.population < 1 or args.generations < 1:
        parser.error("population and generations must be positive")
    p = (math.sqrt(5.0) - 1.0) / 2.0
    result = {
        "experiment": "new independent critical DHL population dynamics",
        "historical_run_recovered": False,
        "started_utc": utc_now(),
        "command_arguments": vars(args) | {"output": str(args.output)},
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python_version": sys.version,
        "numpy_version": np.__version__,
        "platform": platform.platform(),
        "rng": "numpy Generator(PCG64(seed))",
        "floating_point": "numpy float64",
        "critical_parameter": p,
        "diamond_probability": p**4 / (2.0 * p**2 - p**4),
        "series_probability": 1.0 - p**4 / (2.0 * p**2 - p**4),
        "population_size": args.population,
        "generations": args.generations,
        "seeds": args.seeds,
        "method": (
            "Initial population R_0=1. At every generation independently sample "
            "four children with replacement from the preceding normalized "
            "population. With probability q=p^4/(2p^2-p^4), return "
            "(R1+R2)(R3+R4)/(R1+R2+R3+R4); otherwise return R1+R2. "
            "Divide the population by its empirical arithmetic mean and add "
            "the log of that mean to cumulative_log_scale. Homogeneity makes "
            "this stable normalization equivalent to common log-domain scaling."
        ),
        "limitations": (
            "Empirical population approximations, not exact expectations. "
            "Seed spread is descriptive only; it is not a rigorous confidence "
            "interval and does not bound finite-population or generation bias. "
            "The empirical Jensen gap is not an error bound for the exponent."
        ),
        "runs": [],
    }
    for seed in args.seeds:
        result["runs"].append(run_seed(seed, args.population, args.generations))
        result["last_saved_utc"] = utc_now()
        if len(result["runs"]) == len(args.seeds):
            result["ended_utc"] = utc_now()
        result["descriptive_summary"] = {
            key: describe([r["final"][key] for r in result["runs"]])
            for key in ["empirical_log_mean_resistance_over_n",
                        "empirical_mean_log_resistance_over_n",
                        "empirical_jensen_gap_over_n"]
        }
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print("Saved " + str(args.output), flush=True)


if __name__ == "__main__":
    main()
