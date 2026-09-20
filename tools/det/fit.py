#!/usr/bin/env python3
"""WP1: fit the automation seconds against frame size and instruction count.

    automation_seconds = exp(a0) * (frame+1)^a1 * (instructions+1)^a2
                         * (frame+1)^(a3*log(frame+1))
                         * (instructions+1)^(a4*log(instructions+1))

fitted by weighted least squares on the logarithms, the weight being the
square root of the seconds, so the expensive proofs the plan cares about
drive the fit rather than the mass of cheap ones. `automation_seconds` is
the probe's wall time less what the same probe pays to compile the module
text before the automation starts, measured per lemma by the `prefix` probe.

The report also measures the ceiling of any such fit: the spread of seconds
inside one cell of the (frame band, instruction band) grid, and the share of
the variance in log seconds the two bands explain. A fit cannot predict
better than the scatter at fixed predictors allows.
"""

from __future__ import annotations

import argparse
import collections
import json
import math
import statistics
from pathlib import Path

TERMS = ["const", "log_frame", "log_instructions",
         "log_frame^2", "log_instructions^2"]
BUDGET = 600.0
INSTRUCTION_BANDS = [0, 2, 5, 10, 20]
FRAME_BANDS = [10, 30, 60, 100, 200]


def design(row: dict) -> list[float]:
    frame = math.log(row["frame"] + 1)
    instructions = math.log(row["instructions"] + 1)
    return [1.0, frame, instructions, frame ** 2, instructions ** 2]


def solve(matrix: list[list[float]], vector: list[float]) -> list[float]:
    size = len(vector)
    rows = [list(matrix[i]) + [vector[i]] for i in range(size)]
    for column in range(size):
        pivot = max(range(column, size), key=lambda r: abs(rows[r][column]))
        rows[column], rows[pivot] = rows[pivot], rows[column]
        if abs(rows[column][column]) < 1e-12:
            rows[column][column] = 1e-12
        for other in range(size):
            if other == column:
                continue
            factor = rows[other][column] / rows[column][column]
            for index in range(column, size + 1):
                rows[other][index] -= factor * rows[column][index]
    return [rows[i][size] / rows[i][i] for i in range(size)]


def least_squares(rows: list[dict]) -> list[float]:
    columns = len(TERMS)
    normal = [[0.0] * columns for _ in range(columns)]
    right = [0.0] * columns
    for row in rows:
        x = design(row)
        y = math.log(max(row["automation_seconds"], 0.05))
        weight = math.sqrt(max(row["automation_seconds"], 0.05))
        for i in range(columns):
            right[i] += weight * x[i] * y
            for j in range(columns):
                normal[i][j] += weight * x[i] * x[j]
    return solve(normal, right)


def predict(coefficients: list[float], row: dict) -> float:
    return math.exp(sum(c * v for c, v in zip(coefficients, design(row))))


def within(row: dict, prediction: float, budget: float) -> bool:
    if not row["reached_end"]:
        return prediction >= budget / 2
    ratio = prediction / max(row["automation_seconds"], 0.05)
    return 0.5 <= ratio <= 2.0


def score(rows: list[dict], coefficients: list[float],
          budget: float) -> tuple[int, float]:
    hits = 0
    for row in rows:
        row["predicted"] = round(predict(coefficients, row), 2)
        row["within"] = within(row, row["predicted"], budget)
        hits += row["within"]
    return hits, 100 * hits / max(1, len(rows))


def band(value: int, edges: list[int]) -> int:
    for edge in edges:
        if value <= edge:
            return edge
    return edges[-1] + 1


def ceiling(rows: list[dict]) -> dict:
    """How well any fit of the two variables could possibly do."""
    cells = collections.defaultdict(list)
    for row in rows:
        cells[(band(row["instructions"], INSTRUCTION_BANDS),
               band(row["frame"], FRAME_BANDS))].append(
                   row["automation_seconds"])
    spreads = []
    for values in cells.values():
        if len(values) < 10:
            continue
        ordered = sorted(values)
        spreads.append(ordered[9 * len(ordered) // 10]
                       / max(ordered[len(ordered) // 10], 0.05))
    logs = [math.log(max(r["automation_seconds"], 0.05)) for r in rows]
    mean = sum(logs) / len(logs)
    total = sum((value - mean) ** 2 for value in logs)
    groups = collections.defaultdict(list)
    for row, value in zip(rows, logs):
        groups[(band(row["instructions"], INSTRUCTION_BANDS),
                band(row["frame"], FRAME_BANDS))].append(value)
    inside = sum(sum((value - sum(group) / len(group)) ** 2
                     for value in group) for group in groups.values())
    return {"cells": len(cells),
            "median_spread": round(statistics.median(spreads), 2)
            if spreads else 0.0,
            "variance_explained": round(100 * (1 - inside / total), 1)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--joined", type=Path, required=True)
    parser.add_argument("--test-set", type=Path, required=True)
    parser.add_argument("--budget", type=float, default=BUDGET)
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    rows = [json.loads(line) for line in
            arguments.joined.read_text().split("\n") if line.strip()]
    wanted = {tuple(line.split(":", 1)) for line in
              arguments.test_set.read_text().split("\n") if ":" in line}
    test = [r for r in rows if (r["module"], r["lemma"]) in wanted]
    population = [r for r in rows if r["reached_end"] and r["prefix_seconds"]]
    held_out = [r for r in population if (r["module"], r["lemma"]) not in wanted]

    result = {"terms": TERMS, "budget": arguments.budget}
    for name, train in (("whole population", population),
                        ("test lemmas held out", held_out)):
        coefficients = least_squares(train)
        _, population_share = score(population, coefficients, arguments.budget)
        _, test_share = score(test, coefficients, arguments.budget)
        finished = [r for r in test if r["reached_end"]]
        _, finished_share = score(finished, coefficients, arguments.budget)
        print(f"fit on {len(train)} lemmas ({name}):")
        print("  " + "   ".join(f"{term} {value:+.3f}"
                                for term, value in zip(TERMS, coefficients)))
        print(f"  within a factor of two: population {population_share:.1f}%, "
              f"the 244 expensive probes {test_share:.1f}% "
              f"({finished_share:.1f}% of the {len(finished)} that finished)")
        result[name] = {"coefficients": coefficients, "train": len(train),
                        "population_share": population_share,
                        "test_share": test_share,
                        "test_finished_share": finished_share}
    limit = ceiling(population)
    print(f"ceiling: inside one (frame band, instruction band) cell the "
          f"seconds spread p90/p10 by a median factor of "
          f"{limit['median_spread']}; the two bands explain "
          f"{limit['variance_explained']}% of the variance in log seconds")
    result["ceiling"] = limit
    result["test_rows"] = test
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text(json.dumps(result, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
