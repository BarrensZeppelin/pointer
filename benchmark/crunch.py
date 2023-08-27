#!/usr/bin/env python3

import json

with open("data.jsonl") as f:
    data = [*map(json.loads, f)]

N = len(data)

print(f"Benchmark results for {N} modules", end="\n\n")

for analysis in ("steensgaard", "andersen"):
    time = 0.
    edges = reachable = 0
    for d in (d[analysis] for d in data):
        time += (d["analysisDuration"] + d.get("callGraphDuration", 0.)) / 1000
        edges += d["callGraphEdges"]
        reachable += d["reachable"]

    print(f"""{analysis.title()} stats:
    Average analysis time:            {time / N:.2f}s
    Average # of non-static edges:    {edges / N:.2f}
    Average # of reachable functions: {reachable / N:.2f}
""")
