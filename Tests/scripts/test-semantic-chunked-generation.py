#!/usr/bin/env python3
"""Check with the native case tool that a campaign's generation in several
requests equals one request.

For every pure profile, at the suite's random node budget and the campaign's
random defaults, one request for three whole functions is compared byte for
byte with the campaign's merged result of one-function requests, two-function
requests and requests that overflow until they hold one function. Seeds start
at one and two below 2^64, so later requests continue across the wrap. An
attempt budget of two exhausts generation in both forms. This test neither
compiles Rust nor executes an EVM.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("chunked_generation_suite", ROOT / "scripts/semantic-suite.py")
suite = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suite)
campaign = suite.pure_campaign
FUNCTIONS = 3
ATTEMPTS = 256


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def options(profile: str) -> list[str]:
    result = [campaign.RANDOM_G0_VERSION] if profile in campaign.G0_PROFILES else []
    if profile in campaign.RUNTIME_INPUT_PROFILES:
        result.append(campaign.RANDOM_INPUT_SELECTION)
    if profile in campaign.IDENTITY_FILTER_PROFILES:
        result.append(campaign.RANDOM_ACCEPTANCE)
    return result


def requester(tool: Path, profile: str, fuel: int, calls: list, overflow_functions: int | None = None):
    command = campaign.PROFILE_COMMANDS[profile][0]
    nodes = str(suite.PROFILES[profile][2])
    per_function = per(profile)

    def request(first_seed: int, cases: int, attempts: int) -> dict:
        require(0 <= first_seed < campaign.SEED_MODULUS, "a request seed left the uint64 range")
        calls.append((first_seed, cases, attempts))
        if overflow_functions is not None and -(-cases // per_function) > overflow_functions:
            raise campaign.m2.Finding(campaign.RESOURCE, "generation", "output-limit")
        result = subprocess.run([str(tool), command, str(first_seed), nodes, str(cases), str(attempts), str(fuel),
                                 *options(profile)], cwd=ROOT, capture_output=True, text=True, timeout=300, check=False)
        require(result.returncode == 0, f"{profile}: native generation failed: {result.stdout[:300]}")
        return json.loads(result.stdout)
    return request


def per(profile: str) -> int:
    if profile == "closed-g0":
        return 1
    return campaign.inputs_per_function(profile, campaign.RANDOM_INPUT_SELECTION)


def canonical(value) -> str:
    return json.dumps(value, sort_keys=True)


def check(tool: Path, profile: str, seed: int, attempts: int, fuel: int) -> dict:
    count = FUNCTIONS * per(profile)
    single = requester(tool, profile, fuel, [])(seed, count, attempts)
    seen = {}
    for label, functions, overflow in (("one", 1, None), ("two", 2, None), ("overflow", None, 1)):
        calls = []
        merged, stats = campaign.generate_in_requests(requester(tool, profile, fuel, calls, overflow),
                                                      count, attempts, seed, per(profile), functions)
        require(canonical(merged) == canonical(single), f"{profile}: {label}-function requests differ from one request")
        require(all(cases % per(profile) == 0 for _, cases, _ in calls[:-1]), f"{profile}: a request cut a function")
        seen[label] = {"requests": stats["requests"], "retries": stats["outputLimitRetries"], "seeds": [s for s, _, _ in calls]}
    return {"single": single, "schedules": seen}


def validate(tool: Path, fuel: int) -> dict:
    report = {}
    wrap = campaign.SEED_MODULUS - 2
    for profile in campaign.PROFILES:
        result = check(tool, profile, 1, ATTEMPTS, fuel)
        require(result["single"]["status"] == "complete", f"{profile}: three functions did not fit in {ATTEMPTS} attempts")
        require(result["schedules"]["one"]["requests"] == FUNCTIONS, f"{profile}: one-function requests did not take three requests")
        require(result["schedules"]["overflow"]["retries"] == 1, f"{profile}: the overflow schedule did not halve once")
        wrapped = check(tool, profile, wrap, ATTEMPTS, fuel)
        seeds = [int(entry["provenance"]["origin"]["seed"]) for entry in wrapped["single"]["cases"]
                 if isinstance(entry.get("provenance", {}).get("origin"), dict) and "seed" in entry["provenance"]["origin"]]
        require(any(seed < wrap for seed in seeds) or wrapped["single"]["attempted"] <= 2,
                f"{profile}: generation from 2^64 - 2 did not wrap")
        require(any(first < wrap for first in wrapped["schedules"]["one"]["seeds"][1:]),
                f"{profile}: no later request started after the wrap")
        exhausted = check(tool, profile, 1, 2, fuel)
        require(exhausted["single"]["status"] == "generation-exhausted" and exhausted["single"]["attempted"] == 2,
                f"{profile}: two attempts did not exhaust three functions")
        report[profile] = {"cases": len(result["single"]["cases"]), "attempted": result["single"]["attempted"],
                           "excluded": len(result["single"]["excluded"]),
                           "wrapAttempted": wrapped["single"]["attempted"],
                           "exhaustedCases": len(exhausted["single"]["cases"])}
    return {"status": "passed", "profiles": len(report), "functions": FUNCTIONS, "results": report}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
