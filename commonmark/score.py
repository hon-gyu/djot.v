# ai-disclosure: autonomous
"""Run CommonMark 0.31.2 examples through Rocq vm_compute, not extraction."""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import sys
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
# The spec is CC-BY-SA 4.0, so it is fetched rather than committed.
SPEC_URL = "https://spec.commonmark.org/0.31.2/spec.json"
SPEC = ROOT / "_build" / "commonmark" / "spec-0.31.2.json"
RESULT = re.compile(r"^\s*= (true|false)\s*$", re.MULTILINE)


def rocq_string(value):
    return '"' + value.replace('"', '""') + '"'


def source_for(cases, profile):
    header = (
        "From Stdlib Require Import String.\n"
        "From DjotV Require Import Profile.\n"
        "Open Scope string_scope.\n"
    )
    return header + "".join(
        "Eval vm_compute in (String.eqb (convert_profile "
        + profile + " " + rocq_string(case["markdown"]) + ") "
        + rocq_string(case["html"]) + ").\n"
        for case in cases
    )


def run_chunk(cases, profile, timeout):
    with tempfile.TemporaryDirectory(prefix="djot-commonmark-") as temp:
        path = Path(temp) / "cases.v"
        path.write_text(source_for(cases, profile))
        command = ["rocq", "repl",
                   "-q", "-batch", "-R", "_build/default/theories", "DjotV",
                   "-l", str(path)]
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True,
                                   start_new_session=True)
        try:
            try:
                stdout, stderr = process.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                return None, "timeout"
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
    values = RESULT.findall(stdout)
    if process.returncode == 0 and len(values) == len(cases):
        return [value == "true" for value in values], None
    error = stderr.strip() or stdout[-250:].strip()
    return None, error or f"exit {process.returncode}"


def score(cases, profile, timeout):
    values, error = run_chunk(cases, profile, timeout)
    if values is not None:
        return [(case, value, None) for case, value in zip(cases, values)]
    if len(cases) == 1:
        return [(cases[0], False, error)]
    half = len(cases) // 2
    return score(cases[:half], profile, timeout) + score(cases[half:], profile, timeout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", default="commonmark_test_profile",
                        choices=["djot_profile", "markdown_like_profile",
                                 "commonmark_test_profile"])
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--timeout", type=int, default=20)
    parser.add_argument("--show-failures", type=int, default=0)
    args = parser.parse_args()
    if args.chunk_size < 1 or args.timeout < 1:
        parser.error("chunk size and timeout must be positive")
    if not SPEC.exists():
        SPEC.parent.mkdir(parents=True, exist_ok=True)
        urllib.request.urlretrieve(SPEC_URL, SPEC)
    cases = json.loads(SPEC.read_text())
    results = []
    # Examples 265-266 have 9- and 10-digit list starts.  Evaluate them
    # separately: their unary nats exceed the normal batch budget and must
    # not hide the status of neighbouring examples.
    for part in (cases[:264], cases[264:265], cases[265:266], cases[266:]):
        for offset in range(0, len(part), args.chunk_size):
            chunk = part[offset:offset + args.chunk_size]
            budget = min(args.timeout, 5) if chunk[0]["example"] in (265, 266) else args.timeout
            results += score(chunk, args.profile, budget)
            if len(results) % 64 < len(chunk):
                print(f"scored {len(results)}/{len(cases)}", file=sys.stderr,
                      flush=True)
    totals = Counter(case["section"] for case, _, _ in results)
    passed = Counter(case["section"] for case, ok, _ in results if ok)
    failures = [(case, error) for case, ok, error in results if not ok]
    errors = [(case, error) for case, _, error in results if error]
    print(f"profile: {args.profile}")
    print(f"exact HTML: {len(cases) - len(failures)}/{len(cases)}")
    print(f"Rocq execution failures: {len(errors)}")
    for section, total in totals.items():
        print(f"  {section}: {passed[section]}/{total}")
    for case, error in errors:
        print(f"  execution failure #{case['example']}: {error}")
    for case, error in failures[:args.show_failures]:
        print(f"  failure #{case['example']} ({case['section']}): "
              f"{error or 'different HTML'}")


if __name__ == "__main__":
    main()
