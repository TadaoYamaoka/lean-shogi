#!/usr/bin/env python3
"""Compare the actual Lean binary against cshogi, including all legal moves.

Optional test dependency only: python -m pip install cshogi
Run from the project root after `lake build`:
    python tests/compare_cshogi.py --positions 1000 --seed 20260922

This script has NOT been run against a Lean binary in the authoring environment.
"""
from __future__ import annotations

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import random
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--positions', type=int, default=1000,
                        help='number of extra random-play positions; 0 = fixtures only')
    parser.add_argument('--seed', type=int, default=20260922)
    parser.add_argument('--timeout', type=float, default=300.0)
    args = parser.parse_args()
    if args.positions < 0 or args.timeout <= 0:
        parser.error('positions must be nonnegative and timeout must be positive')
    try:
        import cshogi
    except ImportError:
        print('Missing test dependency: python -m pip install cshogi', file=sys.stderr)
        return 2

    root = Path(__file__).resolve().parents[1]
    binary = args.binary or root / '.lake' / 'build' / 'bin' / ('shogi.exe' if os.name == 'nt' else 'shogi')
    binary = binary.resolve()
    if not binary.is_file():
        print(f'Lean executable not found: {binary}. Run lake build first.', file=sys.stderr)
        return 2

    corpus = json.loads((root / 'tests' / 'cases.json').read_text(encoding='utf-8'))
    records: list[tuple[str, str, set[str]]] = []
    for case in corpus['cases']:
        board = cshogi.Board(case['sfen'])
        expected = {cshogi.move_to_usi(m) for m in board.legal_moves}
        # Also check that the regression snapshots agree with the external library.
        saved = set(case['expected_sorted'])
        if expected != saved:
            print(f'Regression snapshot disagrees with cshogi: {case["name"]}', file=sys.stderr)
            print(f'SFEN: {case["sfen"]}', file=sys.stderr)
            print(f'Only in cshogi: {sorted(expected - saved)}', file=sys.stderr)
            print(f'Only in snapshot: {sorted(saved - expected)}', file=sys.stderr)
            return 1
        records.append((case['name'], case['sfen'], expected))

    rng = random.Random(args.seed)
    board = cshogi.Board()
    plies = 0
    for i in range(args.positions):
        candidates = list(board.legal_moves)
        records.append((f'random_{i}', board.sfen(), {cshogi.move_to_usi(m) for m in candidates}))
        if not candidates or plies >= 400:
            board.reset()
            plies = 0
        else:
            board.push(rng.choice(candidates))
            plies += 1

    try:
        process = subprocess.run(
            [str(binary), '--batch'],
            input=''.join(sfen + '\n' for _, sfen, _ in records),
            text=True, encoding='utf-8', capture_output=True, timeout=args.timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        print(f'Could not complete Lean comparison: {exc}', file=sys.stderr)
        return 2
    if process.returncode != 0:
        print(f'Lean exited with {process.returncode}: {process.stderr}', file=sys.stderr)
        print(process.stdout[:4000], file=sys.stderr)
        return 1
    lines = process.stdout.splitlines()
    if len(lines) != len(records):
        print(f'Expected {len(records)} response lines, got {len(lines)}', file=sys.stderr)
        return 1
    for (name, sfen, expected), line in zip(records, lines):
        tokens = line.split()
        actual = set(tokens)
        if actual != expected or len(tokens) != len(actual):
            print(f'MISMATCH: {name}\nSFEN: {sfen}', file=sys.stderr)
            print(f'Missing: {sorted(expected - actual)}', file=sys.stderr)
            print(f'Extra: {sorted(actual - expected)}', file=sys.stderr)
            print(f'Duplicates: {len(tokens) - len(actual)}', file=sys.stderr)
            return 1
    print(f'PASS: {len(records)} positions; cshogi={version("cshogi")}; seed={args.seed}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
