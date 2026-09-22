#!/usr/bin/env python3
"""Sanity-check test data only. This does NOT compile, run, or verify Lean."""
from pathlib import Path
import json
from reference_model import START, parse, checked, legal, usi, perft

root = Path(__file__).resolve().parent
cases = json.loads((root / 'cases.json').read_text())['cases']
for case in cases:
    p = parse(case['sfen'])
    assert not checked(p, 1-p.turn), case['name']
    actual = [usi(m) for m in legal(p)]
    assert sorted(actual) == case['expected_sorted'], case['name']
    assert len(actual) == len(set(actual)), case['name']
    assert set(case['present']) <= set(actual), case['name']
    assert not set(case['absent']) & set(actual), case['name']
    if case['count'] is not None:
        assert len(actual) == case['count'], case['name']
    if case['no_drops']:
        assert not any('*' in move for move in actual), case['name']
assert perft(parse(START), 1) == 30
assert perft(parse(START), 2) == 900
print(f'Python test-data sanity check: {len(cases)} fixtures PASS; perft(1)=30, perft(2)=900')
print('This result is NOT a Lean compilation or execution result.')
