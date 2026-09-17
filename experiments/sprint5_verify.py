#!/usr/bin/env python3
"""Run the bounded Sprint 5 certificates and compare committed JSON outputs."""

import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CASES = (
    ('sprint5_n7_escape_ascent_audit.py', 'sprint5_n7_escape_ascent_result.json'),
    ('sprint5_six_block_parity_audit.py', 'sprint5_six_block_parity_result.json'),
    ('sprint5_finite_field_parity_audit.py', 'sprint5_finite_field_parity_result.json'),
)


def main():
    for script, expected in CASES:
        result = subprocess.run([sys.executable, str(ROOT / script)],
                                capture_output=True, text=True, check=True,
                                timeout=120, cwd=ROOT)
        assert json.loads(result.stdout) == json.loads((ROOT / expected).read_text()), script
        print(f'PASS: {script}', flush=True)


if __name__ == '__main__':
    main()
