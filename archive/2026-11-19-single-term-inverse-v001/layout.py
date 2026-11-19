"""Locations of the earlier certificates and of regenerated outputs."""
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TRANSPORT = ROOT / "archive" / "2026-11-19-zero-transport-v001"
PREVIOUS = ROOT / "archive" / "2026-11-19-sixth-passes-v001" / "compute"
OUTPUT = Path(os.environ.get("SINGLE_TERM_OUTPUT", HERE)).resolve()
