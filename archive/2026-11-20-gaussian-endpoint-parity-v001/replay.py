"""Replay the four endpoint calculations and check their published conclusions."""
import json
from pathlib import Path
import subprocess
import sys

from flint import arb, ctx


HERE = Path(__file__).resolve().parent
RECORDS = (
    ("check_gaussian_base_endpoints.py", "gaussian-base-endpoints.json"),
    ("check_gaussian_hardy_endpoints.py", "gaussian-hardy-endpoints-balls.json"),
    ("check_endpoint_transfer.py", "endpoint-transfer.json"),
    ("check_endpoint_refinement.py", "endpoint-refinement.json"),
)


def compare(saved, fresh, path):
    if isinstance(saved, dict) and isinstance(fresh, dict) and saved.keys() == fresh.keys():
        for key in saved:
            compare(saved[key], fresh[key], f"{path}.{key}")
    elif isinstance(saved, list) and isinstance(fresh, list) and len(saved) == len(fresh):
        for i, (left, right) in enumerate(zip(saved, fresh, strict=True)):
            compare(left, right, f"{path}[{i}]")
    elif saved != fresh:
        # Different FLINT builds can print different rounding radii.
        if isinstance(saved, str) and isinstance(fresh, str) and saved.startswith("[") and fresh.startswith("["):
            if arb(saved).overlaps(arb(fresh)):
                return
        raise ValueError(f"Archived and recomputed readings differ at {path}")


def main():
    ctx.prec = 256
    for script, filename in RECORDS:
        raw = subprocess.check_output([sys.executable, "-B", str(HERE / script)], cwd=HERE)
        result = json.loads(raw)
        compare(json.loads((HERE / filename).read_bytes()), result, filename)
        if filename == "gaussian-base-endpoints.json":
            for row in result["rows"]:
                for key in ("base_hardy_product", "zeta_hardy", "beta_hardy"):
                    assert arb(row[key]) > 0
        elif filename == "endpoint-refinement.json":
            for row, cap in zip(result["endpoints"], ("3.584e-19", "2.945e-19"), strict=True):
                lower = arb(row["completed_normalized_lower"])
                upper = arb(row["completed_normalized_upper"])
                assert -arb(cap) < lower and lower < 0 and 0 < upper and upper < arb(cap)
        print(f"Verified {filename}", flush=True)


if __name__ == "__main__":
    main()
