"""Recompute all eight records and check the stated numerical conclusions."""
import json
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
ARC_RUNS = ((16384, 64), (65536, 64), (65536, 512), (262144, 64), (1048576, 64))


def check_arc(record, cutoff, arcs):
    assert (record["N"], record["full_circle_ccw_arcs"]) == (cutoff, arcs)
    assert record["disk_center"] == "33/64+i(T_D-1/512)" and record["disk_radius"] == "15/1024"
    assert record["arcs_containing_zero"] == arcs
    assert [row["arc"] for row in record["arcs"]] == list(range(arcs))
    assert all(row["contains_zero"] for row in record["arcs"])
    assert record["exact_smoothed_finite_winding"] == (None if (cutoff, arcs) == (65536, 64) else 0)
    finite_error = arb(record["short_weight_error_bound"])
    maximum = arb(record["maximum_smoothed_prefix_real_part_upper"])
    if cutoff == 16384:
        assert maximum < 0
    elif cutoff == 262144:
        assert maximum < arb("-7.6098e-29")
        assert arb(record["omitted_norm_error_bound"]) < arb("2.312e-17")
    elif cutoff == 1048576:
        assert arb(record["minimum_arc_prefix_real_part_lower"]) - finite_error > 0
    else:
        east, _, _, south = record["prefix_at_east_north_west_south"]
        assert arb(east.split(" + ")[0]) - finite_error > 0
        assert arb(south.split(" + ")[0]) + finite_error < 0


def reproduce(directory, name, args):
    destination = directory / name
    subprocess.run([sys.executable, "-B", *args, str(destination)], check=True, cwd=HERE,
                   stdout=subprocess.DEVNULL)
    fresh = json.loads(destination.read_text(encoding="utf-8"))
    archived = json.loads((HERE / name).read_text(encoding="utf-8"))
    if fresh != archived:
        raise ValueError(f"{name}: calculation differs from archived JSON values")
    print(f"Reproduced {name}", flush=True)
    return fresh


def main():
    if not __debug__:
        raise ValueError("Run without Python's -O flag so the enclosure checks are active.")
    ctx.prec = 192
    with TemporaryDirectory() as tmp:
        output = Path(tmp)
        for cutoff, arcs in ARC_RUNS:
            name = "arc-gaussian.json" if cutoff == 16384 else f"arc-gaussian-{cutoff}-{arcs}.json"
            result = reproduce(output, name, ["arc-gaussian.py", "--cutoff", str(cutoff),
                                              "--arcs", str(arcs), "--save"])
            check_arc(result, cutoff, arcs)
        for cutoff, name, band_max in ((2**20, "fourier-count.json", 16),
                                       (2**23, "fourier-count-2pow23.json", 15)):
            result = reproduce(output, name, ["fourier_count.py", "--cutoff", str(cutoff), "--save"])
            assert result["closed_band_count_at_most"] == band_max
            assert result["count_per_closed_disk_at_most"] == band_max // 2
        result = reproduce(output, "mass-count.json", ["mass.py", "10000000"])
        assert arb(result["total_upper"]) < arb("87.057901")
        assert arb(result["single_zero_min"]) > arb("5.481507")
        assert arb("87.057901") < 16 * arb("5.481507")
        assert result["upper_count"] == 7


if __name__ == "__main__":
    main()
