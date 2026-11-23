"""Use checked equalities to join the finished reductions without rerunning them."""
import argparse
from pathlib import Path
import re


MERGE = re.compile(
    r"^  have joined := bandStats_append (\d+) (\d+) (\d+) (\d+) (\d+)\n"
    r"  rw \[(\w+), (\w+)\] at joined\n  exact joined$",
    re.M,
)
ROWS = re.compile(
    r"^  rw \[annulusStats_band, show annulusRowCount (\d+) = (\d+) by decide \+kernel\]\n"
    r"  exact (\w+)$",
    re.M,
)
TAIL = re.compile(
    r"^  checkSpans_of_annulus \(i := (\d+)\) \(w := (\d+)\) \(s := (-?\d+)\)"
    r" \(ws := (\[[^\]]*\])\)\n    (\w+) \(by decide\) (\w+)$",
    re.M,
)
STATS = re.compile(
    r"^private theorem (\w+) : annulusStats (\d+) (\d+) = \((-?\d+), (-?\d+), (-?\d+)\)",
    re.M,
)


def numeral(n):
    return f"({n})" if n < 0 else str(n)


def rewrite(contents):
    stats = {name: tuple(map(int, values)) for name, *values in STATS.findall(contents)}

    def merge(match):
        lo, hi, a, m, n = map(int, match.groups()[:5])
        left, right = match.groups()[5:]
        return (
            f"  exact bandStats_join (lo := {lo}) (hi := {hi}) (a := {a}) (m := {m})\n"
            f"    (b := {a+m}) (n := {n}) (k := {m+n}) rfl rfl {left} {right} (by decide)"
        )

    def rows(match):
        hi, count, name = match.groups()
        return f"  exact annulusStats_of_band (hi := {hi}) (rows := {count}) (by decide +kernel) {name}"

    def tail(match):
        i, w, s = map(int, match.groups()[:3])
        ws, head, rest = match.groups()[3:]
        lo, hi, c, _, _ = stats[head]
        if lo != i or hi != i+w:
            raise ValueError(f"Inconsistent boundaries for {head}")
        return (
            f"  checkSpans_join (i := {i}) (j := {hi}) (w := {w}) (s := {numeral(s)})\n"
            f"    (next := {numeral(s+c)}) (ws := {ws}) rfl (by decide) (by decide) {head} (by decide) {rest}"
        )

    updated, merges = MERGE.subn(merge, contents)
    updated, rows_checked = ROWS.subn(rows, updated)
    updated, tails = TAIL.subn(tail, updated)
    if not merges or not len(stats) == rows_checked == tails:
        raise ValueError("Missing assembly substitutions")
    return (
        "import QuarticAnnulusAssembly\n" +
        updated.replace("set_option maxHeartbeats 0\n", "set_option maxHeartbeats 0\nset_option Elab.async false\n", 1)
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    args.destination.mkdir(parents=True, exist_ok=True)
    for path in sorted(args.source.glob("Block*.lean")):
        try:
            updated = rewrite(path.read_text(encoding="utf-8-sig"))
        except ValueError as exc:
            raise ValueError(f"Could not rewrite {path}") from exc
        (args.destination / path.name).write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    main()
