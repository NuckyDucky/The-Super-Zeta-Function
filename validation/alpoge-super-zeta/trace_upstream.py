"""Read pinned Lean import headers from Git, including sparse or missing worktree files."""

from argparse import ArgumentParser
from collections import deque
from pathlib import Path
import json
import re
import subprocess


ROOT = Path(__file__).resolve().parents[3]
UPSTREAM = ROOT / "work" / "alpoge-rh"
PIN = "ba2a065656ec7c638baa601994de3e0245ff6665"
DEDUCTION = "Development.AutomorphicArithmetic.DedekindLFunctions"
LANDAU = f"{DEDUCTION}.LandauTheorems"
CHARACTER = "Development.AutomorphicArithmetic.CharacterBoxes"
LEVEL = "Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses"
ROOTS = {
    "headline": ("Main", f"{CHARACTER}.MainConclusion"),
    "reflection": ("Formalism.GammaFactorNonvanishing.RhOfRight",
                   f"{LANDAU}.LFunctionConj"),
    "characters": ("Statements", f"{CHARACTER}.ClaimStrip"),
    "continuation_and_residues": (f"{LANDAU}.poleData", f"{LANDAU}.LogDerivLocal"),
    "prime_powers_and_smoothing": ("Formalism.StatementOC", f"{DEDUCTION}.CharFamily",
                                   f"{LANDAU}.mellinGchiOfNeOne",
                                   f"{LANDAU}.mellinGchiModOne"),
    "signed_windows": (f"{LANDAU}.landauWindow", f"{LANDAU}.ZeroFreeOfRpowWindow",
                       f"{LANDAU}.WindowHypUOfWindowHyp", f"{LEVEL}.TopWin"),
}
ANALYTIC_ROOTS = {name: (f"{LANDAU}.{name}",)
                  for name in ("poleData", "landauWindow", "LogDerivLocal")}
BRIDGE_ROOTS = ("Formalism.GammaFactorNonvanishing.RhOfRight", "Statements")
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)")


def git(*args):
    return subprocess.check_output(["git", "-C", str(UPSTREAM), *args])


def named_sources():
    return {
        path[4:-5].replace("/", "."): path
        for path in git("ls-tree", "-r", "--name-only", PIN, "src").decode().splitlines()
        if path.endswith(".lean") and path.startswith("src/")
    }


def read_edges(process, path):
    process.stdin.write(f"{PIN}:{path}\n".encode())
    process.stdin.flush()
    header = process.stdout.readline().decode().strip().split()
    if len(header) != 3 or header[1] != "blob":
        raise RuntimeError(f"Cannot read pinned blob {path}: {header}")
    blob = process.stdout.read(int(header[2]))
    if process.stdout.read(1) != b"\n":
        raise RuntimeError(f"Incomplete pinned blob {path}")
    return sorted({m.group(1) for line in blob.decode().splitlines()
                   if (m := IMPORT.match(line))})


def trace(roots=ROOTS, depth=2):
    sources = named_sources()
    traced = {}
    with subprocess.Popen(
        ["git", "-C", str(UPSTREAM), "cat-file", "--batch"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    ) as process:
        for label, entries in roots.items():
            queue = deque((root, 0) for root in entries)
            edges = {}
            while queue:
                module, distance = queue.popleft()
                if module in edges:
                    continue
                imports = read_edges(process, sources[module])
                edges[module] = imports
                if distance < depth:
                    queue.extend((name, distance + 1) for name in imports if name in sources)
            traced[label] = {"roots": entries, "modules_read": len(edges), "imports": edges}
        process.stdin.close()
        if process.wait() != 0:
            raise RuntimeError("git cat-file failed")
    return {"commit": PIN, "depth_from_each_root": depth, "lanes": traced}


def stage_analytic(result):
    folder = Path(__file__).resolve().parent
    edges = {name: deps for lane in result["lanes"].values()
             for name, deps in lane["imports"].items()}
    ordered = {}

    def place(name):
        if name in ordered:
            return
        for child in edges.get(name, ()):
            if child in edges:
                place(child)
        relative = Path(*name.split(".")).with_suffix(".lean")
        source = git("show", f"{PIN}:src/{relative.as_posix()}")
        target = folder / "upstream" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != source:
            raise RuntimeError(f"Pinned source differs from existing {target}")
        if not target.exists():
            target.write_bytes(source)
        ordered[name] = relative.with_suffix("").as_posix()

    for name in BRIDGE_ROOTS:
        place(name)
    for lane in ANALYTIC_ROOTS.values():
        for name in lane:
            place(name)
    (folder / "upstream-analytic-order.txt").write_text(
        "\n".join(ordered.values()) + "\n", encoding="utf-8")
    print(f"Staged {len(ordered)} modules from pinned Git blobs")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=UPSTREAM,
                        help="Local Git checkout of Deicyde/riemann-hypothesis")
    parser.add_argument("--stage-analytic", action="store_true",
                        help="Stage the small pole and window import closures and their build order")
    args = parser.parse_args()
    UPSTREAM = args.upstream.resolve()
    result = trace()
    target = Path(__file__).with_name("upstream-imports.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    summary = {"commit": PIN, "depth_from_each_root": result["depth_from_each_root"],
               "lanes": {key: {"roots": lane["roots"], "modules_read": lane["modules_read"],
                               "root_imports": {name: lane["imports"][name] for name in lane["roots"]}}
                         for key, lane in result["lanes"].items()}}
    target.with_name("upstream-summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    for name, lane in result["lanes"].items():
        print(f"{name}: {lane['modules_read']} upstream import headers")
    if args.stage_analytic:
        analytic = trace(ANALYTIC_ROOTS, depth=64)
        target.with_name("upstream-analytic-closures.json").write_text(
            json.dumps(analytic, indent=2) + "\n", encoding="utf-8")
        stage_analytic(analytic)
