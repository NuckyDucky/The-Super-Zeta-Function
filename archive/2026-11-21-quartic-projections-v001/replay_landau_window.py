"""Check the original proof bodies for Deduction.landau_window in one Lean run."""

from hashlib import sha256
import argparse
from pathlib import Path
import subprocess
import tempfile


focus = "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow"
expected_commit = "ba2a065656ec7c638baa601994de3e0245ff6665"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Pinned Alpöge source with its mathlib cache")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    source = checkout / "src"
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if revision != expected_commit:
        raise ValueError(f"Unexpected checkout revision {revision}")
    external_imports = set()
    bodies = {}
    checksums = {}

    def visit(name):
        if name in bodies:
            return
        path = source.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.exists():
            if name != "Mathlib" and not name.startswith("Mathlib."):
                raise ValueError(f"Unresolved import {name}")
            external_imports.add(name)
            return
        raw = subprocess.check_output(["git", "-C", str(checkout), "show", f"{revision}:{path.relative_to(checkout).as_posix()}"])
        checksums[name] = sha256(raw).hexdigest()
        body = []
        for line in raw.decode("utf-8").splitlines(keepends=True):
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    visit(dependency)
            else:
                body.append(line)
        bodies[name] = "".join(body)

    visit(focus)
    print(f"Upstream {revision}, {len(bodies)} modules", flush=True)
    for name in bodies:
        print(checksums[name], name, flush=True)
    with tempfile.TemporaryDirectory() as directory:
        merged = Path(directory) / "ImportedLandauWindow.lean"
        merged.write_text("\n".join(f"import {name}" for name in sorted(external_imports)) + "\n" +
                          "\n".join(bodies.values()) + "\n#print axioms Deduction.landau_window\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(merged)], cwd=checkout, timeout=300)
        return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
