"""Verify the bytes and inventory of append-only research snapshots."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
NAME_PATTERN = re.compile(r"\d{4}-\d{2}-\d{2}-[a-z0-9]+(?:-[a-z0-9]+)*-v\d{3}")
MANIFEST = "manifest.json"


def inventory(snapshot):
    seen = set()
    files = {}
    for path in sorted(snapshot.rglob("*")):
        relative = path.relative_to(snapshot).as_posix()
        if path.is_symlink() or path.is_junction():
            raise ValueError(f"Linked path in snapshot: {relative}")
        folded = relative.casefold()
        if folded in seen:
            raise ValueError(f"Case-insensitive path collision: {relative}")
        seen.add(folded)
        if path.is_file() and relative != MANIFEST:
            with path.open("rb") as stream:
                digest = hashlib.file_digest(stream, "sha256").hexdigest()
            files[relative] = {"sha256": digest, "bytes": path.stat().st_size}
    if "README.md" not in files:
        raise ValueError(f"{snapshot.name} is missing README.md")
    return files


def verify_snapshot(snapshot):
    if (snapshot.is_symlink() or snapshot.is_junction() or not snapshot.is_dir()
            or not NAME_PATTERN.fullmatch(snapshot.name)):
        raise ValueError(f"Invalid snapshot directory: {snapshot}")
    actual = inventory(snapshot)
    saved = json.loads((snapshot / MANIFEST).read_text(encoding="utf-8"))
    if saved["snapshot"] != snapshot.name or saved["format_version"] != 1:
        raise ValueError(f"Invalid manifest header for {snapshot.name}")
    expected = saved["files"]
    if expected != actual:
        missing = set(expected) - set(actual)
        extra = set(actual) - set(expected)
        different = {name for name in set(expected) & set(actual) if expected[name] != actual[name]}
        raise ValueError(
            f"{snapshot.name}: missing {sorted(missing)}, extra {sorted(extra)}, "
            f"size or checksum mismatch {sorted(different)}"
        )
    return len(actual)


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True, encoding="utf-8")


def verify_previous_snapshots(base):
    if not base or base == "0" * 40:
        return
    if not re.fullmatch(r"[0-9a-f]{40}", base):
        raise ValueError("Expected a full hexadecimal Git commit SHA for --base")
    for path in git("ls-tree", "-d", "--name-only", "-z", base, "archive/").split("\0"):
        if path and git("diff", "--name-only", base, "HEAD", "--", path):
            raise ValueError(f"Existing snapshot changed: {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-manifest", type=Path, help="create a manifest for a new snapshot")
    parser.add_argument("--base", help="optional previous Git commit for append-only checks")
    args = parser.parse_args()
    archive = ROOT / "archive"
    try:
        if args.write_manifest:
            snapshot = args.write_manifest.resolve()
            if snapshot.parent != archive or not NAME_PATTERN.fullmatch(snapshot.name):
                raise ValueError("Choose an immediate snapshot directory under archive/")
            content = {"format_version": 1, "snapshot": snapshot.name, "files": inventory(snapshot)}
            with (snapshot / MANIFEST).open("x", encoding="utf-8", newline="\n") as stream:
                json.dump(content, stream, indent=2, sort_keys=True)
                stream.write("\n")
        snapshots = sorted(archive.iterdir())
        if not snapshots:
            raise ValueError("The archive has no snapshots")
        count = sum(verify_snapshot(snapshot) for snapshot in snapshots)
        verify_previous_snapshots(args.base)
    except (OSError, KeyError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Archive check failed: {error}\n")
    print(f"Verified {count} files across {len(snapshots)} snapshots.")


if __name__ == "__main__":
    main()
