"""Run the pinned Lean executable on a resumable range of sharp score rows."""

import argparse
import hashlib
import os
import re
import subprocess
from pathlib import Path


CUTOFF = 1442840576
ROW_COUNT = 37984
COLUMNS = 22
ROW = re.compile(rb"[0-9]+(?:\t-?[0-9]+){22}\r?\n")


def check_row(record, expected):
    if not ROW.fullmatch(record) or int(record.split(b"\t", 1)[0]) != expected:
        raise ValueError(f"Invalid or out-of-order record at row {expected}")


def resume(stream, header, first, stop):
    stream.seek(0)
    initial = stream.readline()
    if initial and not initial.endswith(b"\n") and header.startswith(initial):
        stream.truncate(0)
        initial = b""
    if not initial:
        stream.write(header)
        stream.flush()
        return first
    if initial != header:
        raise ValueError("Checkpoint range or Lean entry point has changed")
    expected = first
    while True:
        offset = stream.tell()
        record = stream.readline()
        if not record:
            return expected
        if not record.endswith(b"\n"):
            stream.truncate(offset)
            return expected
        if expected >= stop:
            raise ValueError("Checkpoint extends beyond the requested range")
        check_row(record, expected)
        expected += 1


def lock_output(lock):
    if os.name == "nt":
        import msvcrt

        lock.seek(0)
        msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
    else:
        import fcntl

        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)


def replay(args, stream, header):
    first_missing = resume(stream, header, args.first, args.stop)
    if first_missing == args.stop:
        print(f"{args.first}:{args.stop} complete", flush=True)
        return
    argv = [
        str(args.lean.resolve()), "-j1", "-s65536", "-M3200", "-DwarningAsError=true",
        "--run", str(args.entry.resolve()), str(first_missing), str(args.stop),
    ]
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    row = first_missing
    with subprocess.Popen(argv, stdout=subprocess.PIPE, env=env) as proc:
        try:
            for record in proc.stdout:
                if row >= args.stop:
                    raise ValueError("Lean emitted more rows than requested")
                check_row(record, row)
                stream.write(record.replace(b"\r\n", b"\n"))
                stream.flush()
                row += 1
                if (row - first_missing) % 32 == 0:
                    os.fsync(stream.fileno())
        except BaseException:
            if proc.poll() is None:
                proc.kill()
            raise
        status = proc.wait()
    os.fsync(stream.fileno())
    if status or row != args.stop:
        raise RuntimeError(f"Lean exited {status} after saving rows {first_missing}:{row}")
    print(f"{args.first}:{args.stop} complete", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean", type=Path)
    parser.add_argument("entry", type=Path)
    parser.add_argument("first", type=int)
    parser.add_argument("stop", type=int)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if not 0 <= args.first < args.stop <= ROW_COUNT:
        parser.error("Expected a nonempty zero-based range within the sharp prefix")
    digest = hashlib.sha256(args.entry.read_bytes()).hexdigest()
    header = f"# dottie-sharp-v1 {CUTOFF} {COLUMNS} {args.first} {args.stop} {digest}\n".encode()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.with_suffix(args.output.suffix + ".lock").open("a+b") as lock:
        lock_output(lock)
        with args.output.open("a+b") as stream:
            replay(args, stream, header)


if __name__ == "__main__":
    main()
