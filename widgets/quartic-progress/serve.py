"""Serve a read-only view of the local quartic Lean replay."""

import argparse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
from threading import Lock
import time


HERE = Path(__file__).resolve().parent
REPLAY = HERE.parents[1] / "verification/quartic-kernel/.replay"
CERTIFICATE_PASS = "The kernel certificate passed the standard-axioms-only audit."
REPLAY_PASS = re.compile(
    r"^Clean full-proof replay passed: (\d+) modules built from source "
    r"using (\d+) verified certificate modules\.$", re.M
)
REPLAY_TOTAL = 95
PART = re.compile(r"Block(\d+)Part(\d+)")
BLOCK = re.compile(r"Block(\d+)")
FAILED_PART = re.compile(r"^Failed KernelNumerics\.(Block\d+Part\d+)\s", re.M)
RETRIED_BLOCK = re.compile(r"^Retrying KernelPrefixes\.Block(\d+)\b", re.M)
FAILED_ENCLOSURE = re.compile(r"^Failed KernelCells\.(Block\d+)\s", re.M)
RETRIED_ENCLOSURE = re.compile(r"^Retrying KernelCells\.(Block\d+)\b", re.M)
STARTED_ENCLOSURE = re.compile(r"^Checking KernelCells\.(Block\d+)\s", re.M)
FINISHED_ENCLOSURE = re.compile(r"^(?:Compiled|Reused) KernelCells\.(Block\d+)\s", re.M)
ENCLOSURE_RANGE = re.compile(r"^theorem block\d+ : checkCoreCellRange (\d+) (\d+) = true", re.M)
GRID_NODE = re.compile(r"^def node \(j : ℕ\) : ℚ := j / (\d+)$", re.M)
REPLAY_STAGE = re.compile(r"^Build directory: (.+)$", re.M)
EXPECTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
FINAL_THEOREM = "QuarticKernel.actual_quartic_certificate_kernel"
AXIOM_LINE = re.compile(
    rf"^(?:'{re.escape(FINAL_THEOREM)}' depends on axioms:|"
    rf"Checked input {re.escape(FINAL_THEOREM)}) \[([^\]]*)\]$", re.M
)


def ordered_names(folder, pattern):
    def key(name):
        return tuple(map(int, pattern.fullmatch(name).groups()))

    return sorted(
        (path.stem for path in folder.glob("*.lean") if pattern.fullmatch(path.stem)),
        key=key,
    )


def receipts(folder, names, now):
    if not folder.is_dir():
        return set(), 0
    with os.scandir(folder) as directory:
        entries = {entry.name: entry for entry in directory}
    saved = set()
    recent = 0
    for name in names:
        entry = entries.get(f"{name}.verified.json")
        if entry is None or f"{name}.olean" not in entries:
            continue
        saved.add(name)
        recent += entry.stat().st_mtime >= now - 15 * 60
    return saved, recent


def read_tail(path, limit=48_000):
    try:
        with path.open("rb") as stream:
            stat = os.fstat(stream.fileno())
            stream.seek(max(0, stat.st_size - limit))
            tail = stream.read().decode("utf-8-sig", errors="replace")
            return tail.replace("\r\n", "\n"), stat.st_mtime
    except FileNotFoundError:
        return "", 0


def full_proof_progress(transcript, build_root):
    match = REPLAY_STAGE.search(transcript)
    if not match:
        return 0
    stage = Path(match.group(1).strip()).resolve()
    if stage == build_root or not stage.is_relative_to(build_root):
        return 0
    return sum(path.with_suffix(".olean").is_file() for path in stage.rglob("*.verified"))


def audited_axioms(*transcripts):
    for transcript in transcripts:
        for match in AXIOM_LINE.finditer(transcript):
            names = match.group(1).split(", ")
            if sorted(names) == sorted(EXPECTED_AXIOMS):
                return EXPECTED_AXIOMS
    return ()


def enclosure_ranges(packet, modules, grid_source):
    if not modules:
        return {}, []
    grid_text = grid_source.read_text(encoding="utf-8-sig")
    denominator = int(GRID_NODE.search(grid_text).group(1))
    ranges = {}
    bands = []
    for index, name in enumerate(modules):
        source = (packet / "KernelCells" / f"{name}.lean").read_text(encoding="utf-8-sig")
        first, count = map(int, ENCLOSURE_RANGE.search(source).groups())
        lo, hi = first / denominator, (first + count) / denominator
        ranges[name] = {"first": first, "count": count, "lo": lo, "hi": hi}
        band_start = 4 * (first // (4 * denominator))
        if not bands or bands[-1]["lo"] != band_start:
            bands.append({"lo": lo, "hi": hi, "start": index, "stop": index + 1})
        else:
            bands[-1]["hi"] = hi
            bands[-1]["stop"] = index + 1
    return ranges, bands


class Progress:
    def __init__(self, packet, checkpoint, kernel_log, replay_log, replay_build_root, grid_source=None):
        self.parts = ordered_names(packet / "KernelNumerics", PART)
        self.blocks = ordered_names(packet / "KernelPrefixes", BLOCK)
        self.enclosures = ordered_names(packet / "KernelCells", BLOCK)
        if not self.parts or not self.blocks:
            raise ValueError("No Lean batch or block sources found")
        if grid_source is None:
            grid_source = packet / "QuarticGrid.lean"
            if not grid_source.is_file():
                grid_source = REPLAY.parent / "source/QuarticGrid.lean"
        self.enclosure_ranges, self.enclosure_bands = enclosure_ranges(packet, self.enclosures, grid_source)
        self.groups = [int(PART.fullmatch(name).group(1)) for name in self.parts]
        self.checkpoint = checkpoint
        self.kernel_log = kernel_log
        self.final_log = kernel_log.with_name(kernel_log.name.replace("-live.txt", ".txt"))
        self.replay_log = replay_log
        self.replay_build_root = replay_build_root.resolve()
        self.lock = Lock()
        self.cached_at = 0
        self.cached = b""

    def snapshot(self):
        with self.lock:
            now = time.time()
            if now - self.cached_at < 3:
                return self.cached
            parts, recent = receipts(self.checkpoint / "KernelNumerics", self.parts, now)
            blocks, _ = receipts(self.checkpoint / "KernelPrefixes", self.blocks, now)
            enclosed, _ = receipts(self.checkpoint / "KernelCells", self.enclosures, now)
            kernel, kernel_at = read_tail(self.kernel_log)
            failure_names = set()
            enclosure_failures = set()
            enclosure_active = {}
            for line in kernel.splitlines():
                if failed := FAILED_PART.match(line):
                    failure_names.add(failed.group(1))
                elif retried := RETRIED_BLOCK.match(line):
                    failure_names = {
                        name for name in failure_names
                        if PART.fullmatch(name).group(1) != retried.group(1)
                    }
                elif failed := FAILED_ENCLOSURE.match(line):
                    name = failed.group(1)
                    enclosure_failures.add(name)
                    enclosure_active.pop(name, None)
                elif retried := RETRIED_ENCLOSURE.match(line):
                    enclosure_failures.discard(retried.group(1))
                elif started := STARTED_ENCLOSURE.match(line):
                    enclosure_active[started.group(1)] = None
                elif finished := FINISHED_ENCLOSURE.match(line):
                    enclosure_active.pop(finished.group(1), None)
            final, _ = read_tail(self.final_log)
            replay, replay_at = read_tail(self.replay_log, limit=260_000)
            kernel_pass = CERTIFICATE_PASS in final.splitlines()
            replay_result = REPLAY_PASS.search(replay) if kernel_pass else None
            axioms = audited_axioms(replay, final) if replay_result else ()
            replay_pass = bool(replay_result and axioms)
            replay_count = 0
            replay_certificate_count = 0
            if replay_pass:
                replay_count, replay_certificate_count = map(int, replay_result.groups())
            elif kernel_pass:
                replay_count = full_proof_progress(replay, self.replay_build_root)
            problem = any(
                line.startswith(("Traceback (most recent call last):", "RuntimeError:"))
                for line in (replay if kernel_pass else kernel).splitlines()
            )
            activity_at = replay_at if kernel_pass else kernel_at
            if replay_pass:
                state = "complete"
            elif problem:
                state = "interrupted"
            elif kernel_pass:
                state = "replay" if REPLAY_STAGE.search(replay) else "ready"
            elif len(blocks) == len(self.blocks) and (
                "Compiled QuarticCheckedShellKernel " in kernel or enclosure_active
            ):
                state = "enclosures"
            elif enclosed:
                state = "enclosures"
            elif now - activity_at > 180:
                state = "waiting"
            elif len(parts) == len(self.parts):
                state = "assembly"
            else:
                state = "checking"
            live = None
            active = [name for name in enclosure_active if name not in enclosed and name in self.enclosure_ranges]
            if active:
                name = active[-1]
                live = {
                    "module": f"KernelCells.{name}",
                    "active": len(active),
                    **self.enclosure_ranges[name],
                }
            self.cached = json.dumps(
                {
                    "mode": "live",
                    "time": now,
                    "state": state,
                    "count": len(parts),
                    "total": len(self.parts),
                    "bits": "".join(
                        "1" if name in parts else "2" if name in failure_names else "0" for name in self.parts
                    ),
                    "groups": self.groups,
                    "blocks": len(blocks),
                    "blockTotal": len(self.blocks),
                    "enclosures": len(enclosed),
                    "enclosureTotal": len(self.enclosures),
                    "enclosureBands": self.enclosure_bands,
                    "enclosureLive": live,
                    "enclosureBits": "".join(
                        "1" if name in enclosed else "2" if name in enclosure_failures else "0"
                        for name in self.enclosures
                    ),
                    "kernelPass": kernel_pass,
                    "replayPass": replay_pass,
                    "replayCount": replay_count,
                    "replayTotal": replay_count if replay_pass else REPLAY_TOTAL,
                    "replayCertificateCount": replay_certificate_count,
                    "axioms": axioms,
                    "recent": recent,
                },
                separators=(",", ":"),
            ).encode()
            self.cached_at = now
            return self.cached


def make_handler(progress):
    files = {
        "/": ("text/html; charset=utf-8", HERE / "index.html"),
        "/style.css": ("text/css; charset=utf-8", HERE / "style.css"),
        "/progress.js": ("text/javascript; charset=utf-8", HERE / "progress.js"),
    }

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.headers.get("Host") != f"127.0.0.1:{self.server.server_port}":
                self.send_error(400)
                return
            if self.path == "/progress.json":
                mime, body = "application/json", progress.snapshot()
            elif self.path in files:
                mime, path = files[self.path]
                body = path.read_bytes()
            else:
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Type", mime)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Content-Security-Policy", "default-src 'self'; frame-ancestors 'none'; base-uri 'none'")
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, format, *args):
            pass

    return Handler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8766)
    parser.add_argument("--packet", type=Path, default=REPLAY / "generated")
    parser.add_argument("--checkpoint", type=Path, default=REPLAY / "certificate")
    parser.add_argument("--kernel-log", type=Path, default=REPLAY / "certificate.log")
    parser.add_argument("--replay-log", type=Path, default=REPLAY / "full.log")
    parser.add_argument("--replay-build-root", type=Path, default=REPLAY)
    parser.add_argument("--grid", type=Path, help="Override the source of the grid spacing")
    parser.add_argument("--freeze", type=Path, help="Write a frozen progress JSON file")
    args = parser.parse_args()
    progress = Progress(args.packet, args.checkpoint, args.kernel_log, args.replay_log, args.replay_build_root, args.grid)
    if args.freeze:
        snapshot = json.loads(progress.snapshot())
        snapshot["mode"] = "archive"
        with args.freeze.open("x", encoding="utf-8", newline="\n") as stream:
            stream.write(json.dumps(snapshot, separators=(",", ":")) + "\n")
        return
    with ThreadingHTTPServer(("127.0.0.1", args.port), make_handler(progress)) as server:
        print(f"Quartic verification at http://127.0.0.1:{server.server_port}/", flush=True)
        server.serve_forever()


if __name__ == "__main__":
    main()
