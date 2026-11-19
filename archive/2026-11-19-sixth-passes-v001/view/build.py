"""Export the sixth-branch fold viewer from a freshly calculated jets.json."""
import argparse
import json
import math
from pathlib import Path


FIELDS = ("alpha", "sigma", "T", "sigma1", "T1", "sigma2", "T2")
EVENTS = ("pass1", "maximum", "pass2", "minimum", "pass3")
SOURCE_DIR = Path(__file__).resolve().parent


def compact(row):
    values = [float(row[field]) for field in FIELDS]
    if not all(map(math.isfinite, values)):
        raise ValueError("Non-finite coordinate or derivative")
    return [round(value, 12) for value in values]


def plot_data(record):
    if tuple(e["id"] for e in record["events"]) != EVENTS:
        raise ValueError("Expected three passes separated by the two height folds")
    samples = [compact(dict(zip(record["columns"], row, strict=True)))
               for row in record["profiles"]]
    events = []
    for event in record["events"]:
        mid = event["mid"]
        spatial = [None if mid[k] is None else round(float(mid[k]), 12)
                   for k in ("Y_T", "Y_TT")]
        events.append(compact(mid) + spatial)
    if (any(a[0] >= b[0] for a, b in zip(samples, samples[1:]))
            or any(a[0] >= b[0] for a, b in zip(events, events[1:]))):
        raise ValueError("Angles must increase in the direction of travel")
    if len(samples) < 2 or samples[0][0] > events[0][0] - .25 or samples[-1][0] < events[-1][0] + .25:
        raise ValueError("Profile must cover the quarter-degree neighborhood of every pass")
    if any(e[2] != 37.25 for e in events[::2]) or any(e[4] != 0 for e in events[1::2]):
        raise ValueError("Expected crossings at T = 37.25 and height folds at T′ = 0")
    return json.dumps({"events": events, "samples": samples},
                      separators=(",", ":"), allow_nan=False)


def write_output(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8", newline="\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True, help="computed jets.json")
    parser.add_argument("--output", type=Path, required=True, help="standalone HTML file")
    parser.add_argument("--fragment", type=Path, help="optional embeddable HTML fragment")
    args = parser.parse_args()
    record = json.loads(args.data.read_text(encoding="utf-8"))
    fragment = (SOURCE_DIR / "fragment.html").read_text(encoding="utf-8")
    fragment = fragment.replace("__SIXTH_PASS_DATA__", plot_data(record))
    page = (SOURCE_DIR / "page.html").read_text(encoding="utf-8")
    write_output(args.output, page.replace("__SIXTH_PASS_VIEW__", fragment))
    if args.fragment:
        write_output(args.fragment, fragment)


if __name__ == "__main__":
    main()
