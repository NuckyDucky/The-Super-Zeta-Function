"""Render two Cartesian Dottie views with the Reciprocal Tetration Lab's Layer 4."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import tempfile


HERE = Path(__file__).resolve().parent
VIEWS = (
    {
        "name": "Spire overview",
        "pixels": (1560, 1120),
        "real": ("-0.145", "0.145"),
        "imag": ("0.492", "0.748"),
    },
    {
        "name": "Detail near the tip",
        "pixels": (864, 1120),
        "real": ("-0.0065", "0.0065"),
        "imag": ("0.5085", "0.5485"),
    },
)
SETTINGS = {
    "mode": "paired",
    "max_steps": 8000,
    "max_period": 256,
    "tolerance": "1e-10",
    "initial_P": "1",
    "initial_Q": "1",
    "legacy_zero_cutoff": False,
    "samples_per_pixel": 4,
    "gpu_memory_mb": 384,
    "gpu_step_chunk": 256,
}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def viewport(view):
    from decimal import Decimal

    left, right = map(Decimal, view["real"])
    bottom, top = map(Decimal, view["imag"])
    return {
        "mapping": "cartesian",
        "center_re": str((left + right) / 2),
        "center_im": str((bottom + top) / 2),
        "width": str(right - left),
        "height": str(top - bottom),
    }


def render_panel(view, engine, gpu_engine, mapping, np):
    width, height = view["pixels"]
    area = viewport(view)
    precision = mapping.precision_plan(area, 2 * width, 2 * height, "auto")
    if precision["digits"] != 16:
        raise ValueError("These Layer 4 coordinates must pass the Lab's binary64 precision check.")
    precision["backend"] = "CUDA binary64"
    colors = np.empty((height, width, 3), dtype=np.uint8)
    center_counts = Counter()
    subpixel_counts = Counter()
    mixed = 0
    peak_gpu_bytes = 0
    for start in range(0, height, 96):
        rows = min(96, height - start)
        real, imag = mapping.grid_coordinates(area, 2 * width, 2 * height, 16, 2 * start, 2 * rows)
        subpixels = gpu_engine.classify_grid(real, imag, SETTINGS, digits=16)
        rgb = engine.colorize(subpixels, "period").reshape(rows, 2, width, 2, 3)
        colors[start:start + rows] = rgb.mean(axis=(1, 3)).round().astype(np.uint8)
        codes = subpixels["code"].reshape(rows, 2, width, 2)
        mixed += int(np.count_nonzero(np.any(codes != codes[:, :1, :, :1], axis=(1, 3))))
        values, counts = np.unique(codes, return_counts=True)
        subpixel_counts.update({int(k): int(v) for k, v in zip(values, counts)})

        # The even 2-by-2 color grid does not contain the pixel center. Match
        # the Lab renderer and classify each center independently.
        real, imag = mapping.grid_coordinates(area, width, height, 16, start, rows)
        centers = gpu_engine.classify_grid(real, imag, SETTINGS, digits=16)
        values, counts = np.unique(centers["code"], return_counts=True)
        center_counts.update({int(k): int(v) for k, v in zip(values, counts)})
        peak_gpu_bytes = max(
            peak_gpu_bytes,
            subpixels["gpu"]["peak_working_array_bytes"],
            centers["gpu"]["peak_working_array_bytes"],
        )
        print(f"{view['name']}: {start + rows}/{height} rows", flush=True)

    assert sum(center_counts.values()) == width * height
    assert sum(subpixel_counts.values()) == 4 * width * height
    assert min(center_counts) >= -4 and min(subpixel_counts) >= -4
    assert max(center_counts) <= SETTINGS["max_period"]
    return colors, {
        **view,
        "viewport": area,
        "precision": precision,
        "color_samples": 4 * width * height,
        "independent_center_samples": width * height,
        "mixed_color_pixels": mixed,
        "center_counts": dict(sorted(center_counts.items())),
        "subpixel_counts": dict(sorted(subpixel_counts.items())),
        "peak_gpu_working_array_bytes": peak_gpu_bytes,
        "color_raster_sha256": sha256(colors.tobytes()),
    }


def make_figure(rendered, engine, mapping, np, plt, output):
    from matplotlib.patches import Patch, Rectangle

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "text.color": "#182a3e",
        "axes.labelcolor": "#182a3e",
        "axes.edgecolor": "#7a8797",
        "xtick.color": "#31445a",
        "ytick.color": "#31445a",
    })
    figure = plt.figure(figsize=(12.7, 7.95), facecolor="white")
    axes = (figure.add_axes([0.073, 0.168, 0.529, 0.668]),
            figure.add_axes([0.675, 0.168, 0.295, 0.668]))
    figure.text(0.073, 0.943, "The Dottie spire", fontsize=25, weight="bold")
    figure.text(0.073, 0.900, "Detected periods of the ordered exponential map in the complex parameter plane",
                fontsize=11.5, color="#43566b")
    tip = float(mapping.special_constants(45)["ystar"])
    for ax, view, colors in zip(axes, VIEWS, rendered):
        left, right = map(float, view["real"])
        bottom, top = map(float, view["imag"])
        ax.imshow(colors, extent=(left, right, bottom, top), origin="upper",
                  interpolation="nearest", resample=False, aspect="auto")
        ax.set_title(view["name"], loc="left", pad=10, fontsize=13, weight="bold")
        ax.set_xlabel("Re $L$", fontsize=12, labelpad=6)
        ax.set_ylabel("Im $L$", fontsize=12, labelpad=7)
        ax.tick_params(labelsize=9, length=3, width=0.7)
        ax.scatter([0], [tip], color="white", edgecolors="#162334", linewidths=1.2,
                   zorder=5, s=38)

    inset = VIEWS[1]
    left, right = map(float, inset["real"])
    bottom, top = map(float, inset["imag"])
    axes[0].add_patch(Rectangle((left, bottom), right - left, top - bottom,
                                fill=False, lw=1.2, ls="--", ec="white", zorder=4))
    axes[0].annotate("detail shown at right", (right, top), (0.05, 0.567),
                     arrowprops={"arrowstyle": "-", "color": "white", "lw": 0.8},
                     color="white", fontsize=9, va="bottom")
    axes[1].annotate("Dottie tip", (0, tip), (0.00125, 0.5127),
                     arrowprops={"arrowstyle": "-", "color": "white", "lw": 0.85},
                     color="white", fontsize=9, va="bottom")
    palette_codes = [1, 20, 0, -1, -4]
    palette = engine.colorize({"code": np.array(palette_codes)}, "period") / 255
    labels = ["Fixed pair", "Periodic (hue varies with period)", "Unresolved at 8,000 steps",
              "Arithmetic limit", "Phase precision limit"]
    figure.legend([Patch(color=color) for color in palette], labels,
                  loc="lower left", bbox_to_anchor=(0.068, 0.058), ncols=5,
                  frameon=False, columnspacing=1.4, handlelength=1.05, fontsize=9)
    figure.text(0.073, 0.032, "Four computed color samples per pixel  ·  Pair periods up to 256",
                fontsize=9.5, color="#43566b")
    figure.savefig(output, dpi=200, facecolor="white",
                   metadata={"Title": "The Dottie spire", "Description": "Lab Layer 4 numerical survey"})
    plt.close(figure)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lab-directory", type=Path, default=HERE / "lab_source",
                        help="directory containing engine.py, gpu_engine.py and mapping.py")
    parser.add_argument("--output-directory", type=Path, default=HERE)
    args = parser.parse_args()
    lab_dir = args.lab_directory.resolve()
    sources = ["engine.py", "gpu_engine.py", "mapping.py"]
    hashes = {}
    for name in sources:
        path = lab_dir / name
        if not path.is_file():
            parser.error(f"{path} is missing. Supply the Reciprocal Tetration Lab source directory.")
        hashes[name] = sha256(path.read_bytes())
    preset_file = lab_dir / "static" / "app.js"
    if preset_file.is_file():
        source = preset_file.read_bytes()
        if b"4:{size:'native',steps:8000,spp:4" not in source:
            parser.error("The installed Lab Layer 4 preset differs from the surveyed preset.")
        hashes["static/app.js"] = sha256(source)

    sys.path.insert(0, str(lab_dir))
    args.output_directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="dottie-figure-") as cache:
        os.environ.setdefault("CUPY_CACHE_DIR", str(Path(cache) / "cupy"))
        os.environ.setdefault("MPLCONFIGDIR", str(Path(cache) / "mpl"))
        import engine
        import gpu_engine
        import mapping
        import matplotlib
        import numpy as np

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        hardware = gpu_engine.device_info()
        if not hardware["available"]:
            raise RuntimeError(f"CUDA Lab backend unavailable: {hardware.get('error')}")
        rendered, evidence = zip(*(render_panel(view, engine, gpu_engine, mapping, np)
                                   for view in VIEWS))
        png = args.output_directory / "dottie-spire.png"
        make_figure(rendered, engine, mapping, np, plt, png)
        record = {
            "figure": png.name,
            "figure_sha256": sha256(png.read_bytes()),
            "figure_size_pixels": [2540, 1590],
            "renderer": "Reciprocal Tetration Lab Layer 4 (Fine)",
            "lab_source_sha256": hashes,
            "settings": SETTINGS,
            "checkpoints": [512, 1024, 2048, 4096, 8000],
            "arithmetic": "CUDA binary64",
            "hardware": {key: hardware[key] for key in
                         ("name", "cupy_version", "cuda_runtime_version", "cuda_driver_version",
                          "compute_capability", "fused_multiply_add")},
            "runtime": {"python": sys.version.split()[0], **{
                name: importlib.metadata.version(name)
                for name in ("numpy", "matplotlib", "mpmath", "Pillow")
            }},
            "dottie_tip_im": mapping.special_constants(45)["ystar"],
            "panels": evidence,
            "code_labels": {"-4": "phase precision limit", "-1": "arithmetic limit",
                            "0": "unresolved at iteration limit", "1": "fixed pair",
                            "2..256": "detected pair period"},
            "scope": "Numerical three-complete-lap period detections on independently computed grids.",
        }
        (args.output_directory / "dottie-spire-render.json").write_text(
            json.dumps(record, indent=2) + "\n", encoding="utf-8")
        print(f"{png.name}: {record['figure_sha256']}", flush=True)


if __name__ == "__main__":
    main()
