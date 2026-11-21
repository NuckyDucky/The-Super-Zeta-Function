"""Plot archived endpoint classifications from basins.npz using NumPy and Pillow.

For the two thin curves only, reintegrate w' = ell*f/f' from w=37i with the
archived time step, using Euler–Maclaurin for f's Riemann-zeta factor.
"""
import json
from math import cos, pi, sin
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw

from lattice_direction import GRID, INK, MUTED, OUT, PAPER, dot, label


ATLAS = OUT.parents[1] / "archive" / "2026-11-19-dottie-plane-atlas-v001" / "atlas"
# Class indices, mathematical labels, and original colors from atlas/basin_map.py.
KEY = [
    (2, "ρ₅", "#E2D3A2"), (3, "ρ₆", "#267D87"), (4, "ρ₇", "#8170A8"),
    (5, "ρ₈", "#6687A2"), (10, "8πi / log 2", "#E59A55"), (-1, "?", "#D5D6D8"),
]
BERNOULLI = (1/12, -1/720, 1/30240, -1/1209600, 1/47900160)
N = 96
LOG_N = np.log(N)
LOG_NATURALS = np.log(np.arange(1, N))
LOG_2 = np.log(2)


def newton_step(w):
    """Evaluate f/f' where f=2^w (2^w-1) zeta(w)."""
    terms = np.exp(-w * LOG_NATURALS)
    n_to_minus_w = np.exp(-w * LOG_N)
    ratio = N / (w - 1) + .5
    ratio_derivative = -N / (w - 1)**2
    rising, derivative = 1, 0
    for index in range(1, 2*len(BERNOULLI)):
        factor = w + index - 1
        rising, derivative = rising*factor, derivative*factor + rising
        if index % 2:
            c = BERNOULLI[index//2] * N**(-index)
            ratio += c*rising
            ratio_derivative += c*derivative
    zeta = terms.sum() + n_to_minus_w*ratio
    dzeta = -(LOG_NATURALS*terms).sum() + n_to_minus_w*(ratio_derivative - LOG_N*ratio)
    a = np.exp(w*LOG_2)
    return (a-1)*zeta / (LOG_2*(2*a-1)*zeta + (a-1)*dzeta)


def measured_path(record):
    def center(text):
        return float(text.strip("[]").split()[0])

    ell = complex(*map(center, record["ell"]))
    h = .008
    z = 37j
    path = [z]
    for _ in range(500):
        k1 = ell * newton_step(z)
        k2 = ell * newton_step(z+h*k1/2)
        k3 = ell * newton_step(z+h*k2/2)
        k4 = ell * newton_step(z+h*k3)
        z += h*(k1+2*k2+2*k3+k4)/6
        path.append(z)
    reference = complex(*map(center, record["cutoff_center"]))
    if abs(z-reference) > 1e-5:
        raise ValueError("Reintegrated four-lap trajectory disagrees with archived endpoint.")
    return path


def star(draw, xy):
    points = []
    for j in range(10):
        a = -pi/2 + pi*j/5
        r = 9 if j%2 == 0 else 4
        points.append((xy[0]+r*cos(a), xy[1]+r*sin(a)))
    draw.polygon(points, fill=PAPER, outline=INK, width=2)


def main():
    saved = np.load(ATLAS / "basins.npz", allow_pickle=False)
    certificate = json.loads((ATLAS / "basin_certificate.json").read_text())
    xs, ys = saved["xs"], saved["ys"]
    classes = saved["classes"]
    assert classes.shape == (2, len(ys), len(xs))
    assert set(np.unique(classes)) == {k for k, _, _ in KEY}
    assert all(np.array_equal(layer, np.where(a == b, a, -1))
               for layer, (a,b) in zip(classes, saved["raw"].reshape(2,2,len(ys),len(xs))))
    im = Image.new("RGB", (891, 707), PAPER)
    draw = ImageDraw.Draw(im)
    width, height = 300, 522
    top = 57
    bottom = top + height
    x_indices = np.rint(np.linspace(0, len(xs)-1, width)).astype(int)
    y_indices = np.rint(np.linspace(len(ys)-1, 0, height)).astype(int)
    for j, (x0, title, key) in enumerate(((83, "+π/4", "principal_k4"),
                                           (505, "−7π/4", "ordered_rho6"))):
        def position(w):
            return (x0+(width-1)*(w.real-xs[0])/(xs[-1]-xs[0]),
                    bottom-1-(height-1)*(w.imag-ys[0])/(ys[-1]-ys[0]))

        values = classes[j][np.ix_(y_indices, x_indices)]
        pixels = np.empty((height,width,3), dtype=np.uint8)
        for index, _, color in KEY:
            pixels[values == index] = tuple(bytes.fromhex(color[1:]))
        im.paste(Image.fromarray(pixels), (x0,top))
        draw.rectangle((x0,top,x0+width-1,bottom-1), outline=MUTED, width=1)
        label(draw, (x0+width/2,29), "ℑ ℓ = "+title, 28, bold=True)
        for x in (-1,0,1):
            px,_ = position(x)
            draw.line((px,bottom,px,bottom+5),fill=INK,width=1)
            label(draw,(px,bottom+20),str(x).replace("-","−"),18,MUTED)
        for y in (35,36,37,38,39):
            _,py = position(y*1j)
            draw.line((x0-4,py,x0,py),fill=INK,width=1)
            label(draw,(x0-8,py),str(y),18,MUTED,anchor="rm")
        label(draw,(x0-42,top-20),"ℑ w₀",19)
        label(draw,(x0+width+9,bottom+19),"ℜ w₀",19,anchor="lm")
        path = [position(z) for z in measured_path(certificate[key])]
        draw.line(path,fill=INK,width=5)
        draw.line(path,fill=PAPER,width=2)
        for root in saved["roots"]:
            if xs[0] < root.real < xs[-1] and ys[0] < root.imag < ys[-1]:
                star(draw, position(root))
        dot(draw,position(37j),6,PAPER)
        dot(draw,position(37j),4,INK)
    draw.line((40,631,850,631),fill=GRID,width=2)
    for x,(_,name,color) in zip((56,177,298,419,542,758),KEY):
        draw.rectangle((x,655,x+30,681),fill=color,outline=MUTED,width=1)
        label(draw,(x+41,668),name,24,anchor="lm")
    im.save(OUT / "proof-basins.png", optimize=True)


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True,parents=True)
    main()
