"""Rebuild the two ordered-lattice figures and two Gaussian-direction figures.

Use Python 3 with Pillow. Equations and examples are in
docs/proofs/marked-gaussian-direction.md and
archive/2026-11-20-dedekind-phase-v001/README.md.
"""

from functools import lru_cache
from math import atan2, cos, pi, sin, sqrt
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


OUT = Path(__file__).resolve().parents[2] / "docs" / "figures"
PAPER = "#FAF8F2"
INK = "#18323F"
MUTED = "#4F6470"
GRID = "#D2DAD7"
TEAL = "#006D70"
OCHRE = "#9D521C"
PALE_TEAL = "#D4E8E3"
PALE_OCHRE = "#F5E1CE"
CONDUCTOR = (41, 457, 1414835497)
DELTA = (-5045155, 1027708)
U_MIN, U_MAX = pi / 6, pi / 4


@lru_cache
def font(size, bold=False):
    names = (["DejaVuSans-Bold.ttf", "segoeuib.ttf"] if bold
             else ["DejaVuSans.ttf", "segoeui.ttf"])
    for name in names:
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            continue
    raise OSError("Install DejaVu Sans or Segoe UI to generate the figures.")


def label(draw, xy, text, size=24, color=INK, *, bold=False, anchor="mm"):
    draw.text(xy, text, font=font(size, bold), fill=color, anchor=anchor)


def page(width, height):
    image = Image.new("RGB", (width, height), PAPER)
    return image, ImageDraw.Draw(image)


def dot(draw, center, radius, fill):
    x, y = center
    draw.ellipse((x-radius, y-radius, x+radius, y+radius), fill=fill)


def arrow(draw, start, end, color, width=3):
    draw.line([start, end], fill=color, width=width)
    x, y = end
    angle = atan2(y-start[1], x-start[0])
    draw.polygon([(x, y), (x-13*cos(angle-.43), y-13*sin(angle-.43)),
                  (x-13*cos(angle+.43), y-13*sin(angle+.43))], fill=color)


def save_animation(frames, durations, filename):
    indexed = [im.convert("P", palette=Image.Palette.ADAPTIVE, colors=96) for im in frames]
    indexed[0].save(OUT / filename, save_all=True, append_images=indexed[1:],
                    duration=durations, loop=0, optimize=True, disposal=1)


def lattice_frame(u):
    image, draw = page(1120, 456)
    tau = complex(-cos(2*u), sin(2*u))
    cx, cy, scale = 243, 252, 102

    def position(z):
        return cx + scale*z.real, cy - scale*z.imag

    arrow(draw, (28, cy), (502, cy), GRID)
    arrow(draw, (cx, 414), (cx, 29), GRID)
    label(draw, (495, cy+20), "ℜ z", 20, MUTED)
    label(draw, (cx+25, 29), "ℑ z", 20, MUTED)
    for m in range(-5, 6):
        for n in range(-4, 5):
            xy = position(m + n*tau)
            if 32 < xy[0] < 500 and 37 < xy[1] < 416:
                dot(draw, xy, 3, MUTED)
    cell = [position(z) for z in (0j, 1, 1+tau, tau)]
    draw.polygon(cell, fill=PALE_TEAL)
    draw.line([*cell, cell[0]], fill=TEAL, width=2)
    for z, name, offsets in [(1, "1", (10, 16)), (tau, "τ", (-13, -16))]:
        x, y = position(z)
        arrow(draw, position(0j), (x, y), TEAL, 5)
        label(draw, (x+offsets[0], y+offsets[1]), name, 28, TEAL, bold=True)
    x, y = position(1+tau)
    dot(draw, (x, y), 8, OCHRE)
    label(draw, (x+7, y-19), "1 + τ", 24, OCHRE, bold=True, anchor="lm")
    label(draw, (cx-13, cy+14), "0", 19, MUTED)
    draw.line((545, 35, 545, 414), fill=GRID, width=2)

    x0, x1, y0, y1 = 649, 1047, 354, 86

    def graph(angle):
        return x0 + (x1-x0)*(angle-U_MIN)/(U_MAX-U_MIN), y0 - (y0-y1)*(4*sin(angle)**2-1)

    for val in (1, 1.5, 2):
        yy = y0 - (y0-y1)*(val-1)
        draw.line((x0, yy, x1, yy), fill=GRID, width=2)
        label(draw, (x0-12, yy), f"{val:g}", 22, MUTED, anchor="rm")
    draw.line((x0, y0, x0, y1-15), fill=MUTED, width=2)
    arrow(draw, (x0, y0), (x1+27, y0), MUTED, 2)
    label(draw, (x0, y0+25), "π/6", 23)
    label(draw, (x1, y0+25), "π/4", 23)
    label(draw, (x1+46, y0+6), "u", 25, bold=True)
    label(draw, (x0-4, 42), "|1 + τ|²", 26, OCHRE, bold=True, anchor="lm")
    curve = [graph(U_MIN+j*(U_MAX-U_MIN)/128) for j in range(129)]
    draw.line(curve, fill=OCHRE, width=4)
    xx, yy = graph(u)
    draw.line((xx, y0, xx, yy), fill=TEAL, width=2)
    dot(draw, (xx, yy), 11, OCHRE)
    dot(draw, (xx, yy), 4, PAPER)
    label(draw, (841, 425), f"u = {u:.3f}     |1 + τ|² = {abs(1+tau)**2:.3f}", 22)
    return image


def prime_weights():
    image, draw = page(1120, 370)
    cols = (378, 570, 762, 954)
    label(draw, (132, 47), "p ↓", 29, bold=True)
    label(draw, (242, 47), "j →", 27, MUTED, bold=True)
    for j, xx in enumerate(cols, 1):
        label(draw, (xx, 47), str(j), 27, bold=True)
    for row, prime in enumerate((2, 3, 7)):
        yy = 107 + row*78
        chi = {2:-1, 0:0, 1:1}[prime % 3]
        label(draw, (132, yy), str(prime), 32, bold=True)
        for exponent, xx in enumerate(cols, 1):
            weight = 1 + chi**exponent
            fill, ink = [(PAPER, MUTED), (PALE_OCHRE, OCHRE), (PALE_TEAL, TEAL)][weight]
            draw.rounded_rectangle((xx-75, yy-30, xx+75, yy+30), radius=8,
                                   outline=GRID, fill=fill, width=2)
            label(draw, (xx, yy), str(weight), 33, ink, bold=True)
    draw.line((82, 307, 1036, 307), fill=GRID, width=2)
    label(draw, (559, 338), "1 + χ₋₃(p)ʲ", 27)
    image.save(OUT / "lattice-prime-weights.png", optimize=True)


def symbol(value, prime):
    residue = pow(value % prime, (prime-1)//2, prime)
    return -1 if residue == prime-1 else residue


def gaussian_sign(x, y):
    prime = x*x + y*y
    t = (-x*pow(y, -1, prime)) % prime
    return symbol(DELTA[0] + DELTA[1]*t, prime)


def signed_point(draw, position, sign, color, radius=12, ink=PAPER):
    dot(draw, position, radius, color)
    x, y = position
    draw.line((x-5, y, x+5, y), fill=ink, width=2)
    if sign > 0:
        draw.line((x, y-5, x, y+5), fill=ink, width=2)


def prime_directions():
    pairs = [((3, 2), (2, 3)), ((6, 1), (1, 6)), ((8, 3), (3, 8))]
    assert [[gaussian_sign(*v) for v in pair] for pair in pairs] == [[-1,-1],[1,1],[1,-1]]
    frames = []
    for active in pairs:
        p = sum(a*a for a in active[0])
        image, draw = page(1120, 456)
        cx, cy, scale = 68, 385, 35

        def pos(x, y):
            return cx + scale*x, cy - scale*y

        for j in range(10):
            draw.line((pos(j, 0), pos(j, 9)), fill=GRID, width=1)
            draw.line((pos(0, j), pos(9, j)), fill=GRID, width=1)
        arrow(draw, pos(0,0), pos(9.7,0), MUTED, 2)
        arrow(draw, pos(0,0), pos(0,9.7), MUTED, 2)
        for j in (0,3,6,9):
            label(draw, (pos(j,0)[0], cy+19), str(j), 19, MUTED)
            if j:
                label(draw, (cx-11, pos(0,j)[1]), str(j), 19, MUTED, anchor="rm")
        label(draw, (419, cy+2), "ℜ z", 23, anchor="lm")
        label(draw, (68, 27), "ℑ z", 23)
        label(draw, (294, 32), f"|z|² = {p}", 27, bold=True)
        ring = [pos(sqrt(p)*cos(k*pi/192), sqrt(p)*sin(k*pi/192)) for k in range(97)]
        draw.line(ring, fill=MUTED, width=2)
        for (x,y), color in zip(active, (TEAL,OCHRE)):
            xy = pos(x,y)
            arrow(draw, pos(0,0), xy, color, 4)
            signed_point(draw, xy, gaussian_sign(x,y), color)
            label(draw, (xy[0]+8, xy[1]-23), f"{x} + {y}i", 23, color, bold=True, anchor="lm")
        draw.line((518, 33, 518, 417), fill=GRID, width=2)

        left, right, top, bottom = 610, 1041, 92, 337
        for fraction, name in zip((0,.25,.5,.75,1), ("0","π/8","π/4","3π/8","π/2")):
            xx = left+(right-left)*fraction
            draw.line((xx, top-10, xx, bottom+17), fill=GRID, width=1)
            label(draw, (xx, bottom+40), name, 20, MUTED)
        arrow(draw, (left,bottom+16), (right+19,bottom+16), MUTED, 2)
        label(draw, (1030, bottom+76), "θ = arg z", 23)
        label(draw, (left-6, 43), "p", 28, bold=True)
        for pair in pairs:
            q = sum(v*v for v in pair[0])
            yy = bottom-(q-13)/(73-13)*(bottom-top)
            draw.line((left, yy, right, yy), fill=(MUTED if pair==active else GRID), width=2)
            label(draw,(left-15,yy),str(q),24,INK if pair==active else MUTED,
                  bold=pair==active,anchor="rm")
            for (x,y),color,pale in zip(pair,(TEAL,OCHRE),(PALE_TEAL,PALE_OCHRE)):
                xx=left+(right-left)*atan2(y,x)/(pi/2)
                if pair == active:
                    signed_point(draw,(xx,yy),gaussian_sign(x,y),color,14)
                else:
                    signed_point(draw,(xx,yy),gaussian_sign(x,y),pale,10,ink=MUTED)
        frames.append(image)
    frames[-1].save(OUT / "direction-marked-primes.png", optimize=True)
    save_animation(frames, [2700,2700,4200], "direction-marked-primes.gif")


def legendre_header(draw, x, y, p):
    label(draw,(x,y-13),"z",19)
    denominator=f"{p:,}".replace(","," ")
    label(draw,(x,y+15),denominator,16)
    half=draw.textlength(denominator,font=font(16))/2+3
    label(draw,(x-half-8,y),"(",39)
    label(draw,(x+half+8,y),")",39)
    draw.line((x-half,y+1,x+half,y+1),fill=INK,width=1)


def same_ray():
    image,draw = page(1120, 371)
    y,origin,scale=75,75,12.6
    arrow(draw,(origin,y),(1040,y),MUTED)
    for z in (0,20,40,60):
        xx=origin+z*scale
        draw.line((xx,y-5,xx,y+5),fill=MUTED,width=2)
        label(draw,(xx,y+23),str(z),19,MUTED)
    for z,color in ((1,TEAL),(73,OCHRE)):
        xx=origin+z*scale
        dot(draw,(xx,y),8,color)
        label(draw,(xx,y-30),str(z),27,color,bold=True)
    label(draw,(550,37),"arg z = 0",25)
    label(draw,(1071,y),"ℜ z",22)
    draw.line((51,123,1069,123),fill=GRID,width=2)
    cols=(337,540,756)
    label(draw,(128,177),"z",30,bold=True)
    for xx,p in zip(cols,CONDUCTOR):
        legendre_header(draw,xx,178,p)
    label(draw,(956,177),"η",27,bold=True)
    label(draw,(973,189),"δ",17)
    label(draw,(1006,177),"((z))",27,bold=True)
    for row,(z,color) in enumerate(((1,TEAL),(73,OCHRE))):
        yy=246+row*68
        vals=[symbol(z,p) for p in CONDUCTOR]
        label(draw,(128,yy),str(z),31,color,bold=True)
        for xx,value in zip(cols,vals):
            label(draw,(xx,yy),"+1" if value==1 else "−1",29)
        value=vals[0]*vals[1]*vals[2]
        draw.rounded_rectangle((929,yy-25,1049,yy+25),radius=7,
                               fill=PALE_TEAL if row==0 else PALE_OCHRE)
        label(draw,(989,yy),"+1" if value==1 else "−1",30,color,bold=True)
    image.save(OUT/"direction-same-ray.png", optimize=True)


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True, parents=True)
    angles=[U_MIN+j*(U_MAX-U_MIN)/16 for j in range(17)]
    frames=[lattice_frame(u) for u in angles]
    frames[0].save(OUT/"lattice-ordered-ratio.png", optimize=True)
    save_animation(frames+frames[-2:0:-1], [1700]+[80]*15+[1700]+[80]*15,
                   "lattice-ordered-ratio.gif")
    prime_weights()
    prime_directions()
    same_ray()
