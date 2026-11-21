"""Plot the full prime windows and their retained area. Requires python-flint and Pillow."""

from math import log2
from pathlib import Path

from flint import arb, ctx
from PIL import Image, ImageDraw, ImageFont

from prime_windows import coefficients, knot_values, last_obstruction, positive_integral


BG = "#faf9f5"
INK = "#183947"
SUB = "#455e66"
GRID = "#d1d9d8"
AREA = "#086f78"
FILL = "#c8e2de"
THIRTY_SECOND = "#6b4c87"
EIGHTH = "#a94918"
LEFT, RIGHT = 92, 882
SIZE = (920, 1125)


def collect():
    ctx.prec = 192
    starts, end = (1024, 2048, 4096), 2**24
    samples = sorted({round(2**(12 + 12*k/800)) for k in range(801)})
    data = coefficients(end)
    knots = set(starts) | {64, *(y*y for y in starts)} | set(data) | set(samples)
    knots.update(2*n for n in data if 2*n <= end)
    knots = sorted(knots)
    wanted = set(samples) | set(starts) | {y*y for y in starts}
    cumulative = arb(0)
    previous, u = None, None
    table = {}
    for x, v in knot_values(data, knots):
        if previous is not None and previous >= 64:
            cumulative += positive_integral(previous, x, u, v)
        if x in wanted:
            table[x] = cumulative
        previous, u = x, v
    full = [(y, float(table[y*y]-table[y])) for y in starts]
    part = [(y, float(table[end]-table[y])) for y in samples]
    cross = {j: last_obstruction(data, knots, table[end], max(starts), j) for j in (8, 32)}
    return full, part, cross


def font(size, bold=False):
    # Both flags have a scalable bundled fallback in recent versions of Pillow.
    names = ("DejaVuSans-Bold.ttf", "segoeuib.ttf", "Arial Bold.ttf") if bold else (
        "DejaVuSans.ttf", "segoeui.ttf", "Arial.ttf")
    for name in names:
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            pass
    return ImageFont.load_default(size=size)


def dashed(draw, points, color, on, off):
    """Dash a polyline by physical length, regardless of the number of sampled points."""
    distance = 0.0
    for p, q in zip(points, points[1:]):
        dx, dy = q[0]-p[0], q[1]-p[1]
        length = (dx*dx+dy*dy)**0.5
        used = 0.0
        while used < length:
            phase = distance % (on+off)
            step = min(length-used, (on if phase < on else on+off)-phase)
            if step < 1e-7:
                distance += 1e-6
                continue
            if phase < on:
                draw.line((p[0]+dx*used/length, p[1]+dy*used/length,
                           p[0]+dx*(used+step)/length, p[1]+dy*(used+step)/length),
                          fill=color, width=4)
            distance += step
            used += step


def main():
    full, part, cross = collect()
    img = Image.new("RGB", SIZE, BG)
    draw = ImageDraw.Draw(img)
    label, tick = font(29), font(26)

    def title(y, name, subtitle):
        draw.text((LEFT, y), name, font=font(35, True), fill=INK, anchor="la")
        draw.text((LEFT, y+46), subtitle, font=label, fill=SUB, anchor="la")

    def axes(top, bottom, ymax, yrange, xlo, xhi, xticks):
        def xx(x):
            return LEFT + (RIGHT-LEFT)*(log2(x)-xlo)/(xhi-xlo)

        def yy(v):
            return bottom-(bottom-top)*v/ymax

        for y in yrange:
            draw.line((LEFT, yy(y), RIGHT, yy(y)), fill=GRID, width=2)
            draw.text((LEFT-16, yy(y)), str(y), font=tick, fill=SUB, anchor="rm")
        for x, text in xticks:
            draw.line((xx(x), bottom, xx(x), bottom+7), fill=INK, width=2)
            draw.text((xx(x), bottom+13), text, font=tick, fill=INK, anchor="mt")
        draw.line((LEFT, top, LEFT, bottom, RIGHT, bottom), fill=INK, width=2)
        return xx, yy

    def thresholds(xx, yy, low, high):
        xs = [2**(low+(high-low)*k/400) for k in range(401)]
        for j, color, on, off in [(32, THIRTY_SECOND, 5, 7), (8, EIGHTH, 17, 7)]:
            points = [(xx(x), yy(x**(1/j))) for x in xs]
            dashed(draw, points, color, on, off)

    # The same color and dash pattern denote the same threshold in both panels.
    for x, j, color, on, off in [(LEFT, "1/32", THIRTY_SECOND, 5, 7),
                                  (370, "1/8", EIGHTH, 17, 7)]:
        dashed(draw, [(x, 38), (x+56, 38)], color, on, off)
        draw.text((x+65, 40), "Y", font=label, fill=INK, anchor="lm")
        draw.text((x+83, 28), j, font=font(21), fill=INK, anchor="lm")

    title(83, "Full window  A(Y)", "Weighted positive area from Y to Y²")
    xx, yy = axes(204, 470, 4, range(5), 9.9, 12.1,
                  [(1024, "1,024"), (2048, "2,048"), (4096, "4,096")])
    thresholds(xx, yy, 10, 12)
    for x, a in full:
        px, py = xx(x), yy(a)
        draw.line((px, yy(0)-1, px, py), fill=AREA, width=5)
        draw.ellipse((px-8, py-8, px+8, py+8), fill=AREA)
        # Put the rightmost label above and slightly to the left.
        if x == 4096:
            draw.text((px-10, py-8), f"{a:.3f}", font=label, fill=AREA,
                      anchor="rs", stroke_width=3, stroke_fill=BG)
        else:
            draw.text((px+15, py-8), f"{a:.3f}", font=label, fill=AREA,
                      anchor="ls", stroke_width=3, stroke_fill=BG)
    draw.text(((LEFT+RIGHT)/2, 526), "Window start Y", font=label, fill=INK, anchor="mt")

    title(599, "Measured part  B(Y)", "Weighted positive area from Y to 2²⁴")
    xx, yy = axes(724, 1000, 8, [0, 2, 4, 6, 8], 12, 24,
                  [(2**12, "2¹²"), (2**15, "2¹⁵"), (2**18, "2¹⁸"),
                   (2**21, "2²¹"), (2**24, "2²⁴")])
    curve = [(xx(x), yy(a)) for x, a in part]
    draw.polygon([(LEFT, yy(0)-2), *curve, (RIGHT, yy(0)-2)], fill=FILL)
    for v in [2, 4, 6, 8]:
        draw.line((LEFT, yy(v), RIGHT, yy(v)), fill=GRID, width=2)
    draw.line(curve, fill=AREA, width=5)
    thresholds(xx, yy, 12, 24)
    for j, color, xshift, yshift in [(8, EIGHTH, 28, -72),
                                     (32, THIRTY_SECOND, -20, -75)]:
        last, following = cross[j]
        px = xx((last+following)/2)
        py = yy(((last+following)/2)**(1/j))
        dx, dy = px+xshift, py+yshift
        draw.line((px, py, dx, dy+9), fill=color, width=3)
        draw.ellipse((px-7, py-7, px+7, py+7), fill=BG, outline=color, width=4)
        draw.text((dx, dy), f"{last:,}", font=label, fill=color, anchor="ms",
                  stroke_width=3, stroke_fill=BG)
    draw.text(((LEFT+RIGHT)/2, 1060), "Window start Y  (log scale)", font=label,
              fill=INK, anchor="mt")
    target = Path(__file__).with_name("positive-area.png")
    img.save(target, optimize=True)


if __name__ == "__main__":
    main()
