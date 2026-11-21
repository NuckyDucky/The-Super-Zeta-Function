"""Plot H_2/sqrt(X) against log X. The highlighted area is the window integral."""
from collections import defaultdict
from math import log
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw, ImageFont

from windows.prime_windows import coefficients


def main():
    stop = 2**22
    events = defaultdict(float)
    for n, (q, trace) in coefficients(stop).items():
        value = trace * log(q) / n
        events[n] -= value
        if n * 2 <= stop:
            events[2*n] += value
    for n in (64, 2048, 65536, stop):
        events.setdefault(n, 0.0)
    x = np.array(sorted(events), dtype=int)
    slope = np.cumsum([events[n] for n in x])
    h = np.r_[0, np.cumsum(np.diff(x) * slope[:-1])]
    valid = x >= 2048
    x, y = x[valid], h[valid]/np.sqrt(x[valid])
    image = Image.new("RGB", (1450, 510), "#faf9f5")
    draw = ImageDraw.Draw(image)
    try:
        font = ImageFont.truetype("DejaVuSans.ttf", 25)
        bold = ImageFont.truetype("DejaVuSans-Bold.ttf", 27)
    except OSError:
        font = ImageFont.load_default(size=25)
        bold = ImageFont.load_default(size=27)
    left, right, top, bottom = 102, 1405, 52, 410
    def px(n):
        return left + (right-left)*log(n/2048)/log(stop/2048)
    def py(v):
        return top + (bottom-top)*(3.5-v)/10
    pts = [(px(n), py(v)) for n,v in zip(x,y)]
    ink = "#184d60"
    draw.polygon([(left,py(0))] + [(a,min(b,py(0))) for a,b in pts]
                 + [(right,py(0))], fill="#edb16b")
    for value in (-6,-4,-2,0,2):
        draw.line((left,py(value),right,py(value)),fill="#aaa9a6" if value==0 else "#ddddd9",width=1)
        draw.text((left-12,py(value)), str(value), fill=ink, anchor="rm",font=font)
    draw.line(pts, fill=ink, width=3)
    crossing = 735466.5734173918
    xx, yy = px(crossing), py(0)
    draw.ellipse((xx-5,yy-5,xx+5,yy+5),fill="#743c23")
    draw.line((xx,yy-4,xx-27,yy-59),fill="#743c23",width=2)
    draw.text((xx-29,yy-62),"735,466.57",anchor="ms",fill="#743c23",font=font)
    for e, label in [(11,"2¹¹"),(13,"2¹³"),(15,"2¹⁵"),(17,"2¹⁷"),(19,"2¹⁹"),(22,"2²²")]:
        draw.text((px(2**e),bottom+8),label,anchor="mt",fill=ink,font=font)
    draw.text((left,10),"H₂(X) / √X",fill=ink,font=bold)
    draw.text(((left+right)/2,461),"Prime-power cutoff X (logarithmic scale)",anchor="mt",fill=ink,font=font)
    image.save(Path(__file__).with_name("signed-window.png"))


if __name__ == "__main__":
    main()
