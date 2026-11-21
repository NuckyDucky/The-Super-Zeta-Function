"""Animate the measured period-640 angle and its two analytic spectral traces. Requires Pillow."""
import json
import math
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[2]
FIGURES = ROOT / "docs" / "figures"
DATA = ROOT / "archive/2026-11-19-oriented-return-v001/data/quarter_probe.json"
W, H, SCALE = 1056, 466, 2
PAPER, INK, MUTED = "#faf7ef", "#143640", "#415e62"
GRID, TEAL, RUST, GOLD = "#d5dcd5", "#006a74", "#ad471d", "#a97b27"
PIVOT = -math.pi / 2


def mid(ball):
    return float(ball.lstrip("[").split()[0])


def traces(theta):
    return tuple(2 / (1 - math.sin(theta + sign * math.pi / 6)) for sign in (1, -1))


def typeface(size, bold=False, serif=False):
    files = (["georgiab.ttf", "DejaVuSerif-Bold.ttf"] if serif else
             ["segoeuib.ttf", "DejaVuSans-Bold.ttf"] if bold else
             ["segoeui.ttf", "DejaVuSans.ttf"])
    for name in files:
        try:
            return ImageFont.truetype(name, size * SCALE)
        except OSError:
            continue
    raise RuntimeError("Install DejaVu Sans and Serif or the Segoe UI and Georgia fonts.")


def render(theta, start, end):
    im = Image.new("RGB", (W*SCALE, H*SCALE), PAPER)
    d = ImageDraw.Draw(im)
    def line(points, color, width=1):
        d.line([(round(x*SCALE), round(y*SCALE)) for x,y in points], fill=color,
               width=width*SCALE, joint="curve")
    def dot(x,y,r,color,shape="circle"):
        box = ((x-r)*SCALE, (y-r)*SCALE, (x+r)*SCALE, (y+r)*SCALE)
        (d.ellipse if shape == "circle" else d.rectangle)(box, fill=color)
    def label(x,y,value,size,color=INK,bold=False,serif=False,anchor="la"):
        d.text((x*SCALE,y*SCALE), value, fill=color, font=typeface(size,bold,serif), anchor=anchor)
    def dashed(a,b,color):
        x,y=a; dx,dy=b[0]-x,b[1]-y
        count=max(1, round(math.hypot(dx,dy)/8))
        for k in range(count):
            line([(x+dx*k/count,y+dy*k/count),(x+dx*(k+.5)/count,y+dy*(k+.5)/count)],color)
    label(36,22,"Turning the period-640 return by π/6",35,serif=True)
    label(38,74,"The same angle θ sets two reciprocal-root sums, measured at θ + π/6 and θ − π/6.",19)
    line([(36,113),(1020,113)],GRID)
    label(37,129,"Direction of the return",22,bold=True)
    label(494,129,"The two spectral readings",22,bold=True)
    cx,cy,rad=233,215,148
    def unit(t):
        return (cx+rad*math.cos(t),cy-rad*math.sin(t))
    arc=[unit(-math.pi*j/150) for j in range(151)]
    line(arc,GRID,2); line([unit(-math.pi),(cx,cy),unit(0)],GRID,2)
    for i in range(13):
        angle=-math.pi*i/12
        x,y=unit(angle)
        line([(x,y),(cx+(rad+5)*math.cos(angle),cy-(rad+5)*math.sin(angle))],MUTED)
    label(72,211,"−π",16,MUTED,anchor="ra");label(390,211,"0",16,MUTED)
    dashed((cx,cy),unit(PIVOT),GOLD)
    label(cx,380,"−π/2",17,MUTED,anchor="ma")
    line([unit(start+(end-start)*j/90) for j in range(91)],GOLD,4)
    for t in [start,end]:
        x,y=unit(t);dot(x,y,4,GOLD)
    tip=unit(theta);line([(cx,cy),tip],INK,4);dot(cx,cy,4,INK)
    dot(*tip,8,PAPER);dot(*tip,5,INK)
    low,hi=end-.021,start+.018
    def plot(t,val):
        return 571+(t-low)/(hi-low)*420,356-(val-.995)/.31*170
    for value in [1,1.1,1.2,1.3]:
        _,y=plot(low,value);line([(571,y),(997,y)],GRID)
        label(559,y,f"{value:.2f}",15,MUTED,anchor="rm")
    for t,mark in [(-2,"−2"),(-1.8,"−1.8"),(PIVOT,"−π/2"),(start,"θ₀")]:
        x,_=plot(t,1);dashed((x,185),(x,360),GOLD if t==PIVOT else GRID)
        label(x,367,mark,16,MUTED,anchor="ma")
    full=[end+(start-end)*i/180 for i in range(181)]
    for k,color,shape in [(0,TEAL,"circle"),(1,RUST,"square")]:
        line([plot(t,traces(t)[k]) for t in full],color,3)
        x,y=plot(theta,traces(theta)[k]);dot(x,y,9,PAPER,shape);dot(x,y,6,color,shape)
    label(777,390,"Return angle θ (radians)",16,MUTED,anchor="ma")
    line([(36,419),(1020,419)],GRID)
    label(39,428,f"θ = {theta:+.4f} rad".replace("-","−"),20,bold=True)
    for k,color,shape,x,mark in [(0,TEAL,"circle",573,"M+"),(1,RUST,"square",808,"M−")]:
        dot(x,445,5,color,shape)
        label(x+13,428,f"{mark}   {traces(theta)[k]:.4f}",20,color,True)
    return im.resize((W,H),Image.Resampling.LANCZOS)


def main():
    data=json.loads(DATA.read_text(encoding="utf-8"))
    start,end=(math.radians(mid(data[key]["angle_deg"])) for key in ("original","clockwise"))
    assert math.isclose(start-end,math.pi/6,abs_tol=1e-12)
    for angle,key in [(start,"original"),(end,"clockwise")]:
        assert all(abs(x-mid(data[key][label]))<1e-12
                   for x,label in zip(traces(angle),("trace_plus","trace_minus")))
    assert abs(traces(PIVOT)[0]-traces(PIVOT)[1])<1e-13
    FIGURES.mkdir(parents=True,exist_ok=True)
    # Frame exactly at the tie, then visit the endpoint and retrace the same angles.
    angles=[start+(PIVOT-start)*j/7 for j in range(8)]
    angles.extend(PIVOT+(end-PIVOT)*j/25 for j in range(1,26))
    frames=[render(t,start,end) for t in angles]
    frames[0].save(FIGURES/"ordered-turn.png", optimize=True)
    order=list(range(len(angles)))+list(range(len(angles)-2,0,-1))
    palette=frames[0].quantize(colors=128)
    images=[frames[j].quantize(palette=palette,dither=Image.Dither.NONE) for j in order]
    durations=[1150 if j in (0,len(angles)-1) else 650 if j==7 else 90 for j in order]
    images[0].save(FIGURES/"ordered-turn.gif",save_all=True,append_images=images[1:],
                   duration=durations,loop=0,optimize=True,disposal=1)


if __name__=="__main__":
    main()
