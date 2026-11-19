"""Anchor a Riemann ordinal at the 45 degree endpoint and follow its simple zero backward."""
import argparse
from pathlib import Path
import sys

from flint import acb, ctx

HERE = Path(__file__).resolve().parent
OUTPUTS = HERE.parents[1]
sys.path.insert(0, str(OUTPUTS / 'Dottie-Transport-Reversibility'))
from reverse import follow_from_box

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ordinal', type=int)
    n = parser.parse_args().ordinal
    ctx.prec, ctx.cap = 192, 3
    anchor = acb.zeta_zero(n)
    follow_from_box(anchor, f'FLINT acb.zeta_zero({n})', None,
                    HERE / f'backwards-{n}.json')
    print(f'Certified backward branch ending at zero {n}', flush=True)
