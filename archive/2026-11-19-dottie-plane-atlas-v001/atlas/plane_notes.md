# Transport near the sixth zero

I followed each starting point on the level of the unweighted function

$$
H(w,b)=\zeta(w,b)+\zeta(w,1-b),\qquad b=\tfrac16+h/180 .
$$

Here $h$ counts clockwise degrees. The turn starts at the sixth path's last height minimum, $h=13.40917360918594\ldots$, and ends at $15$. The black curve follows the level $H=0$. Each surrounding point keeps its own complex value of $H$.

On any regular lifted path, differentiating $H(w_1,b_1)=H(w_0,b_0)$ in the starting point gives the complex derivative $H_w(w_0,b_0)/H_w(w_1,b_1)$. The length map colors the magnitude of this derivative. A ratio of $0.5$ halves the length of an initially short segment, and a ratio of $2$ doubles it. Area scales by the square of that ratio. The separate grid figure shows all 10,961 initial points and all 10,924 accepted endpoints with equal axis scales. Lines follow representative rows, columns and the source perimeter. The two colored trails follow A and B in the direction of the arrows. [Length map](plane_strain.png) · [Complete grid](plane_grid.png)

| Start | End, rounded | Local length ratio |
|---|---|---:|
| A, $0.075+36.75i$ | $0.796383+37.669472i$ | $0.286128734\pm0.000000001$ |
| B, $-0.525+37.3125i$ | $0.276424+37.035755i$ | $8.075195\pm0.000001$ |

I verified A and B independently with 192-bit complex ball arithmetic. Their nonzero levels are enclosed throughout 88 and 195 consecutive parameter intervals. In each interval a fixed complex Newton preconditioner maps a disk strictly inside itself and has Lipschitz constant below one. The incoming and outgoing small root disks both fit inside that disk. The derivative ratio then encloses the finite length change at the starting point. These certificates cover the published uncertainty in the trough angle and its rounded value used for the raster. [Two directed certificates](plane_anchors.json)

The larger map uses fourth-order Runge–Kutta integration of $dw/dh=-H_b/(180H_w)$. I compared coarse and fine runs at every common node and checked the relative level residual $|H(w(h),b(h))-H(w_0,b_0)|/(1+|H(w_0,b_0)|)$ at every fine step. The printed map admits residuals below $5\times10^{-7}$ and path disagreements at most $2\times10^{-5}$. It also requires the sampled $|H_w|$ to exceed $10^{-4}$. Of 10,961 points, 10,924 passed. The length map shows 37 unresolved cells in gray. The grid view marks their starting positions in rust. Its final frame includes all accepted endpoints, from real part $-0.57800$ to $0.99325$. The length-map scale uses the same color for values above $8$. Its numerical extrema among the accepted points are $0.28613$ and $8.07519$ in length ratio. Numerical evaluation of $H,H_w,H_b$ uses 24 direct terms and 12 Euler–Maclaurin corrections per summand. Independent 160-bit FLINT evaluations check 28 accepted start/end pairs. [Numerical summary](plane_map.json) · [Portable checkpoint data](plane_reference.json)

From this directory, with Python 3.12, python-flint 0.9.0, NumPy 2.5.5 and matplotlib 3.11.2 installed:

```sh
python -B plane_map.py --output replay
python -B plane_anchors.py --output replay
```

The compressed NumPy array records the grid axes, endpoints, log length ratios, acceptance mask, residuals, step counts and marked paths. Use the mask when analyzing endpoints. The data describe this finite transport for the specified $H$ and interval of angles. Attraction under repeated return is a separate experiment.
