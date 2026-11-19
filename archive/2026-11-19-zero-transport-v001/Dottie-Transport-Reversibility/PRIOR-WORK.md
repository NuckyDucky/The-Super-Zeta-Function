# Which turns already appear in the literature?

McPhedran, Botten and Nicorovici plotted four consecutive legs of my early chain in 2007. I identified the matching figures by starting from each of their five published seeds and following its zero through both of my endpoint parameters with directed arithmetic. Figure 4 is particularly easy to misread. Its caption names the fifth Riemann zero at the paper's starting parameter. The piece of that figure from my $60^\circ$ to $45^\circ$ is the turn from the **second** Riemann zero to the **third**. [Original paper, §3 and figures 2–4](https://doi.org/10.1098/rspa.2006.1763) · [Author's full text](https://www.researchgate.net/publication/243685067_Null_trajectories_for_the_symmetrized_Hurwitz_zeta_function) · [Figure 4](https://www.researchgate.net/figure/The-null-trajectory-of-z-C-starting-at-the-fifth-zero-of-zs_fig5_243685067)

## Read the same curves in both conventions

The 2007 paper uses the sum $\zeta_+(w,a)=\zeta(w,a)+\zeta(w,1-a)$. My arithmetic reference is $\pi^{-w}\zeta_+(w,b)$. The factor is everywhere nonzero, and the sum is unchanged by $a=1-b$. The paper's complex variable is my Riemann coordinate $w=2s$. In its parameter, $a=1/2+\theta/\pi$, so the paper travels through $1/2,3/4,5/6$ in that order. My clockwise turn runs from $5/6$ back to $3/4$. For a simple zero the common differential equation is $dw/da=-(\partial_a\zeta_+)/(\partial_w\zeta_+)$. Their equations (3.4)–(3.6) already give the possible zero addresses at the rational parameters. Their equations (3.21)–(3.23) compare *counts* of crossings in height intervals. [McPhedran, Botten and Nicorovici, §3](https://www.researchgate.net/publication/243685067_Null_trajectories_for_the_symmetrized_Hurwitz_zeta_function)

Here $\rho_j$ is ordinary Riemann zero number $j$ in increasing positive height. Read the last two address columns **left to right** for the clockwise turn. The paper identifies the five starting ordinals in its captions. I assigned the middle and right columns by the calculation linked in each row.

| Historical figure | Published seed at $a=1/2$ | My launch at $a=5/6$ | My landing at $a=3/4$ | Directed replay |
| --- | --- | --- | --- | --- |
| 2(a) | $\rho_1$ | $2\pi i/\log 3$ | $2\pi i/\log 2$ | [Record](historical-figure-1.json) |
| 2(b) | $\rho_2$ | $4\pi i/\log 3$ | $\rho_1$ | [Record](historical-figure-2.json) |
| 3(a) | $\rho_3$ | $\rho_1$ | $4\pi i/\log 2$ | [Record](historical-figure-3.json) |
| 3(b) | $\rho_4$ | $4\pi i/\log 2$ | $\rho_2$ | [Record](historical-figure-4.json) |
| 4 | $\rho_5$ | $\rho_2$ | $\rho_3$ | [Record](historical-figure-5.json) |

I used the named historical ordinal as input to FLINT, a 192-bit working precision and overlapping contracting disks over every parameter interval. At each rational shift a common isolating disk of radius $10^{-8}$ identified the endpoint with an ordinary zero or an exact elementary address. The historical comparison is retrospective. To reproduce one row, run the Python verifier with the corresponding ordinal from 1 through 5, using python-flint 0.9.0 and the adjacent Dottie-Off-Axis-Return directory. [Verifier](compare_figures.py)

## What other authors established

- **Exact endpoint algebra.** McPhedran, Botten, Nicorovici and Zucker's companion paper gives the rational-shift evaluations in equations (6.3), (7.2) and (9.3). At $a=3/4$ the factors are $2^w(2^w-1)\zeta(w)$, and at $a=5/6$ they are $(3^w-1)(2^w-1)\zeta(w)$. This identifies the common addresses available for resetting. A zero's trajectory between them still has to be followed. [Companion paper](https://doi.org/10.1098/rspa.2006.1762)
- **Escape at the quarter shift.** Figures 6–7 of the trajectory paper follow four dyadic starts at $a=1/2$ toward $\Re w=-\infty$ from $a<3/4$. The recorded $6\pi i/\log3$ trial approaches $3/4$ from $a>3/4$. Takashi Nakamura treats the same plus family using my smaller shift $b$. Propositions 4.6–4.7 and equation (4.22) give a real root with $\beta_Z(b)=1+\log(\cos 2\pi b)/\log 2+O(\cos 2\pi b)$ as $b$ approaches $1/4$ from below. This gives a published instance of escape on our side of the endpoint, at imaginary part zero. [Historical trajectories, §3](https://doi.org/10.1098/rspa.2006.1763) · [Nakamura, primary text](https://arxiv.org/pdf/1910.10430) · [Published article](https://doi.org/10.1216/rmj.2023.53.157)
- **Classifying Riemann zeros by where they travel.** Ramūnas Garunkštis and Jörn Steuding continued the zeros of the single Hurwitz function $\zeta(w,\alpha)$ from $\alpha=1$ to $1/2$, where $(2^w-1)\zeta(w)$ supplies the two endpoint types. Section 2 and figure 1 classify starting zeros by the type reached, report the first 501 ordinals and describe reversing the initial conditions as a numerical check. The single Hurwitz summand gives a different continuation from the paired sum studied here. [Garunkštis and Steuding, §2](https://journals.vilniustech.lt/index.php/MMA/article/download/5510/4778)

## Where the present evidence adds detail

My reset takes the numerical address at $45^\circ$, restores the parameter to $60^\circ$, and follows the next trajectory from that same address. Thus consecutive steps can lie on **different** historical curves. On the blue turn from $\rho_4$ to $8\pi i/\log 2$, three separately certified interior crossings of $\Re w=1/2$ occur. This arc has different endpoints from every row above. The historical rational-shift formulas do not list its crossing angles. The reverse runs for $\rho_5$ and $\rho_6$ identify two triadic inputs, $10\pi i/\log 3$ and $12\pi i/\log 3$, that cannot themselves occur as finite reset outputs. [Three crossing enclosures](blue-crossings.json) · [Inverse runs and exclusion proof](README.md)

The sources above establish precedence for the family, the simple-zero continuation equation, elementary-to-Riemann connections and several of the **particular** turns. In these papers I found no iteration of this exact reset rule, no table of the blue branch's three crossings, and no identification of both missing predecessors with their finite-reset exclusion. Priority for those narrower results remains open.
