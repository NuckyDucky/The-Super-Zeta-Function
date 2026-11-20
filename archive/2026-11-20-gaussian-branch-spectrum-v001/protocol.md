# Hidden conjugate-branch trial

I use the two Gaussian branches of my quartic, named by the sign in $A\pm2iN$, with $A=N-D$. My ordered ratio $U/V=i$ fixes the positive imaginary direction in the marked basis $(1,i)$. The decoder receives the angular intervals and ordinary coefficients in two anonymous packets. Norm 17 calibrates the decision rule for the two known models. I check the signs at 73 after the calls. The commitment binds the archived labels to the nonce. The protocol and the completed trial are deposited together.

**Frozen decision rule.** For either angular reading supplied as an interval, a strictly positive lower endpoint selects A+2iN, a strictly negative upper endpoint selects A−2iN, and any interval containing zero is unresolved. The two real scalings, 17⁸ and 17¹⁶, are positive and do not change this decision. The unmarked norm spectrum admits both labels. The calibration is the exact arithmetic at norm 17 derived from the original six coefficients. Norm 73 is used only in the reveal. The proofs in the accompanying note specify the full infinite-series and completed-zero-moment tail bounds.

**Budget.** Generate all ideal shells through norm 33 for the ordinary and angular Dirichlet readings. For the zero moment use all nonreal Euler contributions through that same cutoff. Bound the entire infinite remainder in both cases. Randomly permute the two hidden inputs and commit to the permutation with a salted SHA-256 digest. The decoder receives only the anonymized input file. Perform the reveal with the original polynomial at 13, 37, and 73, compare it with the conductor character, and keep both outcomes. A disagreement or unresolved interval counts as such. The separate evaluation at w=2 is a precision cross-check.

**Replay.** From this directory run the following using standard-library Python. The checked-in trial can be verified directly; use an empty directory for a fresh random permutation.

~~~sh
python branch_test.py verify
python branch_test.py prepare --folder new-trial
python branch_test.py decode --folder new-trial
python branch_test.py verify --folder new-trial
~~~
