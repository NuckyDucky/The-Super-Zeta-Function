# The primitive sign and the two ordered readings

**November 22, 2026. First deposit.** At the super-zeta address of a right-ring input, exchange the two Hamilton units on either side of the quaternion. The two readings recover the real and imaginary parts of the completed quartic Mellin integral. The positive Gauss amplitude for the character of conductor \(26{,}509{,}772{,}707{,}289\) fixes the theta reflection used in the proof.

**Formal proof.** [QuarticSignedOrders.lean](QuarticSignedOrders.lean) gives the same-input test for the fixed quartic. A zero requires the signed cosine and sine integrals to vanish together. The assertion that they never vanish together throughout the Dottie annulus is open in this deposit. The low-height side theorem explicitly takes its interval certificate as a hypothesis.

**Analytic control.** [OrderedSignControl.lean](OrderedSignControl.lean) gives three positive symmetric masses whose transform has the same positive reflection sign and exact zeros at a selected reflected pair. It tests which conclusions follow from reflection and distinguishable super-zeta addresses alone.

**Provenance.** The source of the root-number theorem is [Murphy's tagged sign proof](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/blob/v1.0.0/lean/gauss/GaussSign.lean#L281-L287). Its Lean 4.19 port, notices and application to the fixed character are in the [executable proof packet](../../lean-quartic-orders/README.md). The two entry modules here preserve the deposited Git contents. [source-inventory.json](source-inventory.json) records each proof input's repository path, Git blob identifier, SHA-256 and byte length. Any listed file can be recovered with `git cat-file blob <git_blob>`.

**Replay.** Run `python lean-quartic-orders/replay.py --fetch-cache` from the repository root to compile both entry modules and check their theorem dependencies with the pinned Lean 4.19.0 toolchain. Run `python tools/verify_archive.py` with Python 3.12 or later to verify the snapshot bytes.
