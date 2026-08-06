# IGS-RWDL-LEAN

Lean 4 formalisation accompanying the paper *Iterated Graph Systems (I): random walks and diffusion limits* (arXiv:2603.13798).

The formalisation follows one principle throughout: results the paper quotes from the literature enter as **explicit hypotheses**, and every argument the paper carries out itself is **proved**. All projects use Lean `v4.28.0`, each pinning its own revision of `mathlib`, and contain no `sorry`, no `admit` and no additional `axiom`; every formalised statement depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

### `section2-random-walks/` — Section 2
Resistance renormalisation, local mass and resistance dimensions, exit times, the Einstein relation. The exit-time lower bound is unconditional: the near-diagonal Green comparison and the volume-share input are proved from an oscillation-contraction machine built on the Dirichlet Green function. Lemma 2.14 is formalised in its trimmed form with the a0-shifted upper bound.

### `section3-diffusion/` — Section 3
Dirichlet forms and diffusion limits (3.1), the resistance-form Brownian motion (3.2), and the heat-kernel estimates (3.3). Every lemma, proposition, theorem, corollary and worked example is covered, except Lemma 3.1 and Theorem 3.13, which the paper quotes from the literature. Highlights: the oscillation contraction of Lemma 3.4 is proved from the standing assumptions; the sharpened logarithmic exponent of Lemma 3.19 is machine-checked, together with the strict comparison against the one-cell route; the watched-chain argument of Lemma 3.11 is formalised with an explicit jump-count constant; the two-colour spectral dimensions 1.1160 and 1.8877 are verified by interval arithmetic.

### `section4-percolation/` — Section 4
The quenched resistance exponent for the critical percolation cluster on the DHL. Proposition 4.2 is formalised as an equality of the **joint laws of the full resistance sequences**, via a single measure-preserving coarse-graining coupling at criticality; resistances are genuine Thomson effective resistances of the open cluster. The mean-matrix eigenvalues of Subsection 4.2 (a closed form for the Perron root of E(M), and the exact value 2 for E(N)) and the exponent 1.8993 are verified in `Outlook/`.

## Build

In each folder: `lake exe cache get && lake build`. Each folder documents its own precise scope: the correspondence tables in the Lean file headers, the `SECTION*_NOTES.md` and `FORMALIZATION.md` files where present, and the run-by-run log `ARISTOTLE_SUMMARY.md`; `ARISTOTLE.md` records tool credits.

Proofs were produced with [Aristotle](https://aristotle.harmonic.fun) by Harmonic.
