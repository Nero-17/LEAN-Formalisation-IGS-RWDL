# LEAN Formalisation — IGS / RWDL

Lean 4 development for *Iterated Graph Systems (I): random walks and diffusion limits* (arXiv:2603.13798).

**Full formalization of the paper is not complete.** This development includes unverified candidates. See [FORMALIZATION_AUDIT.md](FORMALIZATION_AUDIT.md) and the [per-source status](verification/20261013T084954Z/source-status.json) for the exact verification boundary.

## Verified progress

- Actual substituted graphs, resistance renormalization, metric completion, limiting measures, and deterministic measured GHP convergence, including the original unweighted graphs with their own diameter normalization. Their actual projection distortions tend uniformly to zero, and a single complete compact common ambient with all required isometric embeddings is constructed internally.
- The actual regular strongly local closed form, varying-space Mosco convergence, conservative self-adjoint closed L² semigroup, its generator identification, and actual finite operator limits.
- All-vertex sup convergence of the original continuous-time and discrete floor-clock semigroups, with de-Poissonization supplied internally. The actual native clock and floor index equal the manuscript clock 2*c*rho^n*|E(Xi^n)| for the same normalization witness.
- Full-sequence finite-horizon path weak convergence for arbitrary convergent moving starts, with continuous limiting paths; a global continuous-path probability family measurable in its starting point, identified with the same closed L² semigroup.
- The actual usual completed-filtration full future-path stopping identity, including the finite event of potentially infinite stopping times, and bounded Borel future conditional expectations are supplied internally. The conservative Hunt construction is verified and preserves the prior closed L² semigroup and global path family.
- Actual closed-domain Nash bounds, L¹ contraction, L¹–L² and L²–continuous smoothing, and compact smoothing. The same actual five-rule closed semigroup has a symmetric strictly positive mass-one heat kernel, jointly continuous in positive time and both spatial variables, with the global small-time bound and a valid clipped all-time bound. Strict positivity and time continuity are supplied internally.
- Actual finite-born point evaluations agree with all continuous closed-domain representatives. Actual harmonic cutoffs, closed-form energy bounds, and half-time Riesz identities give the finite-born two-sided small-time heat estimates and local spectral dimension. These consumers supply both diagonal bounds internally from the same actual compact smoothing construction.
- The actual primitive integer degree matrix has spectral radius greater than one, and the actual degree-to-mass comparison gives a strict spectral-radius gap. Actual address endpoint collars have summable logarithmic schedules and almost-everywhere eventual avoidance; recent endpoints have uniform degree bounds. The primitive condition is a standing model condition retained from the paper; the separate nu=1 extension is not certified by these consumers.
- Actual all-start native-floor displacement tails pass to the same continuous semigroup's distance-cutoff expectation. Compact half lifts give the inverse-ball heat lower bound at every small time in the paper's diameter-normalized metric. Both manuscript ball-volume assertions now hold at every small radius, in both native and explicitly diameter-normalized metrics: finite-born two-sided power bounds and physical almost-everywhere power lower / precise logarithmic upper bounds. The proofs use actual star masses, degree growth, completion geometry and Borel transfer. Continuous-path exit-time consumers remain under verification.
- The actual finite-trace energy domain has anchored Hilbert completeness, and every finite-energy skeleton function extends continuously to the metric completion. The extension operator is compact. From the original rules when rho>1, the completed resistance itself is a metric with the original topology, and its finite-vertex distances equal actual network resistance divided by rho^n. Complete actual resistance-form axioms, including the complete quotient by constants, are constructed internally; the original continuous energy domain equals the constructed closed domain. The resistance form is identified with the same original closed form and Hunt process. Exporting all earlier heat estimates for this same Brownian witness remains under verification.
- Actual continuous-path true ball-exit survival holds at every point and every small radius for the same native global probability family, in both native and diameter-normalized metrics. Finite prefix maximal tails, open-set weak convergence and global restriction identities are supplied internally; this is the entire path-prefix event, not a one-time cutoff expectation. The continuous mean-exit bound remains separate and incomplete.
- Corrected critical percolation rule coding and literal infinite source-cluster laws, resistance exponents, and the stated failure of deterministic normalization.

Generic criteria count as actual-model results only when their inputs are supplied internally. The three standard Lean logical axioms in printed audits are distinguished from unproved mathematical hypotheses.

## Remaining work

The actual continuous-path mean-exit bound including the supremum over starts in a ball, the final same-full-heat Brownian estimate export, and actual graph spectral bridges for manuscript examples remain incomplete. The nonprimitive degree-rate-one extension and final theorem-label scope audit also remain outstanding. The completed 805-module dependency check does not cover every subsequently accepted file; a larger current closure is still required. Random-cluster GHP and diffusion statements retain their original conjectural status.

## Manuscript and layout

The adopted manuscript is [paper-corrections/AIM.corrected.tex](paper-corrections/AIM.corrected.tex). It includes the approved green mean and arrow-orientation corrections and uses one orientation of an undirected simple rule graph.

- `section2-random-walks/`: graph, resistance, volume and walk estimates.
- `section3-diffusion/`: closed forms, operators, probabilities, paths and heat kernels.
- `section4-percolation/`: corrected rule coding and critical cluster laws.
- `verification/20261013T084954Z/`: portable source hashes, accepted logs, source status and verified targets.

## Verification

Pinned Lean **4.28.0**, mathlib **8f9d9cff6bd728b17a24e163c9402775d9e6a365**.

The completed shared-dependency batch contains **805 modules**, with unchanged checked sources. Subsequent independently accepted whole-file receipts are listed separately; inventories overlap and are not a completion percentage.

```sh
python verify_published_snapshot.py
```

This verifies exact source and log hashes and printed axiom audits; it is not a fresh Lean rebuild. To rebuild the recorded targets after installing the pinned toolchain and mathlib dependencies in `section3-diffusion`:

```sh
python verify_published_snapshot.py --rebuild --lean /absolute/path/to/lean
```

An unfiltered full-source build includes drafts and is not claimed to pass. Toolchains, dependency caches and compiled binaries are omitted. The earlier corpus used [Aristotle](https://aristotle.harmonic.fun); subsequent development uses Codex, with current parallel agents GPT-6.1 Sol / high.
