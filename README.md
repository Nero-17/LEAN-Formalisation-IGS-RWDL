# LEAN Formalisation — IGS / RWDL

Lean 4 development for *Iterated Graph Systems (I): random walks and diffusion limits* (arXiv:2603.13798).

**This is an ongoing formalization snapshot. Full unconditional formalization of the paper is not complete.** Source files include unverified drafts; their presence is not a proof of their statements. The precise snapshot status is recorded in [FORMALIZATION_AUDIT.md](FORMALIZATION_AUDIT.md) and the [per-source manifest](verification/20261013T084954Z/source-status.json).

## Verified progress

- Actual substituted graph geometry, resistance renormalization, metric completion, limiting measures and deterministic measured GHP convergence.
- The actual regular strongly local closed form, varying-space Mosco convergence, conservative self-adjoint L² semigroup, and actual finite operator limits.
- Finite-horizon path tightness and existence of subsequential weak limits with almost surely continuous paths, for arbitrary initial probability families.
- A strongly continuous contraction Markov semigroup on continuous functions, identified with the same closed L² semigroup; full-point, all-real-time Markov kernels with joint weak probability continuity, Dirac at zero and Chapman–Kolmogorov identities.
- Full-sequence, all-vertex sup-norm convergence of the actual finite continuous-time semigroups, and genuine single-floor / absolute-floor de-Poissonization error bounds.
- Corrected critical percolation rule coding, nested process laws, resistance exponents, and the stated failure of deterministic normalization.

Each result retains its stated model conditions. General conditional lemmas are not counted as concrete conclusions until their inputs are supplied internally.

## Remaining work

The original discrete sup convergence revision, moving-start product observations, complete path-limit identification, global continuous process/Hunt/strong Markov properties, and the heat-kernel construction and estimates remain unfinished. Nash and heat-kernel development files are pending verification. Random-cluster GHP and diffusion extensions retain the paper's conjectural status.

## Adopted manuscript and layout

The adopted manuscript is [paper-corrections/AIM.corrected.tex](paper-corrections/AIM.corrected.tex). It includes the user-approved green-rule corrections, arrow orientation corrections, and the restriction to one orientation of an undirected simple graph. The original manuscript and correction evidence are retained.

- `section2-random-walks/`: graph, resistance, volume, and walk estimates.
- `section3-diffusion/`: closed forms, operators, probabilities, paths, and heat-kernel development.
- `section4-percolation/`: corrected rule coding and critical cluster laws.
- `verification/20261013T084954Z/`: portable source hashes, selected receipts, audit logs, and verified targets.

## Verification

Pinned versions: Lean **4.28.0**, mathlib **8f9d9cff6bd728b17a24e163c9402775d9e6a365**.

The latest completed shared-dependency batch contains **545 modules**, with unchanged source hashes. Later accepted whole-file results are recorded separately. Accepted printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound` or a subset.

Check the published source and log hashes with Python:

```sh
python verify_published_snapshot.py
```

For a fresh selected-target kernel rebuild, first install the pinned toolchain and obtain mathlib's package/cache dependencies in `section3-diffusion`, then run:

```sh
python verify_published_snapshot.py --rebuild --lean /absolute/path/to/lean
```

`verify_full_paper.py` merges the three legacy `RequestProject` namespaces and compiles dependencies in order. An unfiltered full-source build also includes pending drafts and is not claimed to pass for this snapshot. `.olean` files and dependency/toolchain caches are not published.

The earlier proof corpus was produced with [Aristotle](https://aristotle.harmonic.fun). The subsequent development was conducted with Codex; the current parallel agents use GPT-6.1 Sol / high. Historical model labels in receipts identify earlier runs.
