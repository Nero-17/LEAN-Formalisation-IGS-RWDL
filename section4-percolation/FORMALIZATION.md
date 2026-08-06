# Formalization of Subsection 4.1

This project formalizes the core analytic content of **Subsection 4.1** ("Solution to the open
problem in [hambly2010diffusion]") of *Iterated Graph Systems (I): random walks and diffusion
limits* (arXiv:2603.13798).

The mathematical object is the **reduced two-terminal resistance process** `(R_n)` on the diamond
hierarchical lattice. Starting from `R_0 = 1`, each step replaces every edge independently by

* a **series** of two i.i.d. copies, giving resistance `X + Y`, with probability `p_series`, or
* a **diamond** of four i.i.d. copies, giving resistance `par (X_1 + X_2) (X_3 + X_4)` where
  `par a b = a*b/(a+b)`, with probability `p_diamond`.

For `p ∈ (0,1)` the conditional probabilities are `p_diamond = p^2/(2-p^2)` and
`p_series = (2-2p^2)/(2-p^2)`, and the critical DHL parameter is `p_c = (√5-1)/2`.

As agreed in the request, the model is treated **directly via its distributional recursion**; the
EIGS / effective-resistance-on-random-graphs infrastructure (which is not in Mathlib) is **not**
rebuilt. Consequently the graph reduction proposition (`R_eff` of the percolation cluster `=d R_n`)
is out of scope.

The analytic argument needs two structural facts. The **uniform product-moment bound**
`E[R_n]·E[1/R_n] ≤ M` is now **verified directly from the distributional recursion** for the
concrete law `lawMeasure` (see `Moments.lean`), with the explicit constant `M = 11/5` valid in the
regime `p_diamond ≤ 1/2` (which contains the critical parameter, where `p_diamond = √5 - 2 < 1/2`).
It is therefore no longer an assumption. The **submultiplicativity of the means**
`E[R_{a+b}] ≤ E[R_a]·E[R_b]` is now **also verified directly for the concrete law** (see
`Submultiplicative.lean`, theorem `E1_submultiplicative`). The proof carries out exactly the
self-similar composition / concavity–Jensen argument over random series-parallel networks, but
entirely at the level of the distributional recursion (no effective-resistance graph theory is
required): see the dedicated section below.

## File structure (under `RequestProject/Reduced/`)

* `Params.lean` — the parameters `pdiamond`, `pseries`, `pc` and their algebra:
  `pseries + pdiamond = 1`, positivity, `pc^2 = 1 - pc`, `pdiamond pc = √5 - 2`,
  `pdiamond pc < 1/2`.
* `RealAux.lean` — the elementary real identities/inequalities used in the one-step computations:
  the diamond identity `par a b = (a+b)/4 - (a-b)^2/(4(a+b))`, the reciprocal identity
  `(x+y)⁻¹ = ¼(x⁻¹+y⁻¹) - ¼(x-y)²/(xy(x+y))`, `par a b ≤ √(ab)/2`, monotonicity of
  `x ↦ x - (x-1)²/(2x-1)` and `x ↦ x - (x-1)²/(3x-1)`, and the deterministic series/diamond bounds
  used to prove `1 ≤ R_n ≤ 2^n`.
* `Process.lean` — the **law** of `R_n` as a sequence of measures `lawMeasure pd ps n` defined by
  the distributional recursion. Proves each `lawMeasure pd ps n` is a probability measure
  (`isProb_lawMeasure`) supported on `[1, 2^n]` (`lawMeasure_support`).
* `Moments.lean` — the **moment computations** for the concrete law. Defines `E1 = E[R_n]`,
  `Einv = E[1/R_n]`, `E2 = E[R_n^2]`; proves the one-step moment recursions (`E1_succ`,
  `Einv_succ`, `E2_succ`), the diamond/parallel estimates (`Dmean_le_E1`, `Dsq_le_E1sq`,
  `Dmean_lower`), a reusable integral Cauchy–Schwarz (`integral_cauchy_schwarz_sq`), the
  relative-second-moment bound `E[R^2] ≤ 2·E[R]^2` (`E2_le_two_E1sq`), and finally the
  **uniform product-moment bound** `E[R_n]·E[1/R_n] ≤ 11/5` (`E1Einv_le`, packaged as
  `uniform_product`) for `p_diamond ≤ 1/2`.
* `Limit.lean` — the analytic heart.
* `Submultiplicative.lean` — the **concavity / Jensen argument** on random series-parallel
  networks, working with the laws directly: the generalised law `genLaw ν n` with an arbitrary
  leaf law `ν`, its composition identity `genLaw ν (a+b) = genLaw (genLaw ν b) a`, the
  increasing–concave order `IcvLEon` preserved by the one-step operator (`combineM_icv`,
  `genLaw_icv`), homogeneity (`mean_genLaw_dirac`) and Jensen (`jensen_le_dirac`), culminating in
  the **submultiplicativity of the mean** `E[R_{a+b}] ≤ E[R_a]·E[R_b]` (`E1_submultiplicative`).
* `Capstone.lean` — combines the two structural facts into the **unconditional annealed exponent**
  `reduced_annealed_exponent`.

## Main results (in `Limit.lean`)

* **`fekete_exponent`** — existence of the exponent (Lemma "annealed exponent"). If `m : ℕ → ℝ`
  is submultiplicative with `1 ≤ m n ≤ 2^n`, then `(log (m n))/n` converges to some
  `α ∈ [0, log 2]`. (Fekete's lemma.)

* **`quenched_ae`** — the almost-sure part of Theorem "reduced quenched exponent". For any process
  `R` on a probability space with `1 ≤ R n ≤ 2^n` and uniformly bounded product moments
  `E[R n]·E[1/R n] ≤ M`, if the annealed log-means `(E[log R n])/n` converge to `α`, then the
  quenched limit `(log R n)/n → α` holds almost surely. Proved from Jensen's inequality (for the
  exponential-moment bounds), Markov's inequality (for the concentration tail bound) and the
  Borel–Cantelli lemma.

* **`E1_submultiplicative`** (`Submultiplicative.lean`) — submultiplicativity of the mean reduced
  resistance `E[R_{a+b}] ≤ E[R_a]·E[R_b]`, proved via the concavity / Jensen argument on the
  random series-parallel network (no extra hypotheses beyond the parameter constraints).

* **`reduced_annealed_exponent`** (`Capstone.lean`) — the **unconditional annealed exponent**.
  Combining `1 ≤ E[R n] ≤ 2^n` with `E1_submultiplicative`, Fekete's lemma yields a deterministic
  `α ∈ [0, log 2]` with `(log E[R n])/n → α`, with no hypotheses beyond the parameter constraints.

* **`reduced_quenched_exponent`** — the capstone (Theorem "reduced quenched exponent"). For a
  process `R` with `1 ≤ R n ≤ 2^n`, uniformly bounded product moments (`hM`), and
  **submultiplicative means** (`hsub`, the self-similarity input), there is a deterministic
  `α ∈ [0, log 2]` such that, almost surely, `(log R n)/n → α`, and moreover the annealed exponents
  `(log E[R n])/n → α` and `(E[log R n])/n → α`. In particular the **quenched and annealed
  unit-resistance exponents coincide.**

All declarations are `sorry`-free and depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

## Verified moment bound (`Moments.lean`)

* **`uniform_product`** / **`E1Einv_le`** — for `0 ≤ p_diamond`, `0 ≤ p_series`,
  `p_series + p_diamond = 1` and `p_diamond ≤ 1/2`, every `n` satisfies
  `E[R_n]·E[1/R_n] ≤ 11/5`. This is the **uniform product-moment bound** `M`, now proved directly
  from the distributional recursion (Lemma 4.4 / 4.5 of the paper), so it is no longer a hypothesis.
  The proof is a coupled induction: the relative second moment stays `≤ 2` (`E2_le_two_E1sq`), and
  the product moment satisfies a logistic one-step contraction with fixed point below `11/5`.

## Uniform product-moment bound for all `p` (`Cases23.lean`)

`Moments.lean` proves Lemma 4.5 only in **Case 1** (`p_diamond ≤ 1/2`).  `Cases23.lean`
completes the other two regimes of the paper's Lemma 4.5, so the uniform product-moment bound
`E[R_n]·E[1/R_n] ≤ M(p)` now holds for **every** `p ∈ (0,1)`.

* **`uniform_product_case2`** — Case 2 (`1/2 ≤ p_diamond ≤ 1/√3`, stated as `1/2 ≤ pd` and
  `pd² ≤ 1/3`): again `E[R_n]·E[1/R_n] ≤ 11/5`.  The relative second moment now only stays `≤ 3`
  (`case2_inv`); proving this needs two extra Cauchy–Schwarz estimates over the four-fold product:
  `diamond_CS` (refined diamond second-moment estimate, giving
  `E[D²] ≤ E[R]² − (5/3)(E[R] − E[D])²`) and `harm_CS` (harmonic-mean estimate giving
  `E[D] ≥ (5/11)E[R]`).  These rest on the new integral identities `int_C_int`, `int_K_int`,
  `int_J_int`.
* **`uniform_product_case3`** — Case 3 (`p_diamond > 1/√3`, stated as `1/2 < pd`, `pd < 1`,
  `1/3 < pd²`): a finite uniform bound exists.  Here the relative second moment is controlled by
  `(2−pd)/(2pd−1)` (`E2_ratio_case3`) and the product moment obeys an affine recursion with
  contraction factor `(3/2)(1−pd²) < 1` (`affine_step`), so iteration gives a finite bound.
* **`uniform_product_lemma45`** — stitches Cases 1–3 together: for any `0 < pd < 1`, `ps ≥ 0`,
  `ps + pd = 1` (plus `hmono` in the `pd > 1/√3` regime) there is a finite `M` with
  `E[R_n]·E[1/R_n] ≤ M` for all `n`.

**Case 3 and the monotonicity input.** Case 3 of the paper uses the almost-sure monotonicity
`R_{n+1} ≥ R_n` of the resistance (graph-level Rayleigh monotonicity under the coupled iterated
construction).  In this purely distributional model there is no joint coupling, and mean
monotonicity is genuinely not a one-step consequence of the law recursion; it is therefore taken
as the explicit hypothesis `hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k+1)` — exactly the input the paper
derives from the graph construction.  Cases 1 and 2 use no such hypothesis.

## Positivity of the critical exponent (`Positivity.lean`)

This file formalizes the paper's proposition `α(p_c) > 0` (numbered Prop 4.7/4.8 depending on the
version).  Recall (`Capstone.lean`) that the annealed exponent `α = lim_n (log E[R_n])/n` exists.

* **`Dmean_ge_two_thirds`** — in the regime `p_diamond ≤ 1/2`, the diamond mean satisfies
  `E[D_n] ≥ (2/3) E[R_n]` (from `Dmean_lower` and the relative-second-moment bound
  `E[R_n²] ≤ 2 E[R_n]²`).
* **`E1_succ_ge`** — combined with the one-step recursion
  `E[R_{n+1}] = 2 p_series E[R_n] + p_diamond E[D_n]`, this gives the geometric one-step lower
  bound `E[R_{n+1}] ≥ (2 − (4/3) p_diamond) E[R_n]`.
* **`E1_ge_geom`** — iterating from `E[R_0] = 1`: `E[R_n] ≥ (2 − (4/3) p_diamond)^n`.
* **`annealed_exponent_ge_log`** — hence `α ≥ log (2 − (4/3) p_diamond)`.
* **`alpha_pc_pos`** — at the critical parameter `p_c` (where `p_diamond = √5 − 2`), the growth
  factor is `2 − (4/3) p_diamond = (14 − 4√5)/3 > 1`, so the annealed exponent satisfies
  `α(p_c) ≥ log ((14 − 4√5)/3) > 0`.  In particular `α(p_c) > 0`.

## No deterministic limit (`NoLimit.lean`)

This file formalizes the paper's proposition ruling out a non-zero deterministic limit: assuming
`p_series, p_diamond ∈ (0,1)`, for `λ > 0` and `Z_n = λ^n R_n`, if `Z_n` converges in distribution
to a deterministic constant `c ≥ 0` then `c = 0` (**`no_deterministic_limit`**).  Convergence in
distribution to `c` is modelled by its defining property `∫ f dν_n → f c` for every bounded
continuous `f` (where `ν_n = zMeasure pd ps lam n` is the law of `Z_n`).

The proof follows the paper at the level of the distributional recursion:

* **`zMeasure_succ_integral`** — the one-step recursion for the law of `Z_n` integrated against a
  bounded continuous `f`:
  `∫ f dν_{n+1} = p_series · ∫ f(λ(a+b)) d(ν_n ⊗ ν_n) + p_diamond · ∫ f(λ·diamond) d(ν_n^{⊗4})`
  (built from `prod_zMeasure_eq`, `prod4_zMeasure_eq`, the homogeneity `par_smul`, and the change
  of variables `integral_map`).
* **`series_limit`** — if `ν_n → δ_c` weakly then the series term tends to `f(2λc)` (continuous
  mapping theorem on the two-fold product, `weak2_int_tendsto`).
* **`diamond_limit`** — if `ν_n → δ_c` weakly with `c > 0` then the diamond term tends to `f(λc)`.
  Since the parallel map is singular at the origin, the genuine integrand is compared to a globally
  continuous truncation `diamondSafe` (which agrees with it where the coordinate sum is `≥ c`); the
  mismatch is controlled by a bump function (`exists_bump4`) whose mass tends to `0` by weak
  convergence (`weak4_int_tendsto`).
* **`limit_identity`** — combining the above with uniqueness of limits gives, for every bounded
  continuous `f`, `f c = p_series · f(2λc) + p_diamond · f(λc)`.
* **`no_deterministic_limit`** — choosing a tent function (`exists_tent`) equal to `1` at `c` and
  `0` at whichever of `2λc`, `λc` differs from `c` (one of them does, since `2λc ≠ λc` for
  `c > 0`, `exists_ne_of_pos`) contradicts `p_series, p_diamond > 0` unless `c = 0`.

The weak-convergence layer is built on Mathlib's `ProbabilityMeasure` weak topology
(`tendsto_iff_forall_integral_tendsto`, `continuous_prod`).

## Scope notes

* The graph-level reduction proposition (Proposition "dhl_reduction") is out of scope, as it
  requires effective-resistance / random-recursive-fractal infrastructure absent from Mathlib.
* The propositions `α(p_c) > 0` and "no deterministic limit" are now formalized, in
  `Positivity.lean` and `NoLimit.lean` respectively (see the two dedicated sections above).
* The **submultiplicativity of the means** `E[R_{a+b}] ≤ E[R_a]·E[R_b]` is **no longer an
  assumption**: it is proved as the theorem `E1_submultiplicative` (`Submultiplicative.lean`) by
  carrying out the self-similar composition / concavity–Jensen argument over random
  series-parallel networks entirely at the level of the distributional recursion. The abstract
  capstone `reduced_quenched_exponent` still *states* it as a hypothesis `hsub` because it is
  formulated for an arbitrary process `R` on an arbitrary probability space; for the concrete
  model that hypothesis is discharged by `E1_submultiplicative`, as witnessed unconditionally by
  `reduced_annealed_exponent` (`Capstone.lean`).
* The single joint probability space carrying the whole sequence `R_n` **is now constructed**
  (`JointSpace.lean`): the sample space is `Ω = ℝ^ℕ`, the law is the infinite product
  `P = ⨂ₙ μ_n` of the marginal laws `μ_n = lawMeasure pd ps n` (`jointMeasure`, via Mathlib's
  `Measure.infinitePi`), and `R_n = π_n` is the `n`-th coordinate projection (`proj`).  The
  marginal identity `(R_n)_* P = μ_n` (`jointMeasure_map_proj`) transfers the established marginal
  facts (bounds `1 ≤ R_n ≤ 2^n`, the product-moment bound `E[R_n]·E[1/R_n] ≤ 11/5`, and
  submultiplicativity) into the hypotheses `hge`, `hle`, `hM`, `hsub` of
  `reduced_quenched_exponent`.  This yields, for the concrete model in the regime `pd ≤ 1/2`
  (which contains `p_c`), the theorem `reduced_quenched_exponent_concrete`: there is a
  deterministic `α ∈ [0, log 2]` such that `P`-almost surely `(1/n) log R_n → α`.  (The
  everywhere bounds required by the abstract theorem are supplied via the clamped process
  `Rclamp`, which agrees with `π_n` `P`-almost surely, so the conclusion holds verbatim for the
  coordinate projections.)

* The concrete quenched-exponent theorem `reduced_quenched_exponent_concrete`
  (`JointSpace.lean`) now also **exposes the quenched = annealed equality**: alongside the
  almost-sure quenched limit it keeps the annealed component, rewritten through
  `integral_Rclamp` into `(1/n) log E[R_n] → α` with `E[R_n] = E1 pd ps n`.  Its regime is
  **widened from `pd ≤ 1/2` to `pd² ≤ 1/3`** (i.e. `pd ≤ 1/√3`) via the combined bound
  `E1Einv_le_of_sq` (`Cases23.lean`), which case-splits on `pd ≤ 1/2` (`E1Einv_le`) versus
  `1/2 < pd` (the `.2` projection of `case2_inv`) and uses neither the monotonicity hypothesis
  `hmono`; the critical point stays covered since `pdiamond pc < 1/2 ⟹ (pdiamond pc)² < 1/4 < 1/3`.
* The **headline theorem at the critical point** `reduced_exponent_critical` (`Critical.lean`)
  merges `reduced_quenched_exponent_concrete`, `reduced_annealed_exponent` and `alpha_pc_pos`,
  instantiated at `p_c`: with `P = jointMeasure (pdiamond pc) (pseries pc)` and `R_n = proj n`,
  there is a deterministic `α` with `0 < α ≤ log 2` and `log ((14 − 4√5)/3) ≤ α` such that
  `P`-almost surely `(1/n) log R_n → α` and simultaneously `(1/n) log E[R_n] → α`.  The two
  exponents are identified by uniqueness of limits (`tendsto_nhds_unique`), the annealed
  sequences from the concrete theorem and from `alpha_pc_pos` being identical.

All declarations are `sorry`-free and depend only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`.

## Proposition 4.2: the percolation cluster resistance (`RequestProject/Cluster/`)

The graph-level reduction proposition, listed above as out of scope, is now formalized: it is
**Proposition 4.2** of the paper.  Everything it needs — finite electrical networks, the Thomson
(minimal-energy) definition of two-terminal effective resistance, and the series/parallel laws —
is built from scratch in this project, since Mathlib does not provide it.

* `Cluster/Network.lean` — finite **two-terminal networks** `TTN` (a finite vertex set, a finite
  edge set with tail/head maps, and two distinct terminals `a ≠ b`, all edges of unit resistance).
  A `Flow t` is a real function on edges whose divergence is `t` at `a`, `−t` at `b` and `0`
  elsewhere; `energy` is the sum of squares, and

      effRes N = ⨅ {ENNReal.ofReal (energy f) | f a unit flow}   (`⊤` if no unit flow exists),

  the Thomson principle taken as the definition, valued in `ℝ≥0∞` so that a **disconnected** pair
  of terminals gets resistance `⊤`.  Proved here: the scaling law `flowRes t = t² · effRes`,
  `effRes_edge = 1` for a single edge, `effRes_gap = ⊤` for two isolated terminals, and the two
  structural laws

  * **`effRes_series`** — `effRes (N ⧺ M) = effRes N + effRes M`;
  * **`effRes_par`** — `effRes (N ∥ M) = (effRes N⁻¹ + effRes M⁻¹)⁻¹`,

  both valid in `ℝ≥0∞` including the degenerate (`⊤`) cases; in particular a dangling
  disconnected branch is automatically invisible to the effective resistance.

* `Cluster/DHL.lean` — **bond percolation on the diamond hierarchical lattice**.  A level-`n`
  configuration is `Conf n` (`Conf 0 = Bool`, `Conf (n+1) = Conf n ^ 4`), `net n c` is the network
  of open edges (a closed edge becomes a gap), and `res n c = (net n c).effRes` is the resistance
  of the open cluster between the two boundary vertices (`⊤` iff they are disconnected).  With the
  i.i.d. Bernoulli(`p`) measure `confMeasure p n` and `resLaw p n = (res n)_* confMeasure p n`,
  the two network laws give the distributional recursion

  * **`resLaw_succ`** — `resLaw p (n+1) = parLaw (sumLaw ρ ρ) (sumLaw ρ ρ)` with `ρ = resLaw p n`.

* `Cluster/Law.lean` — the notion of a **resistance law** `IsResLaw ρ m λ`: `ρ = m·δ_⊤ + (λ)_*ofReal`
  with `λ` a finite measure on the positive reals.  Computes the effect of the series and parallel
  combinations on such a law (**`IsResLaw.sum`**, **`IsResLaw.par`**), the mixed terms of the
  parallel rule being exactly the deletion of a dangling branch, plus the rearrangement
  **`par_series_prod`** identifying "parallel of two series pairs" with the fourfold `diamondMap`.

* `Cluster/Prop42.lean` — the critical computation.  From `p_c² = 1 − p_c` one gets
  **`pdiamond_pc_eq`** (`p_diamond = p_c³`) and **`pseries_pc_eq`** (`p_series = 2p_c²`), and then
  by induction on `n`

  * **`resLaw_isResLaw`** — `resLaw p_c n` is a resistance law with disconnection mass `1 − p_c`
    and finite part `p_c · lawMeasure (pdiamond p_c) (pseries p_c) n`;
  * **`prob_connected`** — the two boundary vertices are connected with probability exactly `p_c`
    at *every* level `n`;
  * **`cluster_resistance_law`** (**Proposition 4.2**) — conditionally on the two boundary vertices
    being connected, the effective resistance of the level-`n` critical percolation cluster has
    exactly the law `lawMeasure (pdiamond p_c) (pseries p_c) n` of the reduced resistance `R_n`.

All the resistances involved are genuine Thomson effective resistances of the open cluster, not a
hand-made recursion.

### Proposition 4.2 as an identity of *processes*

The paper phrases Proposition 4.2 as an identity of the whole processes
`(R_{⟨Ξⁿ₁⟩₁}(v₊,v₋))_{n≥0} =_d (R_n)_{n≥0}`, not just of the one-level marginals.  This is now
formalized as well, by constructing **one** coupling and checking its compatibility level by level
(rather than by patching marginals together).  Since the law of a sequence is determined by its
finite windows, the statement is given window by window: for every `N`, the joint law of
`(R_0, …, R_N)` on the two sides agree.

* `Cluster/Coarse.lean` — **coarse-graining**.  `conn n : Conf n → Bool` is the combinatorial
  connectivity of the two terminals, identified with finiteness of the resistance
  (**`res_ne_top_iff_conn`**, using `one_le_res : 1 ≤ res n c`).  The map
  `coarse n : Conf (n+1) → Conf n` declares an edge of the level-`n` lattice open exactly when the
  diamond of level-`(n+1)` edges that replaced it connects its endpoints; this is the coupling that
  turns the levels of the cluster into a process, i.e. the inverse of one substitution step.
  Proved here:

  * **`conn_coarse`** — coarse-graining preserves connectivity of the two terminals;
  * **`confMeasure_map_coarse`** — *at the critical parameter*, the coarse-grained configuration is
    again i.i.d. Bernoulli(`p_c`) (the fixed-point identity `2p_c² − p_c⁴ = p_c`), so the levels
    form a consistent family.

* `Cluster/Tree.lean` — the reduced process of Subsection 4.1 realised as a **tree of replacement
  choices**: `RConf 0 = Unit`, `RConf (n+1) = (RConf n)² ⊕ ((RConf n)² × (RConf n)²)` (series cell
  with two subtrees, or diamond cell with four), with `Rres n` the level-`n` reduced resistance,
  `rtrunc n : RConf (n+1) → RConf n` forgetting the finest generation, `rMeasure pd ps n` the law
  of the tree and `rwin n : RConf n → (Fin (n+1) → ℝ)` the window `(R_0, …, R_n)`.  The link with
  Subsection 4.1 is **`rMeasure_map_Rres`**: the image of `rMeasure pd ps n` under `Rres n` is the
  law `lawMeasure pd ps n` of `R_n`.

* `Cluster/Coupling.lean` — the **reduction map** `Phi n : Conf n → RConf n`, reading off the
  series/diamond choices cell by cell (both branches connect ⇒ diamond; exactly one ⇒ series, the
  dangling pieces of the other branch being deleted), and its three properties:

  * **`rtrunc_Phi`** — `Phi` intertwines coarse-graining with truncation:
    `rtrunc n (Phi (n+1) c) = Phi n (coarse n c)`; this single induction is the compatibility of
    the reduction with one substitution step;
  * **`toReal_res_eq_Rres`** — `Phi` preserves the resistance: `(res n c).toReal = Rres n (Phi n c)`
    for every connected configuration;
  * **`Phi_pushforward`** — at `p_c`, `Phi n` pushes the percolation measure restricted to the
    connected configurations forward to `p_c · rMeasure (pdiamond p_c) (pseries p_c) n`
    (induction on `n`, splitting the connected event into "both branches connect" and the two
    "exactly one branch connects" pieces, whose masses are `p_c⁴` and `p_c²(1 − p_c²)`).

  Consequently, with `cwin n : Conf n → (Fin (n+1) → ℝ)` the window of cluster resistances along
  the coarse-graining coupling,

  * **`cluster_resistance_process`** (**Proposition 4.2, process form**) — for every `n`,
    conditionally on the two boundary vertices being connected, the window `(R_0, …, R_n)` of
    two-terminal effective resistances of the critical percolation cluster has exactly the law of
    the window `(R_0, …, R_n)` of the reduced process of Subsection 4.1;
  * **`cluster_resistance_law_of_process`** — reading the last coordinate recovers the one-level
    statement `cluster_resistance_law`, so the two formulations agree.

All declarations in `RequestProject/Cluster/` are `sorry`-free and depend only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

## Subsection 4.2: the two mean matrices and their Perron roots (`RequestProject/Outlook/`)

Subsection 4.2 ("Outlook: Brownian spectral dimensions for the critical percolation cluster of the
DHL") codes the critical cluster by a four-colour random EIGS with colour order
`(1,2,3,4) = (red, blue, green, black)`, colour `4` being a cemetery state kept only as a zero
placeholder.  Mass growth is governed by the mean offspring matrix `E(M)` (`4 × 4`) and degree
growth by the mean boundary matrix `E(N)` (`8 × 8`); since both systems are reducible, the relevant
eigenvalues are the Perron roots of the *live* blocks (the upper-left `3 × 3` block of `E(M)` and
the upper-left `6 × 6` block of `E(N)`).  The subsection then quotes the numbers

    λ(E(M)) ≈ 3.7303,   λ(E(N)) = 2,   log λ(E(M)) / log 2 ≈ 1.8993.

All three are now machine-verified, at the critical parameter `p = p_c = (√5 - 1)/2`.

* `Outlook/Matrices.lean` — the matrices `EM`, `EN` exactly as printed in the paper, together with
  their live blocks `EMlive`, `ENlive` and the two `3 × 3` blocks `ENodd`, `ENeven` obtained from
  `ENlive` by separating odd and even indices.  Eigenvalues are taken in the elementary sense
  `HasEig A z ↔ ∃ v ≠ 0, A *ᵥ v = z • v` (equivalently `det (z • 1 - A) = 0`, `hasEig_iff_det`), and
  `specRad A = sSup {‖z‖ | z eigenvalue}`.  Proved here: the reductions
  `hasEig_EM_live`, `hasEig_EN_live`, `hasEig_ENlive_split` and their converses
  `hasEig_EMlive_EM`, `hasEig_ENodd_ENlive`, `hasEig_ENlive_EN` (so the cemetery/placeholder rows
  contribute only the eigenvalue `0`), the characteristic polynomials of the `3 × 3` blocks at a
  parameter satisfying `p² = 1 - p`,

      det (t·1 - EMlive p)  = (t - (4 - 4p)) · (t² - (10 - 8p)·t + 8p),
      det (t·1 - ENodd p)   = (t - 2)       · (t² + (8p - 6)·t + (20p - 12)),
      det (t·1 - ENeven p)  = (t - 2p)      · (t² + (6p - 6)·t + (8p - 4)),

  and `quad_root_cases`: a complex root of a monic real quadratic is either real or has squared
  modulus equal to the constant coefficient.

* `Outlook/EigenM.lean` — the Perron root of `E(M)`, defined as the larger root of the quadratic
  factor,

      λ(E(M)) = (10 - 8p_c + √(164 - 256 p_c))/2 = 7 - 2√5 + √(73 - 32√5)   (`lamM`, `lamM_eq`).

  Verified: `lamM_hasEig` (it *is* an eigenvalue of the full `4 × 4` matrix `E(M)`),
  `hasEig_EM_norm_le` (every complex eigenvalue has modulus `≤ λ(E(M))`), hence
  `lamM_isGreatest` / `specRad_EM : specRad (EM p_c) = λ(E(M))`; `lamM_unique` (it is the *unique*
  real eigenvalue `≥ 2`, the other two roots being `≈ 1.5279` and `≈ 1.3254`); and the interval
  arithmetic `3.7302885 < λ(E(M)) < 3.7302886`, whence `lamM_approx : |λ(E(M)) - 3.7303| < 10⁻⁴`.

* `Outlook/EigenN.lean` — `λ(E(N)) = 2` **exactly**: `two_hasEig_EN` exhibits `2` as an eigenvalue
  (it is the Perron root of the odd block), and `hasEig_EN_norm_le` shows every complex eigenvalue
  has modulus `≤ 2` — the remaining roots of the odd block are a complex pair of modulus
  `√(20p_c - 12) ≈ 0.60`, and those of the even block are `2p_c ≈ 1.236`, `≈ 1.7532`, `≈ 0.5386`.
  Hence `lamN_isGreatest` / `specRad_EN : specRad (EN p_c) = 2`.

* `Outlook/Dimensions.lean` — the resulting dimension values

      dimBox = log λ(E(M)) / log 2,        dimDeg = log λ(E(M)) / log λ(E(N)),

  which agree (`dimDeg_eq_dimBox`, because `λ(E(N)) = 2`) and satisfy the sharp enclosure
  `1.89928 < · < 1.89929` (`dimBox_enclosure`), in particular
  `|· - 1.8993| < 10⁻⁴` (`dimBox_approx`, `dimDeg_approx`).  The logarithm is estimated by interval
  arithmetic: writing `λ(E(M)) = 4(1 - u)` with `u ≈ 0.0674`, the five-term Taylor bound
  `Real.abs_log_sub_add_sum_range_le` for `log (1 - u)` is combined with the enclosure of
  `λ(E(M))` and Mathlib's decimal enclosure of `log 2`.
  `section42_numerics` collects the three verified numerical claims of the subsection.

**Scope note.** Only the *computational* content of Subsection 4.2 is formalized: the two Perron
roots and the numerical value derived from them.  The subsection's dimension identities themselves
(`dim_B ⟨Ξ₁⟩₁ = log λ(E(M))/log 2` etc.), the walk dimension, and the spectral-dimension
conjecture are explicitly conjectural in the paper and are not formalized.

All declarations in `RequestProject/Outlook/` are `sorry`-free and depend only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
