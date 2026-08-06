import RequestProject.Section31.CellMass
import RequestProject.Section31.WeakLimit
import RequestProject.Section31.NoShortcut
import RequestProject.Section31.Oscillation
import RequestProject.Section31.Contraction
import RequestProject.Section31.PathExample
import RequestProject.Section31.MarkovProperty
import RequestProject.Section31.DirichletPrinciple
import RequestProject.Section31.TraceMin
import RequestProject.Section31.HarmonicSplines
import RequestProject.Section31.ProjectionTail
import RequestProject.Section31.SpeedMeasure
import RequestProject.Section31.DiscreteHarmonics
import RequestProject.Section31.Mosco
import RequestProject.Section31.ExitTime
import RequestProject.Section31.WatchedChain
import RequestProject.Section31.TraceChain
import RequestProject.Section31.TraceDecomposition
import RequestProject.Section31.WatchedChainExample
import RequestProject.Section31.Chaining
import RequestProject.Section31.ContinuousStay
import RequestProject.Section31.Main

/-!
# A formalisation of Section 3.1 of arXiv:2603.13798

*Iterated Graph Systems (I): random walks and diffusion limits*,
§3.1 "Dirichlet form and diffusion limits" (together with the two lemmas of the
§3 preamble that it uses).

The rule followed here is the one the user asked for: **everything the paper
itself imports from the literature is taken as a hypothesis**, and everything
the paper argues itself is proved.  No `sorry` and no new axioms appear
anywhere; every statement below compiles.

## Correspondence with the paper

| paper | file | what is proved here |
|---|---|---|
| Lemma `GH_limit_metric` | — | black box (the Gromov–Hausdorff limit space, `neroli2024fractal`) |
| Lemma `GHP_convergence`, final step | `Section31.WeakLimit` | the monotone-class argument: two Borel probability measures agreeing on a generating π-system of cells coincide, and (compactness of the space of probability measures on a compact metric space) a sequence whose subsequential limits all give the cells their prescribed masses converges weakly |
| Lemma `GHP_convergence` | `Section31.CellMass`, `Section3.Recursions` | the affine Perron recursion and the cell mass `≍ ρ(M)^{-m}` (scalar case); `μ({x}) = 0` for every finite-born point, from the star bound `C ρ(N)^{m-k} · C' ρ(M)^{-m}` |
| Lemma `sec31_trace_weighted`, one-cell input | `Section31.DirichletPrinciple` | the Dirichlet principle on a finite network: existence and uniqueness of the energy minimiser with prescribed boundary values, together with the discrete Poincaré inequality along a path which supplies its only analytic input |
| Lemma `sec31_trace_weighted` | `Section31.TraceMin` | the decoupling over cells: the minimum of the level-`(n+1)` energy over all extensions is the sum of the one-cell minima, and it is attained at a unique extension; plus the renormalisation identity `ρ(Ψ)^{n+1} ψ_i(v)^{-1} = ρ(Ψ)^n [v]_i^{-1}` |
| Lemma `sec31_continuous_harmonics` | `Section31.HarmonicSplines` | geometric decay of the cell oscillations, uniform convergence of the harmonic extensions to a continuous function, and the maximum-principle argument giving uniform density of the splines in `C(Ξ_M)` |
| Lemma `sec31_continuous_harmonics`, the contraction `θ < 1` | `Section31.NoShortcut`, `Section31.Oscillation`, `Section31.Contraction` | **now proved rather than assumed**: the standing assumption (distance-positivity for `K ≥ 2`, `d(β^+,β^-) ≥ 2` for `K = 1`) excludes shortcut edges; the Euler–Lagrange equation, the truncation maximum principle `0 ≤ g ≤ 1` and the strong maximum principle then give edge oscillation `< 1` for the `0`–`1` profile; finiteness of the rule-graph family (and convergence of the conductance family) give a uniform `θ ∈ [0,1)`, and affinity in the boundary data turns it into the contraction "child oscillation `≤ θ ·` parent oscillation" |
| Lemma `sec31_continuous_harmonics`, worked example | `Section31.PathExample` | all the hypotheses above verified on the path of length `2`, the shortest rule graph the standing assumption allows: its profile is `(0, 1/2, 1)` and `θ = 1/2` |
| Lemma `sec31_projection_tail_continuous`, Lemma `sec31_projection_tail_discrete` | `Section31.ProjectionTail` | the Pythagoras identity for the harmonic projection and the geometric summation producing `‖u-u_m‖₂² ≤ C (ρ(M)ρ(Ψ))^{-m} ℰ(u,u)` |
| Theorem `sec31_limit_dirichlet_form` | `Section31.MarkovProperty` (+ black box) | the Markov property inherited from the finite traces is proved (`ℰ(T∘g) ≤ ℰ(g)` for every normal contraction `T`, and its stability under suprema); the construction of the closure as a regular Dirichlet form remains a black box (`fukushima1994dirichlet`), its two hypotheses being density of the splines and the tail estimate |
| Lemma `sec31_speed_measure` | `Section31.SpeedMeasure` | the uniform cell bound `π_n(V(Λ)) ≤ C_m ρ(M)^{-m}` with an explicit constant, and the transfer of weak convergence from `μ_{Ξⁿ}` to `π_n` |
| Lemma `sec31_discrete_harmonics` | `Section31.DiscreteHarmonics` | the Perron limit of the traced conductances, the convergence of the minimisers of a uniformly convergent family of forms on a compact space, and the convergence of the energy and `L²` Gram matrices |
| Theorem `sec31_mosco` | `Section31.Mosco` | the definition of Mosco convergence for a varying-space asymptotic relation, and the closing step of the liminf inequality (closedness of the limit form applied to the spline approximations) |
| Lemma `sec31_one_step_stay` | `Section31.ExitTime`, `Section31.Main` | `E[τ] ≤ t + E[(τ-t)^+]` and the arithmetic giving `p_stay = c_exit/(2 C_exit)`, and the unrolling of the cell-exit recursion `T_s ≤ T_{s-1} + A q^{s-1} ⇒ T_s ≤ C_T q^s` |
| Lemma `sec31_one_step_stay`, "uniform exit bound for cells" | `Section31.WatchedChain` | **the recursion itself**: for a finite-state chain, geometric decay of the survival probabilities from a uniform hitting probability; connectivity (a descent function `ν ≤ N`) plus a compact conductance range `[a,b]` giving the *explicit* bound `C_R = N (card S · b/a)^N` on the expected number of skeleton jumps; the optional-stopping (Wald) step bounding the accumulated jump durations by `C_R · C_⋆ q^{s-1}`; and the two composed into `T_s ≤ T_{s-1} + C_R C_⋆ q^{s-1}` and `T_s ≤ C_T q^s` |
| Lemma `sec31_one_step_stay`, watched chain | `Section31.TraceChain` | the watched process **is** a Markov chain on the skeleton: the hitting distribution of the skeleton exists as a monotone limit, is supported on the skeleton, and is a probability distribution as soon as the skeleton is hit almost surely (which the uniform hitting estimate gives), so the trace kernel `Q(v,w) = ∑_u P(v,u) P_u(X_{σ_S}=w)` is a genuine transition kernel |
| Lemma `sec31_one_step_stay`, optional stopping | `Section31.TraceDecomposition` | the decomposition itself, *proved* rather than assumed: `E_z[σ_B] ≤ E_z[σ_S] + ∑_w P_z(X_{σ_S}=w)·(accumulated jump time)` — obtained by exhibiting the right-hand side as a supersolution — and hence `E_z[σ_B] ≤ T_{s-1} + C_⋆ q^{s-1} C_R`, the only §2 inputs being the identification of the watched kernel with the conductance walk and the one-excursion bound |
| Lemma `sec31_one_step_stay`, worked example | `Section31.WatchedChainExample` | all the hypotheses of the previous line verified on the path skeleton `0 — 1 — 2` with terminals `{0,2}`: `C_R = 3`, and with unit jump durations the accumulated cost is exactly `1` |
| Theorem `sec31_discrete_eld_tightness` | `Section31.ExitTime` | the two scaling identities that fix the chaining radius `δ = (t/r)^{1/(d_w-1)}`: `r δ^{d_w-1} = t` and `r/δ = (r^{d_w}/t)^{1/(d_w-1)}` |
| Theorem `sec31_discrete_eld_tightness`, chaining | `Section31.Chaining` | the bookkeeping of the chaining proof: the deterministic inclusion `{τ ≤ t} ⊆ {#long increments ≤ t/Δ}`, and its combination with the Azuma–Hoeffding lower tail (a hypothesis, as in the paper) into exactly the displayed bound `C exp[-c (r^{d_w}/t)^{1/(d_w-1)}]` |
| Theorem `sec31_ghps` | — | black box (`kuwae2003convergence`, `billingsley1999convergence`) |
| Corollary `sec31_continuous_stay` | `Section31.Main` | the full derivation from the discrete stay estimate and the Skorokhod coupling |

## What is *not* proved (and is not claimed to be)

The Gromov–Hausdorff(-Prokhorov) limit space and topology; the existence of the
weak limit measure; the correspondence between regular Dirichlet forms and Hunt
processes; the process-convergence theorem for Mosco-convergent forms in varying
spaces; Azuma–Hoeffding and Aldous' tightness criterion; the Skorokhod
representation theorem; the effective-resistance computation on a single rule
graph (§2).  These are precisely the results that the paper cites rather than
proves.

Remarks on the statements themselves are collected in
`SECTION31_NOTES.md` at the root of the repository.
-/
