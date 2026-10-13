import RequestProject.Section32.TraceResistance
import RequestProject.Section32.PointBoundary
import RequestProject.Section32.DyadicExample
import RequestProject.Section32.ResistanceHomeo
import RequestProject.Section32.CommonCore
import RequestProject.Section32.FormsAgree

/-!
# A formalisation of Section 3.2 of arXiv:2603.13798

*Iterated Graph Systems (I): random walks and diffusion limits*,
§3.2 "Resistance-form Brownian motion".

Same rule as for §3.1: **everything the paper itself imports from the literature
is taken as an explicit hypothesis**, and everything the paper argues itself is
proved.  No `sorry` and no new axioms appear; every statement below compiles.

Throughout the subsection the paper assumes `d_R(Ξ) > 0`, equivalently
`ρ(Ψ) > 1`; that inequality appears as the hypothesis `1 < rho` wherever it is
used, and it is genuinely used (it is what makes the recursion
`A_{L+1} ≤ ρ⁻¹A_L + B` bounded, and what makes `ρ^{-m} → 0`).

## Correspondence with the paper

| paper | file | what is proved here |
|---|---|---|
| definition of `R_m`, and `R_{m+1} = R_m` on `V(Ξ^m)` | `Section32.TraceResistance` | from trace compatibility alone: minimising the level-`(m+1)` energy under `f(x)=0`, `f(y)=1` gives the same value as at level `m` (`condEnergy_succ_eq`), so `R_n(x,y)` is independent of the level `n` containing `x,y` (`Reff_stable`, `Reff_eq_of_mem`) — this is what makes `R_*` well defined |
| `ℰ_𝒱(f,f) := lim_m ℰ_m^W` exists | `Section32.TraceResistance`, `Section3.ResistanceForm` | trace compatibility makes the traced energies non-decreasing (`CompatibleEnergies.energy_mono`), so on the domain `ℱ_𝒱` the limit exists and equals the supremum (`traced_energy_tendsto`) |
| Lemma `sec32_point_boundary` | `Section32.PointBoundary` | the full induction on the height `h_Λ(z)`: base case from the terminal-to-terminal resistance `ρ(Ψ)^{-m}[v]_i`, inductive step from the triangle inequality and the finitely many first-generation configurations, giving `R_*(z,a_Λ), R_*(z,b_Λ) ≤ C_∂ρ(Ψ)^{-m}` with the explicit constant `C_∂ = max(A₀, Bρ(Ψ)/(ρ(Ψ)-1))` (`point_boundary`), and its uniform-smallness form (`point_boundary_tendsto`) |
| Lemma `sec32_point_boundary`, worked instance | `Section32.DyadicExample` | all the hypotheses verified in the dyadic model of the line (`ρ = 2`, `A₀ = B = 1`), so the lemma is not vacuous: every dyadic point of a level-`m` dyadic interval is within `2·2^{-m}` of either endpoint |
| Theorem `sec32_resistance_metric` | `Section32.ResistanceHomeo` | the paper's own argument: the cell bound makes the canonical map `(𝒱,d) → (𝒱,R_*)` uniformly continuous, hence `d`-convergent sequences are `R_*`-Cauchy with a limit independent of the sequence (`uniformContinuous_of_cell_bound`, `iota`); the extension `ι : Ξ_M → Ξ_R` is continuous, surjective (compact image, closed, containing the dense `𝒱`), injective (separation by a finite-energy harmonic spline), hence a homeomorphism (`resistanceHomeo`) |
| Lemma `sec32_common_core` | `Section32.CommonCore` | both halves: density in the form norm — a function orthogonal to all splines vanishes on `𝒱`, hence (continuity + density) is `0`, and a subspace of a Hilbert space with trivial orthogonal complement is dense (`spline_core_dense`); and density in `L²` — the pointwise bound `|u - P_m^Ru|² ≤ C_∂ρ(Ψ)^{-m}ℰ_R(u,u)` (`spline_error_pointwise`) integrates to `‖u-P_m^Ru‖²_{L²(μ)} → 0` for a probability measure `μ` (`spline_error_L2_le`, `spline_error_L2_tendsto`) |
| Theorem `sec32_brownian_motion` | `Section32.FormsAgree` | two closed forms agreeing on a common core agree everywhere (`closed_forms_agree`), proved from core approximation and closedness (Fatou) via the reverse triangle inequality for the energy norms; the last sentence, that the same form gives the same semigroup, Hunt process and heat kernel (`P_t^R = P_t^W`, `q_t = p_t`), is `process_eq_of_forms_agree`, whose hypothesis `hdet` is precisely the cited correspondence |

## What is *not* proved (and is not claimed to be)

Exactly the results the paper cites rather than proves:

* the construction of a resistance form from compatible finite traces, and the
  identification of its resistance metric with `R_*` (Kigami);
* that finite-energy functions are continuous in the resistance metric (Kigami);
* trace theory identifying the `ℰ_R`-orthogonal complement of the level-`m`
  spline subspace with the functions of vanishing trace on `V(Ξ^m)`;
* the correspondence "regular Dirichlet form ↔ symmetric Hunt process" and the
  resulting identification of semigroups and heat kernels (Fukushima et al.);
* the level-`m` terminal-to-terminal resistance `ρ(Ψ)^{-m}[v]_i` (§2), and the
  trace compatibility of `(ℰ_m^W)` itself (Lemma `sec31_trace_weighted`, whose
  own decomposition is formalised in `Section31.TraceMin`).

Each of these appears as a named hypothesis of the statements above, so the
place where it enters is visible.

Remarks on the statements themselves are collected in `SECTION32_NOTES.md`.
-/
