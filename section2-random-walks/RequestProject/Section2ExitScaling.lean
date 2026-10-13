import Mathlib
import RequestProject.Section2Green
import RequestProject.Section2Commute
import RequestProject.Section22
import RequestProject.Section1Vertices

/-!
# Assembling `E[τ] ≍ V·R` and the walk dimension for the EIGS (Section 2)

This file ties together the layers built in `Section2Green.lean`
(Dirichlet Green function, exit-time upper bound, conditional lower bound),
`Section2Commute.lean` (the self-contained commute-time identity `C = 2|E|·R`)
and `Section22.lean` (the analytic scaling-dimension core), and instantiates them
onto the concrete substitution networks `Ξⁿ` built in `Section1Vertices.lean`.

Following the roadmap:

* **Two-sided exit estimate `E[τ] ≍ V·R`** (`exit_two_sided`).  The clean upper
  bound `E^v[τ_S] ≤ R_eff·V(S)` is unconditional; the matching lower bound
  `c·c'·R_eff·V(S) ≤ E^v[τ_S]` is reduced (faithfully, as in the paper) to the two
  genuine EIGS-local-geometry inputs: a near-diagonal Green lower bound on a
  sizeable set `T ⊆ S`, and local volume regularity `c'·V(S) ≤ ∑_{y∈T} deg(y)`.

* **Instantiation onto `Ξⁿ`** (`xi_exit_two_sided`).  The general Green layer is
  written for an arbitrary finite connected simple graph; here it is plugged into
  the concrete `XiSimpleGraph 𝓘 n`, so that the word "local" in the inputs has a
  concrete carrier.  Connectivity of `Ξⁿ` is the cited structural input.

* **Commute-time scaling from the identity** (`commute_time_geometric_of_identity`).
  `Section22.commute_time_bounds` previously *assumed* the commute time had the
  form `2·|E|·R`.  Here we feed in the now-*proved* identity `C = 2|E|·R`
  (`Section2Commute.commute_eq_two_card_edges_mul_resistance`, supplied through the
  hypothesis `hid`) and obtain the genuine two-sided geometric scaling of the
  commute time.

* **Walk dimension** (`xi_walk_dimension`).  Combining the exit-time scaling
  `E[τ] ≍ (ρ(M)ρ(Ψ))^{m}` with the radius scaling `r ≍ ρ_min^{m}` gives the
  Einstein relation `dim_W = dim_B + dim_R`, via `Section22.walk_dimension_einstein`.

The deep geometric inputs (distance growth `diam ≍ ρ_min^n`, local volume/resistance
regularity, near-diagonal Green comparison, and Perron–Frobenius eigenpair
existence) are carried as explicit hypotheses, exactly as the paper cites them.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset Filter Topology

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The two-sided exit estimate `E[τ] ≍ V·R` -/

/-- **Two-sided exit estimate `E[τ] ≍ V·R` (general connected graph).**
The upper bound `τ(v) ≤ R_eff(v,Sᶜ)·V(S)` is unconditional; the lower bound
`c·c'·R_eff·V(S) ≤ τ(v)` is reduced to the two EIGS-local-geometry inputs
`hnd` (near-diagonal Green lower bound on `T`) and `hvol` (local volume
regularity). -/
theorem exit_two_sided (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S)
    {T : Finset V} (hTS : T ⊆ S) {c c' : ℝ} (hc : 0 < c)
    (hnd : ∀ y : V, ∀ hy : y ∈ T,
      c * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ ≤ greenFn G S ⟨v, hv⟩ ⟨y, hTS hy⟩)
    (hvol : c' * volume G S ≤ ∑ y ∈ T, (G.degree y : ℝ)) :
    c * c' * effResToBoundary G S v * volume G S ≤ τ v
      ∧ τ v ≤ effResToBoundary G S v * volume G S :=
  ⟨exit_ge_volume_mul_resistance G hG hSc hτ hv hTS hc hnd hvol,
   exit_le_volume_mul_resistance G hG hSc hτ hv⟩

/-! ### Instantiation onto the substitution network `Ξⁿ` -/

variable {K : ℕ}

/-- The adjacency of the substitution network `Ξⁿ` is decidable (classically). -/
noncomputable instance XiSimpleGraphDecidableRel (𝓘 : EIGSData K) (n : ℕ) :
    DecidableRel (XiSimpleGraph 𝓘 n).Adj := Classical.decRel _

/-- **Two-sided exit estimate on `Ξⁿ`.**  The general Green-function exit estimate
instantiated to the concrete substitution network `XiSimpleGraph 𝓘 n`. -/
theorem xi_exit_two_sided (𝓘 : EIGSData K) (n : ℕ)
    (hG : (XiSimpleGraph 𝓘 n).Connected) {S : Finset (XiVtx 𝓘 n)} (hSc : Sᶜ.Nonempty)
    {τ : XiVtx 𝓘 n → ℝ} (hτ : ExitSystem (XiSimpleGraph 𝓘 n) S τ)
    {v : XiVtx 𝓘 n} (hv : v ∈ S)
    {T : Finset (XiVtx 𝓘 n)} (hTS : T ⊆ S) {c c' : ℝ} (hc : 0 < c)
    (hnd : ∀ y : XiVtx 𝓘 n, ∀ hy : y ∈ T,
      c * greenFn (XiSimpleGraph 𝓘 n) S ⟨v, hv⟩ ⟨v, hv⟩
        ≤ greenFn (XiSimpleGraph 𝓘 n) S ⟨v, hv⟩ ⟨y, hTS hy⟩)
    (hvol : c' * volume (XiSimpleGraph 𝓘 n) S ≤ ∑ y ∈ T, ((XiSimpleGraph 𝓘 n).degree y : ℝ)) :
    c * c' * effResToBoundary (XiSimpleGraph 𝓘 n) S v * volume (XiSimpleGraph 𝓘 n) S ≤ τ v
      ∧ τ v ≤ effResToBoundary (XiSimpleGraph 𝓘 n) S v * volume (XiSimpleGraph 𝓘 n) S :=
  exit_two_sided (XiSimpleGraph 𝓘 n) hG hSc hτ hv hTS hc hnd hvol

/-! ### Commute-time scaling from the proved identity `C = 2|E|·R` -/

/-- **Commute-time geometric scaling, from the identity `C = 2|E|·R`.**
The hypothesis `hid : Commute n = 2·Edges n·Res n` is exactly the content of the
self-contained identity `commute_eq_two_card_edges_mul_resistance` of
`Section2Commute.lean` (with `Edges n = |E(Ξⁿ)|`, `Res n = ℛ(𝔳₊,𝔳₋)`).  Combined
with the geometric mass/resistance bounds it yields the genuine two-sided commute
scaling `C ≍ (ρ(M)ρ(Ψ))^n` — `Section22.commute_time_bounds` no longer needs to
*assume* the `2·|E|·R` form. -/
theorem commute_time_geometric_of_identity
    {Commute Edges Res : ℕ → ℝ} {ρM ρPsi cE CE cΨ CΨ : ℝ}
    (hcE : 0 < cE) (hcΨ : 0 < cΨ) (hρM : 0 < ρM) (hρPsi : 0 < ρPsi)
    (hid : ∀ n, Commute n = 2 * Edges n * Res n)
    (hE : ∀ n, cE * ρM ^ n ≤ Edges n ∧ Edges n ≤ CE * ρM ^ n)
    (hR : ∀ n, cΨ * ρPsi ^ n ≤ Res n ∧ Res n ≤ CΨ * ρPsi ^ n) :
    ∀ n, 2 * cE * cΨ * (ρM * ρPsi) ^ n ≤ Commute n
        ∧ Commute n ≤ 2 * CE * CΨ * (ρM * ρPsi) ^ n := by
  intro n
  rw [hid n]
  exact commute_time_bounds hcE hcΨ hρM hρPsi hE hR n

/-! ### Walk dimension of `Ξ` from the exit-time scaling -/

/-- **Walk dimension via the exit-time scaling (Einstein relation).**  If the exit
time `Exit n` is squeezed between `c₁(ρ(M)ρ(Ψ))^{m n}` and `c₂(ρ(M)ρ(Ψ))^{m n}` and
the radius `Rad n` between `c₃ρ_min^{m n}` and `c₄ρ_min^{m n}` (with the level
`m n → ∞`), then the walk dimension `resistanceDimension Exit Rad` splits as
`dim_B + dim_R = log ρ(M)/log ρ_min + log ρ(Ψ)/log ρ_min`.  This is the assembly of
the `E[τ] ≍ V·R` programme into the walk dimension. -/
theorem xi_walk_dimension
    {Exit Rad : ℕ → ℝ} {ρM ρPsi ρmin : ℝ} {m : ℕ → ℕ}
    (hρM : 0 < ρM) (hρPsi : 0 < ρPsi) (hρmin : 1 < ρmin) (hm : Tendsto m atTop atTop)
    (hExit : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n, c₁ * (ρM * ρPsi) ^ (m n) ≤ Exit n ∧ Exit n ≤ c₂ * (ρM * ρPsi) ^ (m n))
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
      ∀ n, c₃ * ρmin ^ (m n) ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ (m n)) :
    resistanceDimension Exit Rad
      = Real.log ρM / Real.log ρmin + Real.log ρPsi / Real.log ρmin :=
  walk_dimension_einstein hρM hρPsi hρmin hm hExit hRad

end EIGS
