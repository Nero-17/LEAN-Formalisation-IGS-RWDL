import Mathlib
import RequestProject.Section2Green

/-!
# Unifying the two notions of effective resistance (Section 2)

The project carries two notions of effective resistance:

* `Section2Network.effRes` — the **Thomson** form: the infimum of the flow energy
  `∑_e θ(e)²` over all unit flows (used to build the renormalisation map `Ψ`);
* `Section2Green.effResToBoundary` — the **Dirichlet/Green** form: the Dirichlet
  energy of the unit-current potential, which `green_diag_eq_resistance` already
  identifies with the Green diagonal `g_S(v,v)`.

This file proves the missing link — **Thomson's principle** — directly inside the
simple-graph / Green framework: the Dirichlet energy of the harmonic unit potential
*equals* the infimum of the flow energy over all unit flows from `v` to the boundary
`Sᶜ`.  Combined with `green_diag_eq_resistance`, this shows the three quantities

  `R_eff (Thomson infimum)  =  effResToBoundary (Dirichlet energy)  =  g_S(v,v)`

coincide, so the resistance used in `E[τ] ≍ V·R` is the same object as the
renormalisation resistance `ℛ ≍ ρ(Ψ)ⁿ`.

## Contents

* `flowDiv`, `IsBoundaryUnitFlow`, `flowEnergy` — flows on a simple graph and their
  energy (a unit of current injected at `v`, extracted on `Sᶜ`).
* `harmonicFlow` — the gradient flow of the unit potential; `harmonicFlow_isFlow`
  shows it is a boundary unit flow and `flowEnergy_harmonic` computes its energy.
* `thomson_lower` — Thomson optimality: the harmonic flow minimises the energy.
* `effResToBoundary_eq_iInf` — the unification theorem (Thomson's principle).
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Flows on a simple graph -/

/-- The **divergence** of a current `θ` at a vertex `x`: the net outflow
`∑_{y ∼ x} θ(x,y)`. -/
def flowDiv (θ : V → V → ℝ) (x : V) : ℝ := ∑ y, if G.Adj x y then θ x y else 0

/-- `θ` is a **unit flow from `v` to the boundary `Sᶜ`**: it is antisymmetric
(`θ(x,y) = -θ(y,x)`) and has divergence `+1` at `v` and `0` at every other vertex of
`S` (the boundary `Sᶜ` absorbs the current). -/
def IsBoundaryUnitFlow (S : Finset V) (v : V) (θ : V → V → ℝ) : Prop :=
  (∀ x y, θ x y = - θ y x) ∧ (∀ x ∈ S, flowDiv G θ x = if x = v then 1 else 0)

/-- The **energy** of a current `θ`: `½ ∑_{x,y : x ∼ y} θ(x,y)²` (each undirected
edge counted once). -/
noncomputable def flowEnergy (θ : V → V → ℝ) : ℝ :=
  (∑ x, ∑ y, if G.Adj x y then (θ x y) ^ 2 else 0) / 2

/-- The **harmonic flow**: the gradient of the unit-current potential,
`θ_h(x,y) = h(x) − h(y)`. -/
noncomputable def harmonicFlow (S : Finset V) (v : V) : V → V → ℝ :=
  fun x y => unitPotential G S v x - unitPotential G S v y

/-! ### The divergence of a gradient is the Laplacian -/

/-
The divergence of the gradient flow of `f` equals the graph Laplacian applied to
`f`: `div(∇f)(x) = (L f)(x)`.
-/
lemma flowDiv_gradient (f : V → ℝ) (x : V) :
    flowDiv G (fun a b => f a - f b) x = (G.lapMatrix ℝ *ᵥ f) x := by
  simp +decide [ flowDiv, lapMatrix, Matrix.mulVec, dotProduct, SimpleGraph.degMatrix, SimpleGraph.adjMatrix ];
  simp +decide [ Finset.sum_ite, SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
  simp +decide [ sub_mul, Finset.sum_sub_distrib, Finset.sum_ite, diagonal ]

/-! ### The harmonic flow is a boundary unit flow with energy `R_eff` -/

lemma harmonicFlow_antisym (S : Finset V) (v : V) (x y : V) :
    harmonicFlow G S v x y = - harmonicFlow G S v y x := by
  unfold harmonicFlow; ring

/-
The harmonic flow is a unit flow from `v` to the boundary `Sᶜ`.
-/
lemma harmonicFlow_isFlow (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) :
    IsBoundaryUnitFlow G S v (harmonicFlow G S v) := by
  refine' ⟨ fun x y => EIGS.harmonicFlow_antisym G S v x y, _ ⟩;
  exact fun x hx => by rw [ show harmonicFlow G S v = fun a b => unitPotential G S v a - unitPotential G S v b from rfl ] ; exact flowDiv_gradient G ( unitPotential G S v ) x ▸ lapMatrix_mulVec_unitPotential G hG hSc hv x hx;

/-
The energy of the harmonic flow equals the effective resistance to the boundary
(= the Dirichlet energy of the unit potential).
-/
lemma flowEnergy_harmonic (S : Finset V) (v : V) :
    flowEnergy G (harmonicFlow G S v) = effResToBoundary G S v := by
  convert rfl

omit [DecidableEq V] in
lemma flowEnergy_nonneg (θ : V → V → ℝ) : 0 ≤ flowEnergy G θ := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    by_cases h : G.Adj x y <;> simp [h, sq_nonneg]

/-! ### Thomson's principle (orthogonality and optimality) -/

/-
**Orthogonality.**  If `f` vanishes off `S` and `ψ` is antisymmetric with
divergence `0` on `S`, then the gradient of `f` is energy-orthogonal to `ψ`.
-/
lemma grad_orthogonal {S : Finset V} {f : V → ℝ} (hf : ∀ x, x ∉ S → f x = 0)
    {ψ : V → V → ℝ} (hψ : ∀ x y, ψ x y = - ψ y x)
    (hdiv : ∀ x ∈ S, flowDiv G ψ x = 0) :
    (∑ x, ∑ y, if G.Adj x y then (f x - f y) * ψ x y else 0) = 0 := by
  have hA : ∑ x, ∑ y, (if G.Adj x y then f x * ψ x y else 0) = ∑ x, f x * flowDiv G ψ x := by
    simp +decide [ flowDiv, Finset.mul_sum _ _ _, mul_comm ];
  have hB : ∑ x, ∑ y, (if G.Adj x y then f y * ψ x y else 0) = -∑ x, f x * flowDiv G ψ x := by
    rw [ ← Finset.sum_comm ] ; simp +decide [ Finset.sum_ite, SimpleGraph.adj_comm ] ; ring;
    rw [ ← Finset.sum_neg_distrib ] ; congr ; ext x ; rw [ show flowDiv G ψ x = ∑ y, if G.Adj x y then ψ x y else 0 from rfl ] ; simp +decide [ Finset.sum_ite, SimpleGraph.adj_comm ] ; ring;
    rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_congr rfl fun y hy => by rw [ hψ ] ; ring;
  convert congr_arg₂ ( · - · ) hA hB using 1;
  · simpa only [ ← Finset.sum_sub_distrib ] using Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by split_ifs <;> ring;
  · rw [ Finset.sum_eq_zero ] <;> norm_num;
    exact fun x => if hx : x ∈ S then Or.inr ( hdiv x hx ) else Or.inl ( hf x hx )

/-
**Thomson optimality.**  The harmonic flow minimises the energy among all unit
flows from `v` to the boundary.
-/
lemma thomson_lower (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) {θ : V → V → ℝ} (hθ : IsBoundaryUnitFlow G S v θ) :
    flowEnergy G (harmonicFlow G S v) ≤ flowEnergy G θ := by
  have h_harmonicFlow : IsBoundaryUnitFlow G S v (harmonicFlow G S v) :=
    harmonicFlow_isFlow G hG hSc hv
  have h_orthogonal : ∑ x, ∑ y, (if G.Adj x y then (unitPotential G S v x - unitPotential G S v y) * (θ x y - (unitPotential G S v x - unitPotential G S v y)) else 0) = 0 := by
    apply_rules [ grad_orthogonal ];
    · unfold unitPotential; aesop;
    · intro x y; linarith [ hθ.1 x y, harmonicFlow_antisym G S v x y ] ;
    · intro x hx; have := hθ.2 x hx; have := h_harmonicFlow.2 x hx; simp_all +decide [ flowDiv ] ;
      simp_all +decide [ Finset.sum_ite, harmonicFlow ];
  have h_expand : ∑ x, ∑ y, (if G.Adj x y then (θ x y)^2 else 0) = ∑ x, ∑ y, (if G.Adj x y then (unitPotential G S v x - unitPotential G S v y)^2 else 0) + ∑ x, ∑ y, (if G.Adj x y then (θ x y - (unitPotential G S v x - unitPotential G S v y))^2 else 0) + 2 * ∑ x, ∑ y, (if G.Adj x y then (unitPotential G S v x - unitPotential G S v y) * (θ x y - (unitPotential G S v x - unitPotential G S v y)) else 0) := by
    simp +decide only [← sum_add_distrib, Finset.mul_sum _ _ _];
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by split_ifs <;> ring;
  unfold flowEnergy; simp_all +decide [ Finset.sum_ite ] ;
  exact div_le_div_of_nonneg_right ( le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) zero_le_two

/-! ### The unification theorem (Thomson's principle) -/

/-
**Thomson's principle / unification of effective resistances.**  The Dirichlet
energy of the unit potential — equivalently the Green diagonal `g_S(v,v)` by
`green_diag_eq_resistance` — equals the infimum of the flow energy over all unit
flows from `v` to the boundary `Sᶜ`, i.e. the Thomson effective resistance.
-/
theorem effResToBoundary_eq_iInf (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) :
    effResToBoundary G S v
      = ⨅ θ : {θ : V → V → ℝ // IsBoundaryUnitFlow G S v θ}, flowEnergy G θ.1 := by
  convert le_antisymm _ _;
  exact inferInstance;
  · refine' le_csInf _ _;
    · exact ⟨ _, ⟨ ⟨ _, harmonicFlow_isFlow G hG hSc hv ⟩, rfl ⟩ ⟩;
    · rintro _ ⟨ θ, rfl ⟩;
      convert thomson_lower G hG hSc hv θ.2 using 1;
  · refine' ciInf_le_of_le _ _ _;
    exact ⟨ 0, Set.forall_mem_range.mpr fun θ => flowEnergy_nonneg _ _ ⟩;
    exact ⟨ harmonicFlow G S v, harmonicFlow_isFlow G hG hSc hv ⟩;
    convert flowEnergy_harmonic G S v |> le_of_eq

/-- The Green diagonal `g_S(v,v)` equals the Thomson effective resistance (the flow
energy infimum), tying the Green/Dirichlet and Thomson notions together. -/
theorem green_diag_eq_iInf (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) :
    greenFn G S ⟨v, hv⟩ ⟨v, hv⟩
      = ⨅ θ : {θ : V → V → ℝ // IsBoundaryUnitFlow G S v θ}, flowEnergy G θ.1 := by
  rw [← green_diag_eq_resistance G hG hSc hv, effResToBoundary_eq_iInf G hG hSc hv]

end EIGS