import Mathlib
import RequestProject.Section2ExitTime

/-!
# Dirichlet Green functions and the exit-time estimate `E[τ] ≍ V·R` (Section 2)

This file builds the **Dirichlet Green function** layer that sits above the
exit-time linear system of `Section2ExitTime.lean`, following the roadmap

* **Step 1 (Green function, finite linear algebra).**  For a finite connected
  simple graph `G` and a set `S` with nonempty complement, the *Dirichlet
  Laplacian* `L_S` is the principal submatrix of the graph Laplacian on the
  index set `S` (Dirichlet boundary conditions on `Sᶜ`).  It is symmetric
  positive definite, hence invertible, and its inverse is the **Green function**
  `g_S = L_S⁻¹`.  We prove:
  - `green_symm` : `g_S` is symmetric (`L_S` symmetric ⇒ inverse symmetric);
  - `exit_eq_green_weighted` : the exit time is the Green row-sum
    `τ(v) = ∑_{y∈S} g_S(v,y) deg(y)` (this is `L_S τ = deg` read backwards);
  - `green_diag_eq_resistance` : `g_S(v,v) = R_eff(v, Sᶜ)`, the diagonal of the
    Green function equals the effective resistance from `v` to the boundary
    (energy of the unit-current potential);
  - `greenFn_nonneg` / `green_le_diag` : `0 ≤ g_S(v,y) ≤ g_S(v,v)` (discrete
    minimum/maximum principle).

* **Step 2 (upper bound, reachable).** `exit_le_volume_mul_resistance` :
  `E^v[τ_S] = τ(v) = ∑_y g_S(v,y) deg(y) ≤ g_S(v,v) ∑_y deg(y) = R_eff · V(S)`,
  the clean upper half of `E[τ] ≍ V·R`, with `V(S) = ∑_{x∈S} deg(x)`.

* **Step 3 (lower bound, the hard core).** `exit_ge_volume_mul_resistance` :
  a *conditional* lower bound `E^v[τ_S] ≥ c·c'·R_eff·V(S)`, reduced to its two
  genuine analytic inputs — a near-diagonal lower bound on `g_S(v,·)` on a
  sizeable set `T ⊆ S`, and local volume regularity `c'·V(S) ≤ ∑_{y∈T} deg(y)`.
  Supplying these inputs is exactly "doing the real §2.2 local analysis", and is
  the part that genuinely requires the EIGS-specific local geometry
  (`diam ≍ ρ_min^n`, `V(B(v,r)) ≍ r^{d_f}`, `R(v,Bᶜ) ≍ r^ζ`).
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The Dirichlet Laplacian and the Green function -/

/-- The **Dirichlet Laplacian** `L_S`: the principal submatrix of the graph
Laplacian on the index set `S` (Dirichlet boundary conditions on `Sᶜ`). -/
def dirichletLap (S : Finset V) : Matrix S S ℝ :=
  (G.lapMatrix ℝ).submatrix (fun i : S => (i : V)) (fun j : S => (j : V))

/-- The **Dirichlet Green function** `g_S = L_S⁻¹`. -/
noncomputable def greenFn (S : Finset V) : Matrix S S ℝ := (dirichletLap G S)⁻¹

/-
The Dirichlet Laplacian is symmetric.
-/
lemma dirichletLap_isSymm (S : Finset V) : (dirichletLap G S).IsSymm := by
  convert Matrix.IsSymm.transpose _;
  ext i j; simp +decide [ SimpleGraph.adj_comm, Matrix.IsSymm, lapMatrix ] ;
  by_cases hij : ( i : V ) = j <;> simp +decide [ hij, degMatrix ];
  rw [ diagonal_apply_ne ] ; aesop

/-
**`green_symm`.** The Green function is symmetric: `g_S(x,y) = g_S(y,x)`.
-/
theorem green_symm (S : Finset V) (x y : S) :
    greenFn G S x y = greenFn G S y x := by
  convert congr_arg ( fun m : Matrix S S ℝ => m y x ) ( show ( greenFn G S )ᵀ = ( greenFn G S ) from ?_ ) using 1;
  unfold greenFn; rw [ Matrix.transpose_nonsing_inv ] ;
  rw [ dirichletLap_isSymm G S ]

/-! ### Dirichlet energy and the restriction lemma -/

/-- The **Dirichlet energy** of `f`: `½ ∑_{i∼j} (f i − f j)²`. -/
noncomputable def dirichletEnergy (f : V → ℝ) : ℝ :=
  (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2

/-
The Dirichlet energy equals the Laplacian quadratic form `∑_x f x (L f) x`.
-/
lemma dirichletEnergy_eq_quad (f : V → ℝ) :
    dirichletEnergy G f = ∑ x : V, f x * (G.lapMatrix ℝ *ᵥ f) x := by
  simp +decide [ dirichletEnergy, Matrix.mulVec, dotProduct ];
  simp +decide [ lapMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
  simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.filter_ne', Finset.filter_eq', sub_mul, mul_sub, sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, degMatrix ];
  simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def, Finset.sum_filter, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm ];
  rw [ ← Finset.sum_comm ] ; simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.filter_eq', Finset.filter_ne', Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, diagonal ] ; ring;
  simp +decide [ SimpleGraph.adj_comm ] ; ring

/-
**Restriction lemma.** For `f` supported on `S` and `x ∈ S`, the full Laplacian
applied to `f` agrees with the Dirichlet Laplacian applied to `f` restricted to `S`.
-/
lemma lapMatrix_mulVec_restrict (S : Finset V) (f : V → ℝ)
    (hf : ∀ x, x ∉ S → f x = 0) (x : V) (hx : x ∈ S) :
    (G.lapMatrix ℝ *ᵥ f) x
      = (dirichletLap G S *ᵥ (fun y : S => f (y : V))) ⟨x, hx⟩ := by
  -- Since $f(y) = 0$ for $y \notin S$, the sum over all $y$ can be restricted to $y \in S$.
  have h_sum_restrict : ∑ y : V, (G.lapMatrix ℝ) x y * f y = ∑ y ∈ S, (G.lapMatrix ℝ) x y * f y := by
    rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ] ; aesop;
  convert h_sum_restrict using 1;
  refine' Finset.sum_bij ( fun y _ => y ) _ _ _ _ <;> aesop

/-! ### Positive definiteness and invertibility of `L_S` -/

/-
On a connected graph with nonempty complement, the Dirichlet Laplacian is
positive definite.
-/
lemma dirichletLap_posDef (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty) :
    (dirichletLap G S).PosDef := by
  constructor;
  · convert dirichletLap_isSymm G S using 1;
  · intro x hx_ne_zero
    set ex : V → ℝ := fun w => if hw : w ∈ S then x ⟨w, hw⟩ else 0
    have h_ex_nonzero : ex ≠ 0 := by
      contrapose! hx_ne_zero;
      ext ⟨ w, hw ⟩ ; replace hx_ne_zero := congr_fun hx_ne_zero w ; aesop;
    have h_dirichlet : x.sum (fun i xi => x.sum (fun j xj => star xi * dirichletLap G S i j * xj)) = dirichletEnergy G ex := by
      have h_dirichlet : x.sum (fun i xi => x.sum (fun j xj => star xi * dirichletLap G S i j * xj)) = ∑ i : S, x i * (G.lapMatrix ℝ *ᵥ ex) i := by
        have h_dirichlet : ∀ i : S, (G.lapMatrix ℝ *ᵥ ex) i = (dirichletLap G S *ᵥ x) i := by
          intro i
          generalize_proofs at *; (
          convert lapMatrix_mulVec_restrict G S ex ( fun w hw => by aesop ) i i.2 using 1
          generalize_proofs at *; (
          congr! 2 ; aesop));
        simp_all +decide [ Matrix.mulVec, dotProduct, Finsupp.sum_fintype ];
        simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
      rw [h_dirichlet, dirichletEnergy_eq_quad];
      rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
      · refine' Finset.sum_bij ( fun i hi => i ) _ _ _ _ <;> aesop;
      · aesop
    have h_pos : 0 < dirichletEnergy G ex := by
      by_contra h_contra
      have h_const : ∀ i j : V, G.Reachable i j → ex i = ex j := by
        have h_const : (toLinearMap₂' ℝ (G.lapMatrix ℝ)) ex ex = 0 := by
          convert h_dirichlet using 1;
          · convert dirichletEnergy_eq_quad G ex |> Eq.symm using 1;
            convert Matrix.toLinearMap₂'_apply' _ _ _ using 1;
          · exact Eq.symm ( le_antisymm ( le_of_not_gt h_contra ) ( by exact div_nonneg ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) zero_le_two ) );
        grind +suggestions
      have h_const : ex = 0 := by
        obtain ⟨ z, hz ⟩ := hSc; ext w; specialize h_const w z ( hG w z ) ; aesop;
      contradiction
    linarith [h_dirichlet, h_pos]

/-- The Dirichlet Laplacian is invertible (its determinant is a unit). -/
lemma dirichletLap_isUnit_det (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty) :
    IsUnit (dirichletLap G S).det :=
  (dirichletLap_posDef G hG hSc).det_pos.ne'.isUnit

/-- `L_S · g_S = 1`: the Green function inverts the Dirichlet Laplacian. -/
lemma dirichletLap_mul_greenFn (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty) :
    dirichletLap G S * greenFn G S = 1 :=
  Matrix.mul_nonsing_inv _ (dirichletLap_isUnit_det G hG hSc)

/-! ### Discrete maximum principle -/

/-
In a connected graph, if a property `P` holds at `a` but fails at `b`, then some
edge crosses the boundary of `P`.
-/
lemma exists_adj_boundary (hG : G.Connected) (P : V → Prop) {a b : V}
    (ha : P a) (hb : ¬ P b) : ∃ x y, P x ∧ ¬ P y ∧ G.Adj x y := by
  by_contra h_no_edge;
  have h_reachable : ∀ x, G.Reachable a x → P x := by
    intro x hx
    induction' hx with y hy ih;
    induction' y with y z hy ih;
    · assumption;
    · grind;
  exact hb <| h_reachable b <| hG a b

/-
**Discrete maximum principle.** If `f ≤ 0` off `S` and `f` is subharmonic on `S`
(`(L f) x ≤ 0` for `x ∈ S`), then `f ≤ 0` everywhere, on a connected graph with
nonempty complement.
-/
lemma subharmonic_nonpos (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {f : V → ℝ} (hbd : ∀ x, x ∉ S → f x ≤ 0)
    (hsub : ∀ x, x ∈ S → (G.lapMatrix ℝ *ᵥ f) x ≤ 0) :
    ∀ x, f x ≤ 0 := by
  -- Let `M := Finset.univ.sup' _ f` be the maximum value of `f`, attained at some `x₀` with `f x₀ = M`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x, f x ≤ f x₀ := by
    simpa using Finset.exists_max_image Finset.univ f ( Finset.univ_nonempty_iff.mpr ⟨ Classical.choose hSc ⟩ );
  by_cases hM : f x₀ > 0;
  · obtain ⟨u, w, hu, hw, h_adj⟩ : ∃ u w, f u = f x₀ ∧ f w ≠ f x₀ ∧ G.Adj u w := by
      obtain ⟨z, hz⟩ : ∃ z, z ∈ Sᶜ := hSc;
      have := exists_adj_boundary G hG ( fun w => f w = f x₀ ) ( show f x₀ = f x₀ from rfl ) ( show f z ≠ f x₀ from by linarith [ hbd z ( by simpa using hz ) ] ) ; aesop;
    -- Since `f u = f x₀` and `f x₀ > 0`, we have `u ∈ S`.
    have huS : u ∈ S := by
      exact Classical.not_not.1 fun hu' => by linarith [ hbd u hu' ] ;
    have h_lap : (G.lapMatrix ℝ *ᵥ f) u = (G.degree u : ℝ) * f u - ∑ y ∈ G.neighborFinset u, f y := by
      simp +decide [ lapMatrix, Matrix.mulVec, dotProduct, SimpleGraph.degree, SimpleGraph.neighborFinset ];
      simp +decide [ degMatrix, SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', sub_mul ];
      simp +decide [ diagonal, SimpleGraph.neighborSet ];
    have h_sum_lt : ∑ y ∈ G.neighborFinset u, f y < ∑ y ∈ G.neighborFinset u, f x₀ := by
      apply Finset.sum_lt_sum;
      · aesop;
      · exact ⟨ w, by simpa using h_adj, lt_of_le_of_ne ( hx₀ _ ) hw ⟩;
    simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    linarith [ hsub u huS ];
  · exact fun x => le_trans ( hx₀ x ) ( le_of_not_gt hM )

/-! ### Nonnegativity and the diagonal bound for the Green function -/

/-- The unit-current potential: the `v`-th column of the Green function extended by
`0` off `S` (the electric potential of a unit current injected at `v` and extracted
on the boundary `Sᶜ`). -/
noncomputable def unitPotential (S : Finset V) (v : V) : V → ℝ :=
  fun x => if hx : x ∈ S then (if hv : v ∈ S then greenFn G S ⟨x, hx⟩ ⟨v, hv⟩ else 0)
    else 0

/-- For `x ∈ S`, the unit potential is the Green-function entry. -/
lemma unitPotential_apply_mem {S : Finset V} {v : V} (hv : v ∈ S) {x : V} (hx : x ∈ S) :
    unitPotential G S v x = greenFn G S ⟨x, hx⟩ ⟨v, hv⟩ := by
  simp [unitPotential, hx, hv]

/-
For `x ∈ S`, the Dirichlet Laplacian applied to the unit potential is `e_v`.
-/
lemma lapMatrix_mulVec_unitPotential (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {v : V} (hv : v ∈ S) (x : V) (hx : x ∈ S) :
    (G.lapMatrix ℝ *ᵥ unitPotential G S v) x = (if x = v then 1 else 0) := by
  convert lapMatrix_mulVec_restrict G S ( unitPotential G S v ) _ x hx using 1;
  · convert congr_fun ( congr_fun ( dirichletLap_mul_greenFn G hG hSc ) ⟨ x, hx ⟩ ) ⟨ v, hv ⟩ using 1;
    · rw [ dirichletLap_mul_greenFn G hG hSc ] ; aesop;
    · convert congr_fun ( congr_fun ( dirichletLap_mul_greenFn G hG hSc ) ⟨ x, hx ⟩ ) ⟨ v, hv ⟩ using 1;
      simp +decide [ Matrix.mulVec, dotProduct, unitPotential ];
      simp +decide [ Matrix.mul_apply, hv ];
  · unfold unitPotential; aesop;

/-
**`greenFn_nonneg`.** The Green function is entrywise nonnegative.
-/
theorem greenFn_nonneg (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    (x y : S) : 0 ≤ greenFn G S x y := by
  -- Apply `subharmonic_nonpos` to `f := fun w => - unitPotential G S (y.val) w`
  have h_sub : ∀ w, - (unitPotential G S y w) ≤ 0 := by
    apply subharmonic_nonpos G hG hSc;
    · unfold unitPotential; aesop;
    · intro x hx; have := lapMatrix_mulVec_unitPotential G hG hSc y.prop x hx; simp_all +decide [ Matrix.mulVec ] ;
      simp_all +decide [ dotProduct, Finset.sum_neg_distrib ];
      split_ifs <;> norm_num
  generalize_proofs at *; (
  specialize h_sub x; simp_all +decide [ unitPotential ] ;)

/-
**`green_le_diag`.** `g_S(v,y) ≤ g_S(v,v)`: by the maximum principle the
`v`-column of the Green function is maximised on the diagonal.
-/
theorem green_le_diag (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) (y : S) :
    greenFn G S ⟨v, hv⟩ y ≤ greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
  simp +decide [ green_symm ];
  -- Let $c := \text{unitPotential } G S v v$ and $f := \text{fun } w \mapsto \text{unitPotential } G S v w - c$.
  set c := unitPotential G S v v
  set f : V → ℝ := fun w => unitPotential G S v w - c
  generalize_proofs at *; (
  -- Apply `subharmonic_nonpos` to `f` on `S.erase v`.
  have h_subharmonic : ∀ w, w ∉ S.erase v → f w ≤ 0 := by
    intro w hw; by_cases hwS : w ∈ S <;> simp_all +decide [ sub_nonpos ] ;
    · exact sub_nonpos_of_le ( by aesop );
    · simp +zetaDelta at *;
      unfold unitPotential; simp +decide [ hwS ] ;
      split_ifs ; exact greenFn_nonneg G hG hSc _ _
  have h_subharmonic' : ∀ w, w ∈ S.erase v → (G.lapMatrix ℝ *ᵥ f) w ≤ 0 := by
    intro w hw
    have h_lap : (G.lapMatrix ℝ *ᵥ f) w = (G.lapMatrix ℝ *ᵥ (unitPotential G S v)) w - (G.lapMatrix ℝ *ᵥ (fun _ => c)) w := by
      simp +decide [ f, Matrix.mulVec, dotProduct, sub_mul ];
      simp +decide only [mul_sub, sum_sub_distrib]
    generalize_proofs at *; (
    have h_lap_unitPotential : (G.lapMatrix ℝ *ᵥ (unitPotential G S v)) w = 0 := by
      convert lapMatrix_mulVec_unitPotential G hG hSc hv w ( Finset.mem_of_mem_erase hw ) using 1 ; aesop
    generalize_proofs at *; (
    simp_all +decide [ SimpleGraph.lapMatrix, Matrix.mulVec, dotProduct ];
    simp_all +decide [ degMatrix, Matrix.one_apply, sub_mul ];
    simp_all +decide [ diagonal ];
    simp +decide [ Finset.sum_ite, SimpleGraph.degree, SimpleGraph.neighborFinset_def ]))
  have h_nonpos : ∀ w, f w ≤ 0 := by
    apply subharmonic_nonpos G hG (S := S.erase v) (by
    exact ⟨ v, by aesop ⟩) h_subharmonic h_subharmonic'
  generalize_proofs at *; (
  convert sub_nonpos.mp ( h_nonpos y ) using 1;
  · unfold unitPotential; aesop;
  · grind +locals))

/-! ### The exit time as a Green row-sum, and `g_S(v,v) = R_eff` -/

/-
**`exit_eq_green_weighted`.** The expected exit time is the Green row-sum
weighted by degree: `τ(v) = ∑_{y∈S} g_S(v,y) deg(y)`.
-/
theorem exit_eq_green_weighted (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S) :
    τ v = ∑ y : S, greenFn G S ⟨v, hv⟩ y * (G.degree (y : V) : ℝ) := by
  -- By definition of $τ_S$ and $b$, we have $dirichletLap G S *ᵥ τ_S = b$.
  have h_eq : (dirichletLap G S *ᵥ (fun y : S => τ y.val)) = (fun y : S => (G.degree y.val : ℝ)) := by
    ext ⟨ x, hx ⟩;
    rw [ ← lapMatrix_mulVec_restrict G S τ hτ.1 x hx, hτ.2 x hx ];
  -- By definition of $greenFn$, we have $τ_S = greenFn G S *ᵥ b$.
  have h_inv : (fun y : S => τ y.val) = (greenFn G S *ᵥ (fun y : S => (G.degree y.val : ℝ))) := by
    have h_inv : (dirichletLap G S) * (greenFn G S) = 1 := by
      convert dirichletLap_mul_greenFn G hG hSc using 1;
    rw [ ← h_eq, Matrix.mulVec_mulVec, mul_eq_one_comm.mp h_inv, Matrix.one_mulVec ]
  simpa using congr_fun h_inv ⟨ v, hv ⟩

/-- The **effective resistance** from `v` to the boundary `Sᶜ`: the Dirichlet energy
dissipated by the unit-current potential (Joule's law: energy at unit current = `R`). -/
noncomputable def effResToBoundary (S : Finset V) (v : V) : ℝ :=
  dirichletEnergy G (unitPotential G S v)

/-
**`green_diag_eq_resistance`.** The diagonal of the Green function equals the
effective resistance from `v` to the boundary: `g_S(v,v) = R_eff(v, Sᶜ)`.
-/
theorem green_diag_eq_resistance (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) :
    effResToBoundary G S v = greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
  rw [ effResToBoundary, dirichletEnergy_eq_quad ];
  rw [ Finset.sum_eq_single v ] <;> simp_all +decide [ unitPotential ];
  · rw [ lapMatrix_mulVec_unitPotential G hG hSc hv v hv ] ; aesop;
  · intro b hb h; rw [ lapMatrix_mulVec_unitPotential G hG hSc hv b h ] ; aesop;

/-! ### Step 2: the upper bound `E[τ] ≤ V·R` -/

/-- The **volume** of `S`: the total degree `V(S) = ∑_{x∈S} deg(x)`. -/
def volume (S : Finset V) : ℝ := ∑ x ∈ S, (G.degree x : ℝ)

/-
**Step 2 (upper bound).** `E^v[τ_S] ≤ V(S) · R_eff(v, Sᶜ)`.
-/
theorem exit_le_volume_mul_resistance (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S) :
    τ v ≤ effResToBoundary G S v * volume G S := by
  rw [ exit_eq_green_weighted G hG hSc hτ hv, volume ];
  rw [ green_diag_eq_resistance G hG hSc hv, Finset.mul_sum ];
  -- Since绿图是半个映射索引属于 S 实非负, our intuition equals this sum directly here.
  convert Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_right (green_le_diag G hG hSc hv y) (Nat.cast_nonneg (G.degree (y : V)))) using 1;
  rw [ ← Finset.sum_coe_sort ]

/-! ### Step 3: the lower bound (conditional on local geometry) -/

/-
**Step 3 (lower bound, conditional).**  Given a near-diagonal lower bound on the
Green function on a set `T ⊆ S` (with ratio `c`) and local volume regularity
(`c'·V(S) ≤ ∑_{y∈T} deg(y)`), the exit time is bounded below by
`c·c'·R_eff(v,Sᶜ)·V(S)`.  The two hypotheses are exactly the genuine analytic
inputs of the EIGS local analysis.
-/
theorem exit_ge_volume_mul_resistance (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S)
    {T : Finset V} (hTS : T ⊆ S) {c c' : ℝ} (hc : 0 < c)
    (hnd : ∀ y : V, ∀ hy : y ∈ T,
      c * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ ≤ greenFn G S ⟨v, hv⟩ ⟨y, hTS hy⟩)
    (hvol : c' * volume G S ≤ ∑ y ∈ T, (G.degree y : ℝ)) :
    c * c' * effResToBoundary G S v * volume G S ≤ τ v := by
  rw [ exit_eq_green_weighted G hG hSc hτ hv ];
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( show Finset.image ( fun y : T => ⟨ y, hTS y.2 ⟩ ) Finset.univ ⊆ Finset.univ from Finset.subset_univ _ ) _ );
  · rw [ Finset.sum_image ] <;> norm_num;
    · refine' le_trans _ ( Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right ( hnd _ <| by aesop ) <| Nat.cast_nonneg _ );
      simp_all +decide [ ← Finset.mul_sum _ _ _, green_diag_eq_resistance ];
      convert mul_le_mul_of_nonneg_left hvol ( show 0 ≤ c * greenFn G S ⟨ v, hv ⟩ ⟨ v, hv ⟩ by exact mul_nonneg hc.le ( greenFn_nonneg G hG hSc ⟨ v, hv ⟩ ⟨ v, hv ⟩ ) ) using 1 ; ring!;
      conv_rhs => rw [ ← Finset.sum_attach ] ;
    · exact fun x y h => by aesop;
  · exact fun _ _ _ => mul_nonneg ( greenFn_nonneg G hG hSc _ _ ) ( Nat.cast_nonneg _ )

end EIGS