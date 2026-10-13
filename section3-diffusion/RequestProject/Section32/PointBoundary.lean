import Mathlib

/-!
# §3.2, step 2: Lemma `sec32_point_boundary`

*Iterated Graph Systems (I)* (arXiv:2603.13798), Lemma `sec32_point_boundary`:
there is `C_∂ > 0` such that for every level-`m` cell `Λ` with terminals
`a_Λ, b_Λ` and every `z ∈ 𝒱 ∩ Λ`,
`R_*(z, a_Λ) ≤ C_∂ ρ(Ψ)^{-m}` and `R_*(z, b_Λ) ≤ C_∂ ρ(Ψ)^{-m}`.

The paper's proof is an induction on the *height* `h_Λ(z)`, the least `ℓ` such
that `z` is a terminal of a level-`(m+ℓ)` descendant cell of `Λ`:

* height `0`: `z` is a terminal of `Λ`, and the resistance between the two
  terminals of a level-`m` cell of colour `i` is `ρ(Ψ)^{-m}[v]_i ≤ A₀ρ(Ψ)^{-m}`;
* height `L+1`: pick a first-generation child `Λ' ∋ z`, use the triangle
  inequality `R_*(z,a_Λ) ≤ R_*(z,a_{Λ'}) + R_*(a_{Λ'},a_Λ)` and the fact that
  only finitely many first-generation configurations occur, so that
  `R_*(a_{Λ'},a_Λ) ≤ B ρ(Ψ)^{-m}`.

This gives `A_{L+1} ≤ ρ(Ψ)^{-1}A_L + B`, and `ρ(Ψ) > 1` makes the sequence
bounded.  The whole argument is carried out below.  The two inputs it takes from
elsewhere in the paper are hypotheses here: that `R_*` satisfies the triangle
inequality (the resistance-metric axioms, cited from Kigami) and the level-`m`
terminal-to-terminal resistance `ρ(Ψ)^{-m}[v]_i` (§2).

Instead of taking a supremum `A_L` (whose finiteness is what is being proved),
the induction is run directly against the explicit constant
`C_∂ = max(A₀, Bρ/(ρ-1))`, which is exactly the fixed point of the recursion.
-/

namespace IGS.Sec32

variable {𝒱 : Type*} {Cell : Type*}

/-- The combinatorial data attached to the cells of `Ξ`: level, the two
terminals, membership of a point in a cell, and the height of a point in a cell. -/
structure CellData (𝒱 Cell : Type*) where
  /-- the level `m` of a cell -/
  lev : Cell → ℕ
  /-- the first terminal `a_Λ` -/
  termA : Cell → 𝒱
  /-- the second terminal `b_Λ` -/
  termB : Cell → 𝒱
  /-- `z` belongs to the cell -/
  mem : 𝒱 → Cell → Prop
  /-- the height `h_Λ(z)` -/
  ht : 𝒱 → Cell → ℕ

/--
The hypotheses of Lemma `sec32_point_boundary`, with `R` the renormalised
resistance, `rho = ρ(Ψ)`, `A₀ = max_i [v]_i` and `B` the first-generation
constant.
-/
structure PointBoundaryHyp (S : CellData 𝒱 Cell) (R : 𝒱 → 𝒱 → ℝ) (rho A0 B : ℝ) : Prop where
  /-- `R` vanishes on the diagonal -/
  self : ∀ x, R x x = 0
  /-- `R` obeys the triangle inequality (resistance-metric axiom, Kigami) -/
  tri : ∀ x y z, R x z ≤ R x y + R y z
  /-- the terminal-to-terminal resistance of a level-`m` cell is `≤ A₀ρ^{-m}` (§2) -/
  terminals : ∀ Λ : Cell, R (S.termA Λ) (S.termB Λ) ≤ A0 * (rho ^ S.lev Λ)⁻¹
  /-- the same bound with the terminals interchanged -/
  terminals' : ∀ Λ : Cell, R (S.termB Λ) (S.termA Λ) ≤ A0 * (rho ^ S.lev Λ)⁻¹
  /-- a point of height `0` in `Λ` is one of the two terminals of `Λ` -/
  height_zero : ∀ z Λ, S.mem z Λ → S.ht z Λ = 0 → z = S.termA Λ ∨ z = S.termB Λ
  /-- a point of positive height lies in a first-generation child of strictly smaller
  height, whose terminals are close to those of the parent -/
  child : ∀ (z : 𝒱) (Λ : Cell) (L : ℕ), S.mem z Λ → S.ht z Λ ≤ L + 1 → S.ht z Λ ≠ 0 →
    ∃ Λ' : Cell, S.mem z Λ' ∧ S.lev Λ' = S.lev Λ + 1 ∧ S.ht z Λ' ≤ L ∧
      R (S.termA Λ') (S.termA Λ) ≤ B * (rho ^ S.lev Λ)⁻¹ ∧
      R (S.termB Λ') (S.termB Λ) ≤ B * (rho ^ S.lev Λ)⁻¹

/-- The constant of the lemma: the fixed point of `A ↦ ρ⁻¹A + B`, raised to at
least `A₀`. -/
noncomputable def boundaryConst (rho A0 B : ℝ) : ℝ := max A0 (B * rho / (rho - 1))

theorem boundaryConst_nonneg {rho A0 B : ℝ} (hA0 : 0 ≤ A0) : 0 ≤ boundaryConst rho A0 B :=
  le_trans hA0 (le_max_left _ _)

theorem le_boundaryConst (rho A0 B : ℝ) : A0 ≤ boundaryConst rho A0 B := le_max_left _ _

/-- `C_∂` really is a fixed point: `ρ⁻¹ C_∂ + B ≤ C_∂` when `ρ > 1`. -/
theorem boundaryConst_step {rho A0 B : ℝ} (hrho : 1 < rho) :
    rho⁻¹ * boundaryConst rho A0 B + B ≤ boundaryConst rho A0 B := by
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho
  have hsub : 0 < rho - 1 := by linarith
  set C := boundaryConst rho A0 B with hC
  have hKB : B * rho / (rho - 1) ≤ C := le_max_right _ _
  have h1 : B * rho ≤ C * (rho - 1) := by
    rw [div_le_iff₀ hsub] at hKB
    linarith
  have h2 : rho⁻¹ * C + B - C = (B * rho - C * (rho - 1)) / rho := by
    field_simp
    ring
  have h3 : rho⁻¹ * C + B - C ≤ 0 := by
    rw [h2]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hrho0.le
  linarith

/--
**Lemma `sec32_point_boundary`.**
Under the hypotheses above, for every cell `Λ` of level `m` and every point
`z ∈ Λ` (of any finite height),
`R(z, a_Λ) ≤ C_∂ ρ^{-m}` and `R(z, b_Λ) ≤ C_∂ ρ^{-m}`,
with the explicit constant `C_∂ = max(A₀, Bρ/(ρ-1))`.
-/
theorem point_boundary {S : CellData 𝒱 Cell} {R : 𝒱 → 𝒱 → ℝ} {rho A0 B : ℝ}
    (h : PointBoundaryHyp S R rho A0 B) (hrho : 1 < rho) (hA0 : 0 ≤ A0) :
    ∀ (L : ℕ) (Λ : Cell) (z : 𝒱), S.mem z Λ → S.ht z Λ ≤ L →
      R z (S.termA Λ) ≤ boundaryConst rho A0 B * (rho ^ S.lev Λ)⁻¹ ∧
      R z (S.termB Λ) ≤ boundaryConst rho A0 B * (rho ^ S.lev Λ)⁻¹ := by
  have hrho0 : (0 : ℝ) < rho := lt_trans zero_lt_one hrho
  set C := boundaryConst rho A0 B with hC
  have hCnn : 0 ≤ C := boundaryConst_nonneg hA0
  have hA0C : A0 ≤ C := le_boundaryConst rho A0 B
  have hstep : rho⁻¹ * C + B ≤ C := boundaryConst_step hrho
  -- the base case, valid at every level
  have hbase : ∀ (Λ : Cell) (z : 𝒱), S.mem z Λ → S.ht z Λ = 0 →
      R z (S.termA Λ) ≤ C * (rho ^ S.lev Λ)⁻¹ ∧
      R z (S.termB Λ) ≤ C * (rho ^ S.lev Λ)⁻¹ := by
    intro Λ z hz h0
    have hpow : (0 : ℝ) < (rho ^ S.lev Λ)⁻¹ := by positivity
    have hmono : A0 * (rho ^ S.lev Λ)⁻¹ ≤ C * (rho ^ S.lev Λ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hA0C hpow.le
    have hzero : (0 : ℝ) ≤ C * (rho ^ S.lev Λ)⁻¹ := by positivity
    rcases h.height_zero z Λ hz h0 with rfl | rfl
    · exact ⟨by rw [h.self]; exact hzero, le_trans (h.terminals Λ) hmono⟩
    · exact ⟨le_trans (h.terminals' Λ) hmono, by rw [h.self]; exact hzero⟩
  intro L
  induction L with
  | zero =>
      intro Λ z hz hL
      exact hbase Λ z hz (Nat.le_zero.mp hL)
  | succ n ih =>
      intro Λ z hz hL
      by_cases h0 : S.ht z Λ = 0
      · exact hbase Λ z hz h0
      obtain ⟨Λ', hzΛ', hlev, hht, haa, hbb⟩ := h.child z Λ n hz hL h0
      obtain ⟨hA, hB⟩ := ih Λ' z hzΛ' hht
      have hpow : (0 : ℝ) < (rho ^ S.lev Λ)⁻¹ := by positivity
      have hlevpow : ((rho ^ S.lev Λ') : ℝ)⁻¹ = rho⁻¹ * (rho ^ S.lev Λ)⁻¹ := by
        rw [hlev, pow_succ]
        field_simp
      have key : ∀ w w' : 𝒱, R z w' ≤ C * (rho ^ S.lev Λ')⁻¹ →
          R w' w ≤ B * (rho ^ S.lev Λ)⁻¹ → R z w ≤ C * (rho ^ S.lev Λ)⁻¹ := by
        intro w w' h1 h2
        have := h.tri z w' w
        have hsum : R z w ≤ C * (rho ^ S.lev Λ')⁻¹ + B * (rho ^ S.lev Λ)⁻¹ := by
          linarith
        have hrewrite : C * (rho ^ S.lev Λ')⁻¹ + B * (rho ^ S.lev Λ)⁻¹
            = (rho⁻¹ * C + B) * (rho ^ S.lev Λ)⁻¹ := by
          rw [hlevpow]; ring
        have hfinal : (rho⁻¹ * C + B) * (rho ^ S.lev Λ)⁻¹ ≤ C * (rho ^ S.lev Λ)⁻¹ :=
          mul_le_mul_of_nonneg_right hstep hpow.le
        linarith [hsum, hrewrite ▸ hsum]
      exact ⟨key _ _ hA haa, key _ _ hB hbb⟩

/--
The form in which the lemma is used later: the resistance from a point of a
level-`m` cell to either terminal tends to `0` uniformly as `m → ∞`.
-/
theorem point_boundary_tendsto {S : CellData 𝒱 Cell} {R : 𝒱 → 𝒱 → ℝ} {rho A0 B : ℝ}
    (h : PointBoundaryHyp S R rho A0 B) (hrho : 1 < rho) (hA0 : 0 ≤ A0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ m₀ : ℕ, ∀ (Λ : Cell) (z : 𝒱), m₀ ≤ S.lev Λ → S.mem z Λ → (∃ L, S.ht z Λ ≤ L) →
      R z (S.termA Λ) < eps ∧ R z (S.termB Λ) < eps := by
  classical
  set C := boundaryConst rho A0 B with hC
  have hCnn : 0 ≤ C := boundaryConst_nonneg hA0
  have hrho0 : (0 : ℝ) < rho := lt_trans zero_lt_one hrho
  -- choose `m₀` with `C ρ^{-m₀} < eps`
  obtain ⟨m₀, hm₀⟩ : ∃ m : ℕ, C < eps * rho ^ m := by
    have hpow : Filter.Tendsto (fun m : ℕ => eps * rho ^ m) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps (tendsto_pow_atTop_atTop_of_one_lt hrho)
    obtain ⟨m, hm⟩ := (hpow.eventually_gt_atTop C).exists
    exact ⟨m, hm⟩
  refine ⟨m₀, ?_⟩
  rintro Λ z hlev hz ⟨L, hL⟩
  obtain ⟨hA, hB⟩ := point_boundary h hrho hA0 L Λ z hz hL
  have hpowmono : (rho : ℝ) ^ m₀ ≤ rho ^ S.lev Λ := pow_le_pow_right₀ hrho.le hlev
  have hpowpos : (0 : ℝ) < rho ^ S.lev Λ := by positivity
  have hlt : C * (rho ^ S.lev Λ)⁻¹ < eps := by
    rw [mul_inv_lt_iff₀ hpowpos]
    calc C < eps * rho ^ m₀ := hm₀
      _ ≤ eps * rho ^ S.lev Λ := by nlinarith
  exact ⟨lt_of_le_of_lt hA hlt, lt_of_le_of_lt hB hlt⟩

end IGS.Sec32
