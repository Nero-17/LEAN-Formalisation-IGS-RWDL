import RequestProject.Section32.PointBoundary

/-!
# §3.2: a worked instance of Lemma `sec32_point_boundary`

The hypotheses collected in `PointBoundaryHyp` are abstract, so they are checked
here on a concrete model, to make sure the lemma is not vacuous: the dyadic
points of the real line, with

* cells `Λ = (m, k)` the dyadic intervals `[k2^{-m}, (k+1)2^{-m}]`,
* terminals `a_Λ = k2^{-m}`, `b_Λ = (k+1)2^{-m}`,
* resistance `R(x,y) = |x-y|` (the resistance metric of the unit interval, i.e.
  of the rule graph "path", for which `ρ(Ψ) = 2`),
* height `h_Λ(z) = d(z) - m`, where `2^{-d(z)}` is the coarsest dyadic scale
  containing `z`.

This is the one-dimensional case of the situation of §3.2, and all the
hypotheses hold with `ρ = 2`, `A₀ = 1`, `B = 1`, so that the lemma gives
`|z - a_Λ| ≤ 2 · 2^{-m}` for every dyadic `z ∈ Λ` (the true value being
`2^{-m}`).
-/

namespace IGS.Sec32.Dyadic

open scoped Classical

/-- The dyadic points of `ℝ`. -/
def Dy : Set ℝ := {x | ∃ (n : ℕ) (j : ℤ), x = (j : ℝ) / 2 ^ n}

/-- The coarsest dyadic scale containing a dyadic point. -/
noncomputable def minExp (z : Dy) : ℕ := Nat.find z.2

theorem minExp_spec (z : Dy) : ∃ j : ℤ, (z : ℝ) = (j : ℝ) / 2 ^ minExp z := Nat.find_spec z.2

/-- A dyadic point of scale at most `2^{-m}` has an integer numerator at scale `m`. -/
theorem exists_num_of_minExp_le {z : Dy} {m : ℕ} (h : minExp z ≤ m) :
    ∃ j : ℤ, (z : ℝ) = (j : ℝ) / 2 ^ m := by
  obtain ⟨j, hj⟩ := minExp_spec z
  refine ⟨j * 2 ^ (m - minExp z), ?_⟩
  have hsplit : (2 : ℝ) ^ m = 2 ^ minExp z * 2 ^ (m - minExp z) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2 : ℝ) ^ minExp z ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (m - minExp z) ≠ 0 := by positivity
  rw [hj, hsplit]
  push_cast
  field_simp

/-- The cell data of the dyadic model. -/
noncomputable def cellData : CellData Dy (ℕ × ℤ) where
  lev Λ := Λ.1
  termA Λ := ⟨(Λ.2 : ℝ) / 2 ^ Λ.1, ⟨Λ.1, Λ.2, rfl⟩⟩
  termB Λ := ⟨((Λ.2 : ℝ) + 1) / 2 ^ Λ.1, ⟨Λ.1, Λ.2 + 1, by push_cast; ring_nf⟩⟩
  mem z Λ := (Λ.2 : ℝ) / 2 ^ Λ.1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((Λ.2 : ℝ) + 1) / 2 ^ Λ.1
  ht z Λ := minExp z - Λ.1

/-- The resistance of the dyadic model: the euclidean distance. -/
noncomputable def Rdy (x y : Dy) : ℝ := |(x : ℝ) - (y : ℝ)|

@[simp] theorem lev_eq (Λ : ℕ × ℤ) : cellData.lev Λ = Λ.1 := rfl

@[simp] theorem ht_eq (z : Dy) (Λ : ℕ × ℤ) : cellData.ht z Λ = minExp z - Λ.1 := rfl

@[simp] theorem termA_val (Λ : ℕ × ℤ) : ((cellData.termA Λ : Dy) : ℝ) = (Λ.2 : ℝ) / 2 ^ Λ.1 := rfl

@[simp] theorem termB_val (Λ : ℕ × ℤ) :
    ((cellData.termB Λ : Dy) : ℝ) = ((Λ.2 : ℝ) + 1) / 2 ^ Λ.1 := rfl

theorem mem_iff (z : Dy) (Λ : ℕ × ℤ) :
    cellData.mem z Λ ↔ (Λ.2 : ℝ) / 2 ^ Λ.1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((Λ.2 : ℝ) + 1) / 2 ^ Λ.1 :=
  Iff.rfl

/-- All the hypotheses of Lemma `sec32_point_boundary` hold in the dyadic model,
with `ρ = 2`, `A₀ = 1` and `B = 1`. -/
theorem pointBoundaryHyp_dyadic : PointBoundaryHyp cellData Rdy 2 1 1 := by
  constructor
  · intro x; simp [Rdy]
  · intro x y z; simpa [Rdy] using abs_sub_le (x : ℝ) (y : ℝ) (z : ℝ)
  · intro Λ
    have hpow : (0 : ℝ) < 2 ^ Λ.1 := by positivity
    rw [Rdy]
    simp only [termA_val, termB_val, div_sub_div_same, abs_div, abs_of_pos hpow, lev_eq]
    simp
  · intro Λ
    have hpow : (0 : ℝ) < 2 ^ Λ.1 := by positivity
    rw [Rdy]
    simp only [termA_val, termB_val, div_sub_div_same, abs_div, abs_of_pos hpow, lev_eq]
    rw [show (Λ.2 : ℝ) + 1 - Λ.2 = 1 by ring]
    simp
  · -- a point of height `0` is a terminal
    rintro z Λ ⟨hz1, hz2⟩ h0
    rw [ht_eq] at h0
    have hle : minExp z ≤ Λ.1 := by omega
    obtain ⟨j, hj⟩ := exists_num_of_minExp_le hle
    have hpow : (0 : ℝ) < 2 ^ Λ.1 := by positivity
    rw [hj] at hz1 hz2
    have hk : (Λ.2 : ℝ) ≤ (j : ℝ) := by
      rw [div_le_div_iff_of_pos_right hpow] at hz1; exact hz1
    have hk' : (j : ℝ) ≤ (Λ.2 : ℝ) + 1 := by
      rw [div_le_div_iff_of_pos_right hpow] at hz2; exact hz2
    have hk1 : Λ.2 ≤ j := by exact_mod_cast hk
    have hk2 : j ≤ Λ.2 + 1 := by
      have : ((j : ℤ) : ℝ) ≤ ((Λ.2 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    rcases eq_or_lt_of_le hk1 with heq | hlt
    · left
      apply Subtype.ext
      rw [hj, termA_val, ← heq]
    · right
      have hj1 : j = Λ.2 + 1 := by omega
      apply Subtype.ext
      rw [hj, termB_val, hj1]
      push_cast
      ring
  · -- a point of positive height lies in a half of the cell
    rintro z Λ L ⟨hz1, hz2⟩ hL h0
    obtain ⟨m, k⟩ := Λ
    simp only at hz1 hz2
    have hpow : (0 : ℝ) < 2 ^ m := by positivity
    have hpow' : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have hsplit : (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
    have hhalf : ((2 * k : ℤ) : ℝ) / 2 ^ (m + 1) = (k : ℝ) / 2 ^ m := by
      push_cast
      rw [hsplit]
      field_simp
    have hhalf' : (((2 * k : ℤ) : ℝ) + 1 + 1) / 2 ^ (m + 1) = ((k : ℝ) + 1) / 2 ^ m := by
      push_cast
      rw [hsplit]
      field_simp
      ring
    have hht : minExp z - (m + 1) ≤ L := by
      rw [ht_eq] at hL h0
      simp only at hL h0
      omega
    have hmidA : ((2 * k : ℤ) : ℝ) + 1 = ((2 * k + 1 : ℤ) : ℝ) := by push_cast; ring
    by_cases hmid : (z : ℝ) ≤ (((2 * k : ℤ) : ℝ) + 1) / 2 ^ (m + 1)
    · -- left child
      refine ⟨(m + 1, 2 * k), ⟨?_, hmid⟩, rfl, by simpa using hht, ?_, ?_⟩
      · show ((2 * k : ℤ) : ℝ) / 2 ^ (m + 1) ≤ (z : ℝ)
        rw [hhalf]; exact hz1
      · rw [Rdy]
        simp only [termA_val, lev_eq]
        rw [hhalf]
        simp
      · rw [Rdy]
        simp only [termB_val, lev_eq]
        have hval : (((2 * k : ℤ) : ℝ) + 1) / 2 ^ (m + 1) - ((k : ℝ) + 1) / 2 ^ m
            = -(1 / 2 ^ (m + 1)) := by
          push_cast
          rw [hsplit]
          field_simp
          ring
        rw [hval, abs_neg, abs_of_pos (by positivity), one_mul, hsplit]
        rw [div_le_iff₀ (by positivity)]
        field_simp
        linarith
    · -- right child
      push_neg at hmid
      refine ⟨(m + 1, 2 * k + 1), ⟨?_, ?_⟩, rfl, by simpa using hht, ?_, ?_⟩
      · show ((2 * k + 1 : ℤ) : ℝ) / 2 ^ (m + 1) ≤ (z : ℝ)
        rw [← hmidA]
        exact le_of_lt hmid
      · show (z : ℝ) ≤ (((2 * k + 1 : ℤ) : ℝ) + 1) / 2 ^ (m + 1)
        rw [← hmidA, hhalf']
        exact hz2
      · rw [Rdy]
        simp only [termA_val, lev_eq]
        have hval : ((2 * k + 1 : ℤ) : ℝ) / 2 ^ (m + 1) - (k : ℝ) / 2 ^ m = 1 / 2 ^ (m + 1) := by
          push_cast
          rw [hsplit]
          field_simp
          ring
        rw [hval, abs_of_pos (by positivity), one_mul, hsplit, div_le_iff₀ (by positivity)]
        field_simp
        linarith
      · rw [Rdy]
        simp only [termB_val, lev_eq]
        rw [show (((2 * k + 1 : ℤ) : ℝ) + 1) = ((2 * k : ℤ) : ℝ) + 1 + 1 by push_cast; ring,
          hhalf']
        simp

/--
**Lemma `sec32_point_boundary` in the dyadic model.**
Every dyadic point of a level-`m` dyadic interval is at resistance at most
`2 · 2^{-m}` from either endpoint.  (The optimal constant here is `1`; the lemma
gives `C_∂ = max(A₀, Bρ/(ρ-1)) = 2`.)
-/
theorem dyadic_point_boundary (Λ : ℕ × ℤ) (z : Dy) (hz : cellData.mem z Λ) :
    Rdy z (cellData.termA Λ) ≤ 2 * (2 ^ Λ.1)⁻¹ ∧
    Rdy z (cellData.termB Λ) ≤ 2 * (2 ^ Λ.1)⁻¹ := by
  have hC : boundaryConst 2 1 1 = 2 := by
    rw [boundaryConst]
    norm_num
  have h := point_boundary pointBoundaryHyp_dyadic (by norm_num) (by norm_num)
    (cellData.ht z Λ) Λ z hz le_rfl
  rw [hC, lev_eq] at h
  exact h

end IGS.Sec32.Dyadic
