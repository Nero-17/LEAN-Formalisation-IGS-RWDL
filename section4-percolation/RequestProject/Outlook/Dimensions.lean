import RequestProject.Outlook.EigenN

/-!
# The dimension values `≈ 1.8993` of Subsection 4.2

Since the underlying DHL distance scale is `2`, Subsection 4.2 of arXiv:2603.13798 reads off from
the two Perron roots the values

  `dim_B ⟨Ξ₁⟩₁ = log λ(E(M)) / log 2 ≈ 1.8993`,
  `dim_D ⟨Ξ₁⟩₁ = log λ(E(M)) / log λ(E(N)) ≈ 1.8993`.

With `λ(E(M))` and `λ(E(N)) = 2` verified in `EigenM.lean` and `EigenN.lean`, this file verifies
the numerical value: the two quotients are equal (because `λ(E(N)) = 2`) and lie within `10⁻⁴` of
`1.8993`; in fact `1.89928 < · < 1.89929`.

The logarithm is estimated by interval arithmetic: writing `λ(E(M)) = 4(1 - u)` with
`u ≈ 0.0674`, the Taylor bound `Real.abs_log_sub_add_sum_range_le` for `log (1 - u)` with five
terms, combined with the enclosure `3.7302885 < λ(E(M)) < 3.7302886` and Mathlib's decimal
enclosure of `log 2`, gives `log λ(E(M))` to nine decimal places.
-/

namespace Outlook

open Matrix Reduced

/-- Five-term Taylor bound for `log (1 - u)`. -/
lemma log_one_sub_taylor (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) :
    |Real.log (1 - u) + (u + u^2/2 + u^3/3 + u^4/4 + u^5/5)| ≤ u^6/(1-u) := by
  have habs : |u| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le habs 5
  rw [abs_of_nonneg h0] at h
  simp [Finset.sum_range_succ] at h
  have e : Real.log (1 - u) + (u + u^2/2 + u^3/3 + u^4/4 + u^5/5)
      = u + u ^ 2 / (1 + 1) + u ^ 3 / (2 + 1) + u ^ 4 / (3 + 1) + u ^ 5 / (4 + 1)
        + Real.log (1 - u) := by ring
  rw [e]
  exact h

/-- `log` of a number of the form `4(1 - u)`. -/
lemma log_four_mul (u : ℝ) (hu : u < 1) :
    Real.log (4 * (1 - u)) = 2 * Real.log 2 + Real.log (1 - u) := by
  rw [Real.log_mul (by norm_num) (by linarith), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast
  ring

lemma log_lamM_lb : (1.31648549 : ℝ) < Real.log lamM := by
  have hu : (0:ℝ) ≤ 0.067427875 := by norm_num
  have hu1 : (0.067427875 : ℝ) < 1 := by norm_num
  have htay := log_one_sub_taylor 0.067427875 hu hu1
  rw [abs_le] at htay
  have hnum : (0.067427875 : ℝ) + 0.067427875^2/2 + 0.067427875^3/3 + 0.067427875^4/4
      + 0.067427875^5/5 + 0.067427875^6/(1 - 0.067427875) < 0.0698089 := by norm_num
  have hlog : (1.31648549 : ℝ) < 2 * Real.log 2 + Real.log (1 - 0.067427875) := by
    have h2 := Real.log_two_gt_d9
    linarith [htay.1]
  have hmono : Real.log (4 * (1 - 0.067427875)) ≤ Real.log lamM := by
    apply Real.log_le_log (by norm_num)
    have := lamM_lb
    norm_num
    linarith
  rw [log_four_mul _ hu1] at hmono
  linarith

lemma log_lamM_ub : Real.log lamM < 1.31648573 := by
  have hu : (0:ℝ) ≤ 0.06742785 := by norm_num
  have hu1 : (0.06742785 : ℝ) < 1 := by norm_num
  have htay := log_one_sub_taylor 0.06742785 hu hu1
  rw [abs_le] at htay
  have hnum : (0.0698086 : ℝ) < 0.06742785 + 0.06742785^2/2 + 0.06742785^3/3 + 0.06742785^4/4
      + 0.06742785^5/5 - 0.06742785^6/(1 - 0.06742785) := by norm_num
  have hlog : 2 * Real.log 2 + Real.log (1 - 0.06742785) < 1.31648573 := by
    have h2 := Real.log_two_lt_d9
    linarith [htay.2]
  have hmono : Real.log lamM ≤ Real.log (4 * (1 - 0.06742785)) := by
    apply Real.log_le_log lamM_pos
    have := lamM_ub
    norm_num
    linarith
  rw [log_four_mul _ hu1] at hmono
  linarith

/-! ## The two dimension values -/

/-- The box dimension value of Subsection 4.2: `log λ(E(M)) / log 2`. -/
noncomputable def dimBox : ℝ := Real.log (specRad (EM (pc : ℂ))) / Real.log 2

/-- The degree dimension value of Subsection 4.2: `log λ(E(M)) / log λ(E(N))`. -/
noncomputable def dimDeg : ℝ :=
  Real.log (specRad (EM (pc : ℂ))) / Real.log (specRad (EN (pc : ℂ)))

/-- The two dimension values coincide, because `λ(E(N)) = 2`. -/
theorem dimDeg_eq_dimBox : dimDeg = dimBox := by
  unfold dimDeg dimBox
  rw [specRad_EN]

/-- Sharp enclosure of the common value: `1.89928 < log λ(E(M)) / log 2 < 1.89929`. -/
theorem dimBox_enclosure : 1.89928 < dimBox ∧ dimBox < 1.89929 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  unfold dimBox
  rw [specRad_EM]
  constructor
  · rw [lt_div_iff₀ hlog2]
    nlinarith [log_lamM_lb]
  · rw [div_lt_iff₀ hlog2]
    nlinarith [log_lamM_ub]

/-- **The value quoted in Subsection 4.2**: `dim_B = log λ(E(M)) / log 2 ≈ 1.8993`. -/
theorem dimBox_approx : |dimBox - 1.8993| < 1e-4 := by
  have h := dimBox_enclosure
  rw [abs_lt]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- **The value quoted in Subsection 4.2**: `dim_D = log λ(E(M)) / log λ(E(N)) ≈ 1.8993`. -/
theorem dimDeg_approx : |dimDeg - 1.8993| < 1e-4 := by
  rw [dimDeg_eq_dimBox]
  exact dimBox_approx

/-- **All the numerical claims of Subsection 4.2**, at the critical parameter `p = p_c`:
the spectral radius of the mean offspring matrix `E(M)` is `≈ 3.7303`, that of the mean boundary
matrix `E(N)` is exactly `2`, and the resulting dimension values
`log λ(E(M)) / log 2 = log λ(E(M)) / log λ(E(N))` are `≈ 1.8993`. -/
theorem section42_numerics :
    |specRad (EM (pc : ℂ)) - 3.7303| < 1e-4 ∧ specRad (EN (pc : ℂ)) = 2 ∧
      dimDeg = dimBox ∧ |dimBox - 1.8993| < 1e-4 := by
  refine ⟨?_, specRad_EN, dimDeg_eq_dimBox, dimBox_approx⟩
  rw [specRad_EM]
  exact lamM_approx

end Outlook
