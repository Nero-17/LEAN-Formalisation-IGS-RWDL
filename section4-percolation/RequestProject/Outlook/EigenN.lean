import RequestProject.Outlook.EigenM

/-!
# The Perron root `λ(E(N)) = 2`

At the critical parameter `p = p_c = (√5 - 1)/2`, Subsection 4.2 of arXiv:2603.13798 records the
value `λ(E(N)) = 2` for the Perron root of the live block of the mean boundary matrix `E(N)`.

The live `6 × 6` block of `E(N)` splits, after separating the odd and the even indices, into the two
`3 × 3` blocks `ENodd` and `ENeven`, whose characteristic polynomials are

* `(t - 2)·(t² + (8p - 6)·t + (20p - 12))`  (`det_char_ENodd`),
* `(t - 2p)·(t² + (6p - 6)·t + (8p - 4))`   (`det_char_ENeven`).

Hence `2` is an eigenvalue, and all the remaining roots are of modulus `< 2`; we prove:

* `two_hasEig_EN` — `2` is an eigenvalue of `E(N)`;
* `hasEig_EN_norm_le` — every complex eigenvalue `z` of `E(N)` satisfies `‖z‖ ≤ 2`;
* `lamN_isGreatest` — consequently the spectral radius of `E(N)` is exactly `2`.
-/

namespace Outlook

open Matrix Reduced

/-- If a real monic quadratic is positive at `±2` in the strong sense below, then all its complex
roots have modulus at most `2`. -/
lemma abs_root_le_two (b c : ℝ) (hb : -4 < b) (hb' : b < 4) (h1 : 0 < 4 + 2*b + c)
    (h2 : 0 < 4 - 2*b + c) (hc : c ≤ 4) (z : ℂ) (hz : z^2 + (b : ℂ)*z + (c : ℂ) = 0) :
    ‖z‖ ≤ 2 := by
  rcases quad_root_cases b c z hz with ⟨x, hx, hroot⟩ | habs
  · rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · by_contra hcon
      push_neg at hcon
      have hxlt : x < -2 := by linarith
      nlinarith [mul_pos (show (0:ℝ) < -(x + 2) by linarith) (show (0:ℝ) < -(x + b - 2) by linarith)]
    · by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos (show (0:ℝ) < x - 2 by linarith) (show (0:ℝ) < x + b + 2 by linarith)]
  · nlinarith [habs, norm_nonneg z]

/-! ## The characteristic polynomials at the critical parameter -/

lemma det_char_ENodd_pc (z : ℂ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - ENodd (pc : ℂ)).det
      = (z - 2) * (z^2 + (8*(pc:ℂ) - 6)*z + (20*(pc:ℂ) - 12)) :=
  det_char_ENodd (pc : ℂ) z pc_sq_complex

lemma det_char_ENeven_pc (z : ℂ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - ENeven (pc : ℂ)).det
      = (z - 2*(pc:ℂ)) * (z^2 + (6*(pc:ℂ) - 6)*z + (8*(pc:ℂ) - 4)) :=
  det_char_ENeven (pc : ℂ) z pc_sq_complex

/-! ## `2` is an eigenvalue of `E(N)` -/

/-- `2` is an eigenvalue of the mean boundary matrix `E(N)` at the critical parameter. -/
theorem two_hasEig_EN : HasEig (EN (pc : ℂ)) 2 := by
  apply hasEig_ENlive_EN
  apply hasEig_ENodd_ENlive
  rw [hasEig_iff_det, det_char_ENodd_pc]
  simp

/-! ## `2` dominates the spectrum -/

/-- Every complex eigenvalue of `E(N)` at the critical parameter has modulus at most `2`. -/
theorem hasEig_EN_norm_le (z : ℂ) (hz : HasEig (EN (pc : ℂ)) z) : ‖z‖ ≤ 2 := by
  have hlb := pc_lb
  have hub := pc_ub
  rcases hasEig_EN_live _ _ hz with h0 | hlive
  · simp [h0]
  rcases hasEig_ENlive_split _ _ hlive with hodd | heven
  · rw [hasEig_iff_det, det_char_ENodd_pc] at hodd
    rcases mul_eq_zero.mp hodd with h | h
    · have : z = 2 := by linear_combination h
      simp [this]
    · refine abs_root_le_two (8*pc - 6) (20*pc - 12) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) z ?_
      push_cast
      linear_combination h
  · rw [hasEig_iff_det, det_char_ENeven_pc] at heven
    rcases mul_eq_zero.mp heven with h | h
    · have hz2 : z = ((2*pc : ℝ) : ℂ) := by
        have := sub_eq_zero.mp h
        rw [this]
        push_cast
        ring
      rw [hz2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    · refine abs_root_le_two (6*pc - 6) (8*pc - 4) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) z ?_
      push_cast
      linear_combination h

/-- **`λ(E(N)) = 2`**: the spectral radius of the mean boundary matrix `E(N)` at the critical
parameter is exactly `2`. -/
theorem lamN_isGreatest :
    IsGreatest {r : ℝ | ∃ z : ℂ, HasEig (EN (pc : ℂ)) z ∧ ‖z‖ = r} 2 := by
  constructor
  · exact ⟨2, two_hasEig_EN, by norm_num⟩
  · rintro r ⟨z, hz, rfl⟩
    exact hasEig_EN_norm_le z hz

@[simp] theorem specRad_EN : specRad (EN (pc : ℂ)) = 2 :=
  specRad_eq_of_isGreatest lamN_isGreatest

end Outlook
