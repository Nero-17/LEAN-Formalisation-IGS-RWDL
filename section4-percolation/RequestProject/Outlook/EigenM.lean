import RequestProject.Outlook.Matrices
import RequestProject.Reduced.Params

/-!
# The Perron root `λ(E(M)) ≈ 3.7303`

At the critical parameter `p = p_c = (√5 - 1)/2` (so that `p_c² = 1 - p_c`), Subsection 4.2 of
arXiv:2603.13798 records the numerical value `λ(E(M)) ≈ 3.7303` for the Perron root of the live
block of the mean offspring matrix `E(M)`.

Here we verify this rigorously.  The characteristic polynomial of the live block factors as
`(t - (4 - 4p))·(t² - (10 - 8p)·t + 8p)` (`det_char_EMlive`), so the eigenvalue in question is the
larger root of the quadratic,

  `λ(E(M)) = (10 - 8p_c + √(164 - 256 p_c))/2 = 7 - 2√5 + √(73 - 32√5)`,

and we prove:

* `lamM_hasEig` — `λ(E(M))` is an eigenvalue of `E(M)`;
* `hasEig_EM_norm_le` — every complex eigenvalue `z` of `E(M)` satisfies `‖z‖ ≤ λ(E(M))`
  (so `λ(E(M))` is the spectral radius of `E(M)`);
* `lamM_unique` — `λ(E(M))` is the *unique* eigenvalue of `E(M)` that is real and `≥ 2`;
* `lamM_approx` — `|λ(E(M)) - 3.7303| < 10⁻⁴`, together with the sharper enclosure
  `3.7302885 < λ(E(M)) < 3.7302886`.
-/

namespace Outlook

open Matrix Reduced

/-! ## Numerical enclosures -/

lemma sqrt5_lb : (2.236067977 : ℝ) < Real.sqrt 5 := by
  have h : (2.236067977 : ℝ) ^ 2 < 5 := by norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

lemma sqrt5_ub : Real.sqrt 5 < 2.236067978 := by
  have h : (5 : ℝ) < (2.236067978 : ℝ) ^ 2 := by norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

lemma pc_lb : (0.6180339885 : ℝ) < pc := by
  have := sqrt5_lb
  unfold pc
  linarith

lemma pc_ub : pc < 0.618033989 := by
  have := sqrt5_ub
  unfold pc
  linarith

/-- The discriminant of the relevant quadratic. -/
noncomputable def discM : ℝ := 164 - 256 * pc

lemma discM_nonneg : 0 ≤ discM := by
  have := pc_ub
  unfold discM
  linarith

lemma discM_lb : (5.7832988 : ℝ) < discM := by
  have := pc_ub
  unfold discM
  linarith

lemma discM_ub : discM < 5.783299 := by
  have := pc_lb
  unfold discM
  linarith

lemma sqrt_discM_lb : (2.4048490 : ℝ) < Real.sqrt discM := by
  have h : (2.4048490 : ℝ) ^ 2 < discM := by
    have h' : (2.4048490 : ℝ) ^ 2 < 5.7832988 := by norm_num
    linarith [discM_lb]
  nlinarith [Real.sq_sqrt discM_nonneg, Real.sqrt_nonneg discM]

lemma sqrt_discM_ub : Real.sqrt discM < 2.4048491 := by
  have h : discM < (2.4048491 : ℝ) ^ 2 := by
    have h' : (5.783299 : ℝ) < (2.4048491 : ℝ) ^ 2 := by norm_num
    linarith [discM_ub]
  nlinarith [Real.sq_sqrt discM_nonneg, Real.sqrt_nonneg discM]

/-! ## The two roots of the quadratic factor -/

/-- The Perron root `λ(E(M))` of the live block of the mean offspring matrix `E(M)`: the larger
root of `t² - (10 - 8p_c)·t + 8p_c`. -/
noncomputable def lamM : ℝ := (10 - 8 * pc + Real.sqrt discM) / 2

/-- The smaller root of the quadratic factor of the characteristic polynomial of `E(M)`. -/
noncomputable def muM : ℝ := (10 - 8 * pc - Real.sqrt discM) / 2

/-- The closed form of `λ(E(M))` in terms of `√5`. -/
lemma lamM_eq : lamM = 7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) := by
  have h4 : discM = 4 * (73 - 32 * Real.sqrt 5) := by
    unfold discM pc
    ring
  have hnn : (0:ℝ) ≤ 73 - 32 * Real.sqrt 5 := by
    have := sqrt5_ub
    linarith
  have : Real.sqrt discM = 2 * Real.sqrt (73 - 32 * Real.sqrt 5) := by
    rw [h4, show (4:ℝ) * (73 - 32 * Real.sqrt 5) = 2^2 * (73 - 32 * Real.sqrt 5) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  unfold lamM pc
  rw [this]
  ring

lemma lamM_lb : (3.7302885 : ℝ) < lamM := by
  have h1 := pc_ub
  have h2 := sqrt_discM_lb
  unfold lamM
  linarith

lemma lamM_ub : lamM < 3.7302886 := by
  have h1 := pc_lb
  have h2 := sqrt_discM_ub
  unfold lamM
  linarith

lemma lamM_pos : 0 < lamM := lt_trans (by norm_num) lamM_lb

lemma muM_lb : (1.3254394 : ℝ) < muM := by
  have h1 := pc_ub
  have h2 := sqrt_discM_ub
  unfold muM
  linarith

lemma muM_ub : muM < 1.3254396 := by
  have h1 := pc_lb
  have h2 := sqrt_discM_lb
  unfold muM
  linarith

/-- The quadratic factor of the characteristic polynomial splits over `ℝ` with roots
`λ(E(M))` and `muM`. -/
lemma quadM_factor (x : ℝ) :
    x^2 - (10 - 8*pc)*x + 8*pc = (x - lamM) * (x - muM) := by
  have hsq : Real.sqrt discM ^ 2 = discM := Real.sq_sqrt discM_nonneg
  have hd : discM = 164 - 256 * pc := rfl
  unfold lamM muM
  have hpc := pc_sq
  nlinarith [hsq, hd, hpc]

lemma lamM_root : lamM^2 - (10 - 8*pc)*lamM + 8*pc = 0 := by
  rw [quadM_factor lamM]
  ring

lemma muM_root : muM^2 - (10 - 8*pc)*muM + 8*pc = 0 := by
  rw [quadM_factor muM]
  ring

/-! ## `λ(E(M))` is an eigenvalue of `E(M)` -/

lemma pc_sq_complex : ((pc : ℂ))^2 = 1 - (pc : ℂ) := by
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) pc_sq

/-- The characteristic polynomial of the live block of `E(M)` at the critical parameter, over `ℂ`.
-/
lemma det_char_EMlive_pc (z : ℂ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - EMlive (pc : ℂ)).det
      = (z - (4 - 4*(pc:ℂ))) * (z^2 - (10 - 8*(pc:ℂ))*z + 8*(pc:ℂ)) :=
  det_char_EMlive (pc : ℂ) z pc_sq_complex

/-- `λ(E(M))` is an eigenvalue of the mean offspring matrix `E(M)` at the critical parameter. -/
theorem lamM_hasEig : HasEig (EM (pc : ℂ)) (lamM : ℂ) := by
  apply hasEig_EMlive_EM
  rw [hasEig_iff_det, det_char_EMlive_pc]
  have h : ((lamM : ℂ))^2 - (10 - 8*(pc:ℂ))*(lamM : ℂ) + 8*(pc:ℂ) = 0 := by
    have := lamM_root
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  rw [h, mul_zero]

/-! ## `λ(E(M))` is the spectral radius -/

/-- Every complex eigenvalue of `E(M)` at the critical parameter has modulus at most
`λ(E(M))`. -/
theorem hasEig_EM_norm_le (z : ℂ) (hz : HasEig (EM (pc : ℂ)) z) : ‖z‖ ≤ lamM := by
  rcases hasEig_EM_live _ _ hz with h0 | hlive
  · rw [h0]
    simpa using lamM_pos.le
  rw [hasEig_iff_det, det_char_EMlive_pc] at hlive
  rcases mul_eq_zero.mp hlive with h | h
  · -- `z = 4 - 4 p_c`, of modulus `≈ 1.5279`
    have hz' : z = ((4 - 4*pc : ℝ) : ℂ) := by
      have := sub_eq_zero.mp h
      rw [this]
      push_cast
      ring
    rw [hz', Complex.norm_real, Real.norm_eq_abs]
    have h1 := pc_lb
    have h2 := lamM_lb
    rw [abs_of_nonneg (by linarith [pc_ub])]
    linarith
  · -- `z` is a root of the quadratic factor
    have hq : z^2 + ((8*pc - 10 : ℝ) : ℂ)*z + ((8*pc : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination h
    rcases quad_root_cases (8*pc - 10) (8*pc) z hq with ⟨x, hx, hroot⟩ | habs
    · have hfac : (x - lamM) * (x - muM) = 0 := by
        rw [← quadM_factor x]
        linarith [hroot]
      rw [hx, Complex.norm_real, Real.norm_eq_abs]
      rcases mul_eq_zero.mp hfac with h' | h'
      · have : x = lamM := by linarith [sub_eq_zero.mp h']
        rw [this, abs_of_pos lamM_pos]
      · have hxm : x = muM := by linarith [sub_eq_zero.mp h']
        rw [hxm, abs_of_pos (lt_trans (by norm_num) muM_lb)]
        linarith [muM_ub, lamM_lb]
    · -- modulus is `√(8 p_c) ≈ 2.2236`
      nlinarith [habs, pc_ub, lamM_lb, norm_nonneg z]

/-! ## Uniqueness -/

/-- `λ(E(M))` is the unique eigenvalue of `E(M)` which is real and at least `2`. -/
theorem lamM_unique (x : ℝ) (hx : HasEig (EM (pc : ℂ)) (x : ℂ)) (hx2 : 2 ≤ x) : x = lamM := by
  rcases hasEig_EM_live _ _ hx with h0 | hlive
  · exfalso
    have : x = 0 := by exact_mod_cast h0
    linarith
  rw [hasEig_iff_det, det_char_EMlive_pc] at hlive
  rcases mul_eq_zero.mp hlive with h | h
  · exfalso
    have hx' : (x : ℂ) = ((4 - 4*pc : ℝ) : ℂ) := by
      have := sub_eq_zero.mp h
      rw [this]
      push_cast
      ring
    have : x = 4 - 4*pc := by exact_mod_cast hx'
    have := pc_lb
    linarith
  · have hq : x^2 - (10 - 8*pc)*x + 8*pc = 0 := by
      have : ((x^2 - (10 - 8*pc)*x + 8*pc : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
      exact_mod_cast this
    have hfac : (x - lamM) * (x - muM) = 0 := by
      rw [← quadM_factor x]
      linarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith [sub_eq_zero.mp h']
    · exfalso
      have : x = muM := by linarith [sub_eq_zero.mp h']
      have := muM_ub
      linarith

/-- **`λ(E(M))` is the spectral radius of `E(M)`** at the critical parameter. -/
theorem lamM_isGreatest :
    IsGreatest {r : ℝ | ∃ z : ℂ, HasEig (EM (pc : ℂ)) z ∧ ‖z‖ = r} lamM := by
  constructor
  · exact ⟨(lamM : ℂ), lamM_hasEig, by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos lamM_pos]⟩
  · rintro r ⟨z, hz, rfl⟩
    exact hasEig_EM_norm_le z hz

@[simp] theorem specRad_EM : specRad (EM (pc : ℂ)) = lamM :=
  specRad_eq_of_isGreatest lamM_isGreatest

/-! ## The numerical value -/

/-- The value quoted in Subsection 4.2: `λ(E(M)) ≈ 3.7303`. -/
theorem lamM_approx : |lamM - 3.7303| < 1e-4 := by
  rw [abs_lt]
  constructor
  · linarith [lamM_lb]
  · linarith [lamM_ub]

end Outlook
