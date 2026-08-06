import Mathlib

/-!
# The mean matrices of Subsection 4.2

Subsection 4.2 of *Iterated Graph Systems (I): random walks and diffusion limits*
(arXiv:2603.13798) codes the critical percolation cluster on the diamond hierarchical lattice by a
four-colour random EIGS, with colour order `(1,2,3,4) = (red, blue, green, black)`.  Colour `4` is a
cemetery state and is kept in the indexing only as a zero placeholder.

The mass growth of the cluster is governed by the mean offspring matrix `E(M)` of the live colours,
and the degree growth by the mean boundary matrix `E(N)`.  With `p` the bond parameter these are

```
            ⎛ 8p²  4p⁴  4p⁵  0 ⎞
    E(M) =  ⎜ 4p²  4p²  4p³  0 ⎟ ,
            ⎜ 2p²   0    2   0 ⎟
            ⎝  0    0    0   0 ⎠
```

and the `8 × 8` matrix `E(N)` written out in `EN` below.  Since the systems are reducible, the
relevant eigenvalues `λ(E(M))`, `λ(E(N))` are the Perron roots of the *live* blocks: the upper-left
`3 × 3` block `EMlive` of `E(M)` and the upper-left `6 × 6` block `ENlive` of `E(N)`.

This file sets up the matrices, an elementary notion of (complex) eigenvalue, the reduction of the
eigenvalue problem of the full matrices to that of the live blocks (and, for `E(N)`, of the live
block to two `3 × 3` blocks obtained by separating odd and even indices), the characteristic
polynomials of those `3 × 3` blocks at a parameter satisfying `p² = 1 - p`, and an elementary
analysis of the complex roots of a real quadratic.
-/

namespace Outlook

open Matrix

/-! ## The matrices -/

/-- The mean offspring matrix `E(M)` of Subsection 4.2, in the colour order
`(red, blue, green, black)`. -/
def EM {R : Type*} [CommRing R] (p : R) : Matrix (Fin 4) (Fin 4) R :=
  !![8*p^2, 4*p^4, 4*p^5, 0;
     4*p^2, 4*p^2, 4*p^3, 0;
     2*p^2, 0,     2,     0;
     0,     0,     0,     0]

/-- The live (red-blue-green) block of `E(M)`. -/
def EMlive {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![8*p^2, 4*p^4, 4*p^5;
     4*p^2, 4*p^2, 4*p^3;
     2*p^2, 0,     2]

/-- The mean boundary matrix `E(N)` of Subsection 4.2. -/
def EN {R : Type*} [CommRing R] (p : R) : Matrix (Fin 8) (Fin 8) R :=
  !![4*p^2, 0,     2*p^4, 0,     2*p^5, 0,     0, 0;
     0,     4*p^2, 0,     2*p^4, 0,     2*p^5, 0, 0;
     2*p^2, 0,     2*p^2, 0,     2*p^3, 0,     0, 0;
     0,     2*p^2, 0,     2*p^2, 0,     2*p^3, 0, 0;
     2*p,   0,     0,     0,     2*p^2, 0,     0, 0;
     0,     0,     0,     0,     0,     2*p,   0, 0;
     0,     0,     0,     0,     0,     0,     0, 0;
     0,     0,     0,     0,     0,     0,     0, 0]

/-- The live block of `E(N)`. -/
def ENlive {R : Type*} [CommRing R] (p : R) : Matrix (Fin 6) (Fin 6) R :=
  !![4*p^2, 0,     2*p^4, 0,     2*p^5, 0;
     0,     4*p^2, 0,     2*p^4, 0,     2*p^5;
     2*p^2, 0,     2*p^2, 0,     2*p^3, 0;
     0,     2*p^2, 0,     2*p^2, 0,     2*p^3;
     2*p,   0,     0,     0,     2*p^2, 0;
     0,     0,     0,     0,     0,     2*p]

/-- The odd-index (rows and columns `0, 2, 4`) block of the live block of `E(N)`. -/
def ENodd {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![4*p^2, 2*p^4, 2*p^5;
     2*p^2, 2*p^2, 2*p^3;
     2*p,   0,     2*p^2]

/-- The even-index (rows and columns `1, 3, 5`) block of the live block of `E(N)`. -/
def ENeven {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![4*p^2, 2*p^4, 2*p^5;
     2*p^2, 2*p^2, 2*p^3;
     0,     0,     2*p]

/-! ## Eigenvalues -/

/-- `z` is an eigenvalue of the complex matrix `A`. -/
def HasEig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧ A *ᵥ v = z • v

/-- The spectral radius of a complex matrix: the largest modulus of an eigenvalue. -/
noncomputable def specRad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, HasEig A z ∧ ‖z‖ = r}

lemma specRad_eq_of_isGreatest {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {r : ℝ}
    (h : IsGreatest {r : ℝ | ∃ z : ℂ, HasEig A z ∧ ‖z‖ = r} r) : specRad A = r :=
  h.csSup_eq

lemma hasEig_iff_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    HasEig A z ↔ (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hA, sub_self]
  · rintro ⟨v, hv, hA⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hA
    exact hA.symm

/-! ## Reduction to the live blocks -/

/-- A nonzero eigenvalue of `E(M)` is an eigenvalue of its live block. -/
lemma hasEig_EM_live (p z : ℂ) (h : HasEig (EM p) z) : z = 0 ∨ HasEig (EMlive p) z := by
  obtain ⟨v, hv, hA⟩ := h
  by_cases hz : z = 0
  · exact Or.inl hz
  right
  have e3 := congrFun hA 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, EM] at e3
  have hv3 : v 3 = 0 := by
    rcases e3 with h | h
    · exact absurd h hz
    · exact h
  refine ⟨![v 0, v 1, v 2], ?_, ?_⟩
  · intro hcon
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at ha
    have h0 : v 0 = 0 := congrFun hcon 0
    have h1 : v 1 = 0 := congrFun hcon 1
    have h2 : v 2 = 0 := congrFun hcon 2
    fin_cases a
    · exact ha h0
    · exact ha h1
    · exact ha h2
    · exact ha hv3
  · funext i
    have hi := congrFun hA i.castSucc
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> simp [EM, EMlive, hv3] at hi ⊢ <;> linear_combination hi

/-- A nonzero eigenvalue of `E(N)` is an eigenvalue of its live block. -/
lemma hasEig_EN_live (p z : ℂ) (h : HasEig (EN p) z) : z = 0 ∨ HasEig (ENlive p) z := by
  obtain ⟨v, hv, hA⟩ := h
  by_cases hz : z = 0
  · exact Or.inl hz
  right
  have e6 := congrFun hA 6
  have e7 := congrFun hA 7
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, EN] at e6 e7
  have hv6 : v 6 = 0 := by
    rcases e6 with h | h
    · exact absurd h hz
    · exact h
  have hv7 : v 7 = 0 := by
    rcases e7 with h | h
    · exact absurd h hz
    · exact h
  refine ⟨![v 0, v 1, v 2, v 3, v 4, v 5], ?_, ?_⟩
  · intro hcon
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at ha
    have h0 : v 0 = 0 := congrFun hcon 0
    have h1 : v 1 = 0 := congrFun hcon 1
    have h2 : v 2 = 0 := congrFun hcon 2
    have h3 : v 3 = 0 := congrFun hcon 3
    have h4 : v 4 = 0 := congrFun hcon 4
    have h5 : v 5 = 0 := congrFun hcon 5
    fin_cases a
    · exact ha h0
    · exact ha h1
    · exact ha h2
    · exact ha h3
    · exact ha h4
    · exact ha h5
    · exact ha hv6
    · exact ha hv7
  · funext i
    have hi := congrFun hA (i.castLE (by norm_num))
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> simp [EN, ENlive, hv6, hv7, -mul_eq_mul_right_iff] at hi ⊢ <;>
      linear_combination hi

/-- An eigenvalue of the live block of `E(N)` is an eigenvalue of one of the two `3 × 3` blocks
obtained by separating the odd and the even indices. -/
lemma hasEig_ENlive_split (p z : ℂ) (h : HasEig (ENlive p) z) :
    HasEig (ENodd p) z ∨ HasEig (ENeven p) z := by
  obtain ⟨v, hv, hA⟩ := h
  have hodd : (ENodd p) *ᵥ ![v 0, v 2, v 4] = z • ![v 0, v 2, v 4] := by
    funext i
    have h0 := congrFun hA 0
    have h2 := congrFun hA 2
    have h4 := congrFun hA 4
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul] at h0 h2 h4
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [ENodd, ENlive] at h0 ⊢
      linear_combination h0
    · simp [ENodd, ENlive] at h2 ⊢
      linear_combination h2
    · simp [ENodd, ENlive] at h4 ⊢
      linear_combination h4
  have heven : (ENeven p) *ᵥ ![v 1, v 3, v 5] = z • ![v 1, v 3, v 5] := by
    funext i
    have h1 := congrFun hA 1
    have h3 := congrFun hA 3
    have h5 := congrFun hA 5
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul] at h1 h3 h5
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [ENeven, ENlive] at h1 ⊢
      linear_combination h1
    · simp [ENeven, ENlive] at h3 ⊢
      linear_combination h3
    · simp [ENeven, ENlive, -mul_eq_mul_right_iff] at h5 ⊢
      linear_combination h5
  by_cases hodd0 : (![v 0, v 2, v 4] : Fin 3 → ℂ) = 0
  · right
    refine ⟨![v 1, v 3, v 5], ?_, heven⟩
    intro hcon
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at ha
    have h0 : v 0 = 0 := congrFun hodd0 0
    have h2 : v 2 = 0 := congrFun hodd0 1
    have h4 : v 4 = 0 := congrFun hodd0 2
    have h1 : v 1 = 0 := congrFun hcon 0
    have h3 : v 3 = 0 := congrFun hcon 1
    have h5 : v 5 = 0 := congrFun hcon 2
    fin_cases a
    · exact ha h0
    · exact ha h1
    · exact ha h2
    · exact ha h3
    · exact ha h4
    · exact ha h5
  · exact Or.inl ⟨_, hodd0, hodd⟩

/-- Conversely, an eigenvalue of the live block of `E(M)` is an eigenvalue of `E(M)`. -/
lemma hasEig_EMlive_EM (p z : ℂ) (h : HasEig (EMlive p) z) : HasEig (EM p) z := by
  obtain ⟨w, hw, hA⟩ := h
  refine ⟨![w 0, w 1, w 2, 0], ?_, ?_⟩
  · intro hcon
    refine hw (funext fun i => ?_)
    have h0 : w 0 = 0 := congrFun hcon 0
    have h1 : w 1 = 0 := congrFun hcon 1
    have h2 : w 2 = 0 := congrFun hcon 2
    fin_cases i <;> simpa using ‹_›
  · funext i
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    have h2 := congrFun hA 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      at h0 h1 h2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [EM, EMlive] at h0 ⊢
      linear_combination h0
    · simp [EM, EMlive] at h1 ⊢
      linear_combination h1
    · simp [EM, EMlive] at h2 ⊢
      linear_combination h2
    · simp [EM]

/-- An eigenvalue of the odd block is an eigenvalue of the live block of `E(N)`. -/
lemma hasEig_ENodd_ENlive (p z : ℂ) (h : HasEig (ENodd p) z) : HasEig (ENlive p) z := by
  obtain ⟨w, hw, hA⟩ := h
  refine ⟨![w 0, 0, w 1, 0, w 2, 0], ?_, ?_⟩
  · intro hcon
    refine hw (funext fun i => ?_)
    have h0 : w 0 = 0 := congrFun hcon 0
    have h1 : w 1 = 0 := congrFun hcon 2
    have h2 : w 2 = 0 := congrFun hcon 4
    fin_cases i <;> simpa using ‹_›
  · funext i
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    have h2 := congrFun hA 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      at h0 h1 h2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [ENodd, ENlive] at h0 ⊢
      linear_combination h0
    · simp [ENlive]
    · simp [ENodd, ENlive] at h1 ⊢
      linear_combination h1
    · simp [ENlive]
    · simp [ENodd, ENlive] at h2 ⊢
      linear_combination h2
    · simp [ENlive]

/-- An eigenvalue of the live block of `E(N)` is an eigenvalue of `E(N)`. -/
lemma hasEig_ENlive_EN (p z : ℂ) (h : HasEig (ENlive p) z) : HasEig (EN p) z := by
  obtain ⟨w, hw, hA⟩ := h
  refine ⟨![w 0, w 1, w 2, w 3, w 4, w 5, 0, 0], ?_, ?_⟩
  · intro hcon
    refine hw (funext fun i => ?_)
    have h0 : w 0 = 0 := congrFun hcon 0
    have h1 : w 1 = 0 := congrFun hcon 1
    have h2 : w 2 = 0 := congrFun hcon 2
    have h3 : w 3 = 0 := congrFun hcon 3
    have h4 : w 4 = 0 := congrFun hcon 4
    have h5 : w 5 = 0 := congrFun hcon 5
    fin_cases i <;> simpa using ‹_›
  · funext i
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    have h2 := congrFun hA 2
    have h3 := congrFun hA 3
    have h4 := congrFun hA 4
    have h5 := congrFun hA 5
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]
      at h0 h1 h2 h3 h4 h5
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [EN, ENlive] at h0 ⊢
      linear_combination h0
    · simp [EN, ENlive] at h1 ⊢
      linear_combination h1
    · simp [EN, ENlive] at h2 ⊢
      linear_combination h2
    · simp [EN, ENlive] at h3 ⊢
      linear_combination h3
    · simp [EN, ENlive] at h4 ⊢
      linear_combination h4
    · simp [EN, ENlive, -mul_eq_mul_right_iff] at h5 ⊢
      linear_combination h5
    · simp [EN]
    · simp [EN]

/-! ## Characteristic polynomials of the `3 × 3` blocks -/

/-- Characteristic polynomial of the live block of `E(M)` at a parameter with `p² = 1 - p`. -/
lemma det_char_EMlive {R : Type*} [CommRing R] (p t : R) (hp : p^2 = 1 - p) :
    (t • (1 : Matrix (Fin 3) (Fin 3) R) - EMlive p).det
      = (t - (4 - 4*p)) * (t^2 - (10 - 8*p)*t + 8*p) := by
  simp [Matrix.det_fin_three, EMlive]
  linear_combination
    (-4*(2*p^5*t + 2*p^4*t - 8*p^4 + 8*p^3 - 6*p^2*t + 6*p*t + 8*p + 3*t^2 - 10*t)) * hp

/-- Characteristic polynomial of the odd block of `E(N)` at a parameter with `p² = 1 - p`. -/
lemma det_char_ENodd {R : Type*} [CommRing R] (p t : R) (hp : p^2 = 1 - p) :
    (t • (1 : Matrix (Fin 3) (Fin 3) R) - ENodd p).det
      = (t - 2) * (t^2 + (8*p - 6)*t + (20*p - 12)) := by
  simp [Matrix.det_fin_three, ENodd]
  linear_combination
    (4*(2*p^6 - 2*p^5 - 2*p^4*t + 2*p^3*t - 2*p^3 + p^2*t + 2*p^2 + p*t - 4*p - 2*t^2 + 6)) * hp

/-- Characteristic polynomial of the even block of `E(N)` at a parameter with `p² = 1 - p`. -/
lemma det_char_ENeven {R : Type*} [CommRing R] (p t : R) (hp : p^2 = 1 - p) :
    (t • (1 : Matrix (Fin 3) (Fin 3) R) - ENeven p).det
      = (t - 2*p) * (t^2 + (6*p - 6)*t + (8*p - 4)) := by
  simp [Matrix.det_fin_three, ENeven]
  linear_combination (2*(2*p - t)*(2*p^4 - 2*p^3 - 2*p + 3*t + 2)) * hp

/-! ## Complex roots of a real quadratic -/

/-- A complex root of a monic quadratic with real coefficients is either real, or has squared
modulus equal to the constant coefficient. -/
lemma quad_root_cases (b c : ℝ) (z : ℂ) (hz : z^2 + b*z + c = 0) :
    (∃ x : ℝ, z = (x : ℂ) ∧ x^2 + b*x + c = 0) ∨ ‖z‖ ^ 2 = c := by
  have him : z.re * z.im + z.im * z.re + b * z.im = 0 := by
    have := congrArg Complex.im hz
    simpa [Complex.ext_iff, pow_two, Complex.add_im, Complex.mul_im] using this
  have hre : z.re^2 - z.im^2 + b * z.re + c = 0 := by
    have := congrArg Complex.re hz
    simpa [Complex.ext_iff, pow_two, Complex.add_re, Complex.mul_re] using this
  have habs : ‖z‖ ^ 2 = z.re^2 + z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  by_cases hy : z.im = 0
  · left
    refine ⟨z.re, ?_, ?_⟩
    · apply Complex.ext <;> simp [hy]
    · rw [hy] at hre; linarith [hre]
  · right
    have hx : 2 * z.re + b = 0 := by
      have h : z.im * (2 * z.re + b) = 0 := by nlinarith [him]
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hy
      · exact h
    rw [habs]
    linear_combination -hre + z.re * hx

end Outlook
