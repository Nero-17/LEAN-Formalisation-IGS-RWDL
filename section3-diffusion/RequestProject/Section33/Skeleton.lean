import RequestProject.Section33.Volume

/-!
# Section 3.3, step 2: the skeleton neighbourhoods and Borel–Cantelli

This file formalises the second half of Lemma "heat-volume" of arXiv:2603.13798,
that is, the upper bound on `μ(B(x,r))` at `μ`-almost every *infinite-born*
point.  The paper's argument is:

1. the `C_*ρ_min(D)^{-m}`-neighbourhood `E_{m,L}` of the level-`(m-L)` skeleton
   has mass `≲ Σ_{k ≤ m-L} ρ(M)^k ρ(N)^{m-k} ρ(M)^{-m} ≲ (ρ(N)/ρ(M))^L`
   (the number of `k`-born points is `O(ρ(M)^k)` and each of them carries a ball
   of mass `≲ ρ(N)^{m-k}ρ(M)^{-m}` by the finite-born estimate);
2. with `L_m := ⌈(1+ε) log m / log(ρ(M)/ρ(N))⌉` the masses `μ(E_{m,L_m})` are
   summable, so by Borel–Cantelli almost every `x` avoids `E_{m,L_m}` eventually;
3. for such an `x` the nearby level-`m` terminal has birth level `≥ m-L_m+1`, so
   the finite-born estimate gives `μ(B(x,cρ_min(D)^{-m})) ≲ ρ(N)^{L_m}ρ(M)^{-m}`;
4. `ρ(N)^{L_m} ≲ m^{(1+ε)/(d_deg-1)}` and `m ≍ |log r|`.

Steps 1, 2 and 4 are *proved* here (the geometric summation, the summability and
Borel–Cantelli, and the exponent computation).  Step 3, being the combinatorial
input of §2 (number of `k`-born points, existence of a nearby terminal), enters
as a hypothesis of the final statement.
-/

namespace IGS
namespace Sec33

open Real Finset Filter MeasureTheory

/-- Geometric partial sums are bounded by `(1-q)⁻¹` for `0 ≤ q < 1`. -/
lemma geom_partial_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, q ^ i ≤ (1 - q)⁻¹ := by
  rw [geom_sum_eq (by linarith), div_le_iff_of_neg (by linarith)]
  have h : 0 ≤ q ^ n := by positivity
  have h2 : (1 - q)⁻¹ * (1 - q) = 1 := inv_mul_cancel₀ (by linarith)
  nlinarith [h2]

namespace Params

variable (P : Params)

/-- The contraction ratio `q = ρ(N)/ρ(M) ∈ (0,1)`. -/
noncomputable def q : ℝ := P.rN / P.rM

lemma q_pos : 0 < P.q := div_pos P.rN_pos P.rM_pos
lemma q_lt_one : P.q < 1 := (div_lt_one P.rM_pos).2 P.hrNM
lemma one_sub_q_pos : 0 < 1 - P.q := by linarith [P.q_lt_one]

/--
**The skeleton mass bound (step 1).**
`Σ_{k=0}^{m-L} ρ(M)^k ρ(N)^{m-k} ρ(M)^{-m} ≤ (1-q)^{-1} q^L` with
`q = ρ(N)/ρ(M)`; this is the paper's `μ(E_{m,L}) ≲ (ρ(N)/ρ(M))^L`.
-/
theorem skeleton_sum_bound (L m : ℕ) (hLm : L ≤ m) :
    (∑ k ∈ Finset.range (m - L + 1), P.rM ^ k * P.rN ^ (m - k)) / P.rM ^ m
      ≤ (1 - P.q)⁻¹ * P.q ^ L := by
  have hM : (0:ℝ) < P.rM := P.rM_pos
  have hMm : (0:ℝ) < P.rM ^ m := pow_pos hM m
  set n := m - L with hn
  have hmn : m - n = L := by omega
  -- termwise rewriting
  have hterm : ∀ k ∈ Finset.range (n + 1),
      P.rM ^ k * P.rN ^ (m - k) / P.rM ^ m = P.q ^ (m - k) := by
    intro k hk
    have hkm : k ≤ m := by
      simp only [Finset.mem_range] at hk
      omega
    have hsplit : P.rM ^ m = P.rM ^ k * P.rM ^ (m - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, q, div_pow]
    field_simp
  rw [Finset.sum_div, Finset.sum_congr rfl hterm]
  -- reflect the summation
  have hrefl : ∑ j ∈ Finset.range (n + 1), P.q ^ (m - j)
      = ∑ j ∈ Finset.range (n + 1), P.q ^ (L + j) := by
    have := Finset.sum_range_reflect (fun j => P.q ^ (m - j)) (n + 1)
    rw [← this]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    congr 1
    omega
  rw [hrefl]
  have : ∑ j ∈ Finset.range (n + 1), P.q ^ (L + j)
      = P.q ^ L * ∑ j ∈ Finset.range (n + 1), P.q ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  rw [this, mul_comm]
  exact mul_le_mul_of_nonneg_right (geom_partial_le (le_of_lt P.q_pos) P.q_lt_one _)
    (pow_nonneg (le_of_lt P.q_pos) L)


/--
**The mass of the skeleton neighbourhood `E_{m,L}`.**
The paper bounds `μ(E_{m,L})` by summing, over the `O(ρ(M)^k)` many `k`-born
points with `k ≤ m-L`, the finite-born ball estimate `≲ ρ(N)^{m-k}ρ(M)^{-m}`.
Carrying the two constants through the geometric summation gives
`μ(E_{m,L}) ≤ C_count C_ball (1-q)^{-1} q^L`.
-/
theorem skeleton_mass_le {Ccount Cball massE : ℝ} (hCcount : 0 ≤ Ccount) (hCball : 0 ≤ Cball)
    (L m : ℕ) (hLm : L ≤ m)
    (hsum : massE ≤ ∑ k ∈ Finset.range (m - L + 1),
      (Ccount * P.rM ^ k) * (Cball * P.rN ^ (m - k) / P.rM ^ m)) :
    massE ≤ Ccount * Cball * (1 - P.q)⁻¹ * P.q ^ L := by
  have hMm : (0:ℝ) < P.rM ^ m := pow_pos P.rM_pos m
  have hrw : ∑ k ∈ Finset.range (m - L + 1),
      (Ccount * P.rM ^ k) * (Cball * P.rN ^ (m - k) / P.rM ^ m)
      = Ccount * Cball
        * ((∑ k ∈ Finset.range (m - L + 1), P.rM ^ k * P.rN ^ (m - k)) / P.rM ^ m) := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [hrw] at hsum
  refine le_trans hsum ?_
  have hcoef : (0:ℝ) ≤ Ccount * Cball := mul_nonneg hCcount hCball
  have := P.skeleton_sum_bound L m hLm
  calc Ccount * Cball
        * ((∑ k ∈ Finset.range (m - L + 1), P.rM ^ k * P.rN ^ (m - k)) / P.rM ^ m)
      ≤ Ccount * Cball * ((1 - P.q)⁻¹ * P.q ^ L) := mul_le_mul_of_nonneg_left this hcoef
    _ = Ccount * Cball * (1 - P.q)⁻¹ * P.q ^ L := by ring

/-- The paper's choice `L_m = ⌈(1+ε) log m / log(ρ(M)/ρ(N))⌉`. -/
noncomputable def Lscale (eps : ℝ) (m : ℕ) : ℕ :=
  ⌈(1 + eps) * log m / log (P.rM / P.rN)⌉₊

lemma log_ratio_pos : 0 < log (P.rM / P.rN) :=
  Real.log_pos ((one_lt_div P.rN_pos).2 P.hrNM)

/-- **Step 2a**: `q^{L_m} ≤ m^{-(1+ε)}`, the estimate that makes the series summable. -/
theorem q_pow_Lscale_le {eps : ℝ} (heps : 0 ≤ eps) {m : ℕ} (hm : 1 ≤ m) :
    P.q ^ (P.Lscale eps m) ≤ (m : ℝ) ^ (-(1 + eps)) := by
  have hQ : 0 < log (P.rM / P.rN) := P.log_ratio_pos
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 ≤ log m := Real.log_nonneg (by exact_mod_cast hm)
  set x : ℝ := (1 + eps) * log m / log (P.rM / P.rN) with hx
  have hx0 : 0 ≤ x := by
    apply div_nonneg _ (le_of_lt hQ)
    positivity
  have hxL : x ≤ (P.Lscale eps m : ℝ) := Nat.le_ceil x
  -- `q^L ≤ q^x` since `q < 1`
  have hq0 : 0 < P.q := P.q_pos
  have hpow : P.q ^ (P.Lscale eps m) = P.q ^ ((P.Lscale eps m : ℕ) : ℝ) :=
    (Real.rpow_natCast P.q _).symm
  rw [hpow]
  have hmono : P.q ^ ((P.Lscale eps m : ℕ) : ℝ) ≤ P.q ^ x :=
    Real.rpow_le_rpow_of_exponent_ge hq0 (le_of_lt P.q_lt_one) hxL
  refine le_trans hmono ?_
  -- and `q^x = m^{-(1+ε)}`
  have hqlog : log P.q = -log (P.rM / P.rN) := by
    rw [q, Real.log_div (ne_of_gt P.rN_pos) (ne_of_gt P.rM_pos),
      Real.log_div (ne_of_gt P.rM_pos) (ne_of_gt P.rN_pos)]
    ring
  have : P.q ^ x = (m : ℝ) ^ (-(1 + eps)) := by
    rw [Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hmpos, hqlog, hx]
    congr 1
    field_simp
  exact le_of_eq this

/-- **Step 2b**: the masses of the skeleton neighbourhoods are summable. -/
theorem summable_q_pow_Lscale {eps : ℝ} (heps : 0 < eps) :
    Summable (fun m : ℕ => P.q ^ (P.Lscale eps (m + 1))) := by
  have hcomp : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(1 + eps))) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + eps)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    have h' : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + eps))) := by
      refine h.congr fun n => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    exact (summable_nat_add_iff 1).2 h'
  refine Summable.of_nonneg_of_le (fun m => pow_nonneg (le_of_lt P.q_pos) _) (fun m => ?_) hcomp
  exact P.q_pow_Lscale_le (le_of_lt heps) (Nat.succ_le_succ (Nat.zero_le m))

/--
**Step 2c: Borel–Cantelli.**
If the sets `E m` have mass at most `C q^{L_m}`, then `μ`-almost every point lies
outside `E m` for all large `m`.
-/
theorem ae_eventually_notMem_skeleton {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (E : ℕ → Set X) {eps C : ℝ} (heps : 0 < eps) (hC : 0 ≤ C)
    (hmass : ∀ m : ℕ, mu (E (m + 1)) ≤ ENNReal.ofReal (C * P.q ^ (P.Lscale eps (m + 1)))) :
    ∀ᵐ x ∂mu, ∀ᶠ m in atTop, x ∉ E m := by
  have hsum : Summable (fun m : ℕ => C * P.q ^ (P.Lscale eps (m + 1))) :=
    (P.summable_q_pow_Lscale heps).mul_left C
  have hne : (∑' m : ℕ, mu (E (m + 1))) ≠ ⊤ := by
    have hle : (∑' m : ℕ, mu (E (m + 1)))
        ≤ ∑' m : ℕ, ENNReal.ofReal (C * P.q ^ (P.Lscale eps (m + 1))) :=
      ENNReal.tsum_le_tsum hmass
    have hfin : (∑' m : ℕ, ENNReal.ofReal (C * P.q ^ (P.Lscale eps (m + 1)))) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun m => mul_nonneg hC (pow_nonneg (le_of_lt P.q_pos) _)) hsum]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin hle
  have h := ae_eventually_notMem hne
  filter_upwards [h] with x hx
  rw [eventually_atTop] at hx ⊢
  obtain ⟨m0, hm0⟩ := hx
  exact ⟨m0 + 1, fun m hm => by
    have := hm0 (m - 1) (by omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using this⟩

/--
**Step 4: the logarithmic correction.**
`ρ(N)^{L_m} ≤ ρ(N) · m^{(1+ε)/(d_deg-1)}`.
-/
theorem rN_pow_Lscale_le {eps : ℝ} (heps : 0 ≤ eps) {m : ℕ} (hm : 1 ≤ m) :
    P.rN ^ (P.Lscale eps m) ≤ P.rN * (m : ℝ) ^ ((1 + eps) / (P.ddeg - 1)) := by
  have hQ : 0 < log (P.rM / P.rN) := P.log_ratio_pos
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 ≤ log m := Real.log_nonneg (by exact_mod_cast hm)
  set x : ℝ := (1 + eps) * log m / log (P.rM / P.rN) with hx
  have hx0 : 0 ≤ x := div_nonneg (by positivity) (le_of_lt hQ)
  have hLx : (P.Lscale eps m : ℝ) ≤ x + 1 := le_of_lt (Nat.ceil_lt_add_one hx0)
  have hpow : P.rN ^ (P.Lscale eps m) = P.rN ^ ((P.Lscale eps m : ℕ) : ℝ) :=
    (Real.rpow_natCast P.rN _).symm
  rw [hpow]
  have hmono : P.rN ^ ((P.Lscale eps m : ℕ) : ℝ) ≤ P.rN ^ (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt P.hrN) hLx
  refine le_trans hmono (le_of_eq ?_)
  rw [Real.rpow_add P.rN_pos, Real.rpow_one, mul_comm]
  congr 1
  rw [Real.rpow_def_of_pos P.rN_pos, Real.rpow_def_of_pos hmpos, hx]
  congr 1
  have hratio := P.log_ratio_eq_inv_ddeg_sub_one
  have hrw : log P.rN * ((1 + eps) * log m / log (P.rM / P.rN))
      = (1 + eps) * log m * (log P.rN / log (P.rM / P.rN)) := by ring
  rw [hrw, hratio]
  ring

/--
**Step 4 in the form stated in the current version of the paper.**

Calibrating the parameter of `L_m` as `ε ↦ ε(d_deg-1)` turns the exponent
`(1+ε)/(d_deg-1)` proved above into the paper's `1/(d_deg-1) + ε`:

`ρ(N)^{L_m} ≤ ρ(N) · m^{1/(d_deg-1)+ε}`.
-/
theorem rN_pow_Lscale_le_logExp {eps : ℝ} (heps : 0 ≤ eps) {m : ℕ} (hm : 1 ≤ m) :
    P.rN ^ (P.Lscale (eps * (P.ddeg - 1)) m) ≤ P.rN * (m : ℝ) ^ (P.logExp + eps) := by
  have hcal := P.calibrated_exponent eps
  have h := P.rN_pow_Lscale_le (eps := eps * (P.ddeg - 1))
    (mul_nonneg heps (le_of_lt P.ddeg_sub_one_pos)) hm
  rwa [hcal] at h

/--
The exponent stated in the earlier version of the paper, `1 + 1/(d_deg-1) + ε`,
is (for `d_deg ≥ 2`) weaker than the exponent `(1+ε)/(d_deg-1)` proved above;
both give the same spectral dimension.  The current version states the sharp
exponent `1/(d_deg-1) + ε` (see `rN_pow_Lscale_le_logExp`).
-/
lemma exponent_le_paper {eps : ℝ} (heps : 0 ≤ eps) (hddeg : 2 ≤ P.ddeg) :
    (1 + eps) / (P.ddeg - 1) ≤ 1 + 1 / (P.ddeg - 1) + eps := by
  have h1 : (1:ℝ) ≤ P.ddeg - 1 := by linarith
  have h1' : (0:ℝ) < P.ddeg - 1 := by linarith
  have h2 : eps / (P.ddeg - 1) ≤ eps := by
    rw [div_le_iff₀ h1']
    nlinarith
  have h3 : (1 + eps) / (P.ddeg - 1) = 1 / (P.ddeg - 1) + eps / (P.ddeg - 1) := by
    field_simp
  rw [h3]
  linarith

end Params

end Sec33
end IGS
