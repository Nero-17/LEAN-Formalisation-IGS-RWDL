import RequestProject.NonlinearPerronUnique
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Normalized Thomson orbits converge by order and residual drift.
No projective convergence theorem or Lipschitz estimate is an input.
-/

namespace EIGS.RenormMap

open scoped BigOperators
open Filter Topology

variable {K : ℕ} (Ψ : EIGS.RenormMap K)

private noncomputable def minimumRatio (hK : 0 < K)
    (reference vector : Fin K → ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hK⟩, Finset.mem_univ _⟩ (fun i => vector i / reference i)

private lemma minimumRatio_le (hK : 0 < K) (reference vector : Fin K → ℝ)
    (i : Fin K) : minimumRatio hK reference vector ≤ vector i / reference i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private lemma le_minimumRatio (hK : 0 < K) (reference vector : Fin K → ℝ)
    {bound : ℝ} (hbound : ∀ i, bound ≤ vector i / reference i) :
    bound ≤ minimumRatio hK reference vector :=
  (Finset.le_inf'_iff _ _).mpr (fun i _ => hbound i)

private lemma basis_nonneg (index : Fin K) :
    (0 : Fin K → ℝ) ≤ Pi.single index 1 := by
  classical
  intro i
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

private lemma basis_ne_zero (index : Fin K) :
    (Pi.single index 1 : Fin K → ℝ) ≠ 0 := by
  intro h
  have hi := congrFun h index
  simpa using hi

private lemma residual_drift (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i)
    {reference : Fin K → ℝ} {ρ : ℝ}
    (hreference : ∀ i, 0 < reference i) (hρ : 0 < ρ)
    (heigen : Ψ.apply reference = ρ • reference) (index : Fin K) :
    ∃ drift : ℝ, 0 < drift ∧
      ∀ (vector next : Fin K → ℝ) (lower : ℝ), 0 ≤ lower →
        lower • reference ≤ vector → Ψ.apply vector = ρ • next →
        lower + drift * (vector index - lower * reference index) ≤
          minimumRatio hK reference next := by
  classical
  have hpositive := hstrong (Pi.single index 1) (basis_nonneg index) (basis_ne_zero index)
  let drift : ℝ := minimumRatio hK (fun i => ρ * reference i)
    (Ψ.apply (Pi.single index 1))
  refine ⟨drift, ?_, ?_⟩
  · apply (Finset.lt_inf'_iff _).mpr
    intro i hi
    exact div_pos (hpositive i) (mul_pos hρ (hreference i))
  · intro vector next lower hlower hlower_bound hrec
    have residual_nonneg : 0 ≤ vector - lower • reference := sub_nonneg.mpr hlower_bound
    have coordinate_nonneg : 0 ≤ vector index - lower * reference index := residual_nonneg index
    have basis_bound :
        (vector index - lower * reference index) • (Pi.single index (1 : ℝ) : Fin K → ℝ) ≤
          vector - lower • reference := by
      intro i
      by_cases hi : i = index
      · subst i
        simp
      · simpa [Pi.single_apply, hi, Ne.symm hi] using residual_nonneg i
    have hmono := Ψ.apply_mono (smul_nonneg coordinate_nonneg (basis_nonneg index)) basis_bound
    rw [Ψ.apply_smul (Pi.single index 1) coordinate_nonneg] at hmono
    have hsuper := Ψ.apply_superadditive
      (smul_nonneg hlower (fun i => (hreference i).le)) residual_nonneg
    rw [add_sub_cancel, Ψ.apply_smul reference hlower, heigen] at hsuper
    apply le_minimumRatio
    intro i
    have hcoefficient : drift * (ρ * reference i) ≤ Ψ.apply (Pi.single index 1) i :=
      (le_div_iff₀ (mul_pos hρ (hreference i))).mp
        (minimumRatio_le hK (fun i => ρ * reference i)
          (Ψ.apply (Pi.single index 1)) i)
    have hbound :
        ρ * ((lower + drift * (vector index - lower * reference index)) * reference i)
          ≤ ρ * next i := by
      calc
        _ = lower * (ρ * reference i) +
            (vector index - lower * reference index) * (drift * (ρ * reference i)) := by ring
        _ ≤ lower * (ρ * reference i) +
            (vector index - lower * reference index) * Ψ.apply (Pi.single index 1) i :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hcoefficient coordinate_nonneg)
        _ ≤ lower * (ρ * reference i) + Ψ.apply (vector - lower • reference) i := by
          exact add_le_add le_rfl (hmono i)
        _ ≤ Ψ.apply vector i := hsuper i
        _ = ρ * next i := congrFun hrec i
    exact (le_div_iff₀ (hreference i)).mpr ((mul_le_mul_iff_right₀ hρ).mp hbound)

/-- A normalized positive orbit converges to a positive multiple of its
normalized eigenvector. Only the recurrence and elementary orbit bounds are
inputs; convergence itself is proved by positive residual drift. -/
theorem normalized_sequence_converges (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i)
    {reference : Fin K → ℝ} {ρ : ℝ}
    (hreference : ∀ i, 0 < reference i) (hρ : 0 < ρ)
    (hnorm : (∑ i, reference i) = 1)
    (heigen : Ψ.apply reference = ρ • reference)
    (sequence : ℕ → (Fin K → ℝ))
    (hrec : ∀ n, Ψ.apply (sequence n) = ρ • sequence (n + 1))
    {lower upper : ℝ} (hlower : 0 < lower)
    (hbound : ∀ n i, lower ≤ sequence n i ∧ sequence n i ≤ upper) :
    ∃ limit : ℝ, 0 < limit ∧
      Tendsto sequence atTop (nhds (limit • reference)) := by
  classical
  let ratios : ℕ → ℝ := fun n => minimumRatio hK reference (sequence n)
  have reference_le_one (i : Fin K) : reference i ≤ 1 := by
    calc
      reference i ≤ ∑ j, reference j :=
        Finset.single_le_sum (fun j _ => (hreference j).le) (Finset.mem_univ i)
      _ = 1 := hnorm
  have ratios_lower (n : ℕ) : lower ≤ ratios n := by
    apply le_minimumRatio
    intro i
    apply (le_div_iff₀ (hreference i)).mpr
    exact (mul_le_of_le_one_right hlower.le (reference_le_one i)).trans (hbound n i).1
  have ratios_bound (n : ℕ) : ratios n ≤ upper / reference ⟨0, hK⟩ := by
    exact (minimumRatio_le hK reference (sequence n) ⟨0, hK⟩).trans
      (div_le_div_of_nonneg_right (hbound n ⟨0, hK⟩).2 (hreference _).le)
  have lower_bound (n : ℕ) : ratios n • reference ≤ sequence n := by
    intro i
    exact (le_div_iff₀ (hreference i)).mp (minimumRatio_le hK reference (sequence n) i)
  have drift_bounds (index : Fin K) : ∃ drift : ℝ, 0 < drift ∧ ∀ n,
      0 ≤ sequence n index - ratios n * reference index ∧
      drift * (sequence n index - ratios n * reference index) ≤ ratios (n + 1) - ratios n := by
    obtain ⟨drift, hdrift, hstep⟩ := Ψ.residual_drift hK hstrong hreference hρ heigen index
    refine ⟨drift, hdrift, fun n => ⟨sub_nonneg.mpr (lower_bound n index), ?_⟩⟩
    have h := hstep (sequence n) (sequence (n + 1)) (ratios n)
      ((ratios_lower n).trans' hlower.le) (lower_bound n) (hrec n)
    linarith
  have ratios_mono : Monotone ratios := by
    apply monotone_nat_of_le_succ
    intro n
    obtain ⟨drift, hdrift, hstep⟩ := drift_bounds ⟨0, hK⟩
    have h := hstep n
    have hnonneg := mul_nonneg hdrift.le h.1
    linarith
  have ratios_bdd : BddAbove (Set.range ratios) :=
    ⟨upper / reference ⟨0, hK⟩, Set.forall_mem_range.mpr ratios_bound⟩
  have hlimit : Tendsto ratios atTop (nhds (⨆ n, ratios n)) :=
    tendsto_atTop_ciSup ratios_mono ratios_bdd
  have hlimit_positive : 0 < ⨆ n, ratios n :=
    hlower.trans_le ((ratios_lower 0).trans (le_ciSup ratios_bdd 0))
  refine ⟨⨆ n, ratios n, hlimit_positive, tendsto_pi_nhds.mpr ?_⟩
  intro index
  obtain ⟨drift, hdrift, hstep⟩ := drift_bounds index
  have hshift : Tendsto (fun n => ratios (n + 1)) atTop (nhds (⨆ n, ratios n)) :=
    hlimit.comp (tendsto_add_atTop_nat 1)
  have hdifference : Tendsto (fun n => (ratios (n + 1) - ratios n) / drift)
      atTop (nhds 0) := by
    simpa using (hshift.sub hlimit).div_const drift
  have hresidual : Tendsto (fun n => sequence n index - ratios n * reference index)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n => (hstep n).1) (fun n => ?_) hdifference
    exact (le_div_iff₀ hdrift).mpr (by simpa only [mul_comm] using (hstep n).2)
  have hsum := hresidual.add (hlimit.mul_const (reference index))
  simpa only [ratios, sub_add_cancel, zero_add, Pi.smul_apply, smul_eq_mul] using hsum

/-- Corollary 2.8 from strong positivity, with no projective-convergence input. -/
theorem iterate_normalized_limit_of_strongly_positive (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i)
    {reference : Fin K → ℝ} {ρ : ℝ}
    (hreference : ∀ i, 0 < reference i) (hρ : 0 < ρ)
    (hnorm : (∑ i, reference i) = 1)
    (heigen : Ψ.apply reference = ρ • reference) :
    ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun n => fun i => Ψ.apply^[n] (fun _ => 1) i / ρ ^ n)
        atTop (nhds (limit • reference)) := by
  let sequence : ℕ → (Fin K → ℝ) :=
    fun n i => Ψ.apply^[n] (fun _ => 1) i / ρ ^ n
  have hrec (n : ℕ) : Ψ.apply (sequence n) = ρ • sequence (n + 1) := by
    have hsequence : sequence n = (ρ ^ n)⁻¹ • Ψ.apply^[n] (fun _ => 1) := by
      ext i
      simp only [sequence, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [hsequence, Ψ.apply_smul _ (inv_nonneg.mpr (pow_nonneg hρ.le n))]
    ext i
    simp only [sequence, Pi.smul_apply, smul_eq_mul, Function.iterate_succ_apply']
    rw [pow_succ]
    field_simp
  obtain ⟨lower, upper, hlower, hupper, hgrowth⟩ :=
    Ψ.iterate_one_two_sided hreference hρ heigen
  have hbound (n : ℕ) (i : Fin K) : lower ≤ sequence n i ∧ sequence n i ≤ upper := by
    refine ⟨(le_div_iff₀ (pow_pos hρ n)).mpr (hgrowth n i).1,
      (div_le_iff₀ (pow_pos hρ n)).mpr (hgrowth n i).2⟩
  exact Ψ.normalized_sequence_converges hK hstrong hreference hρ hnorm heigen
    sequence hrec hlower hbound

end EIGS.RenormMap
