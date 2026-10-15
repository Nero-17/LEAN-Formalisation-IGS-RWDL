import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Finite independent trials and an almost-sure renewal phase bound.
Only independence inside each phase is required. An actual address model
must still supply the block maps, their independence and their word masses.
These statements do not assume any volume fluctuation conclusion. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem independent_trials_failure_bound
    {Sample Alphabet : Type*} [MeasurableSpace Sample] [MeasurableSpace Alphabet]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (trials : ℕ) (blocks : Fin trials → Sample → Alphabet)
    (independent : iIndepFun blocks law) (good : Set Alphabet)
    (goodMeasurable : MeasurableSet good)
    (blocksMeasurable : ∀ trial, Measurable (blocks trial))
    (successLower : ℝ) (successNonnegative : 0 ≤ successLower)
    (successBelowOne : successLower ≤ 1)
    (successMass : ∀ trial, ENNReal.ofReal successLower ≤ law ((blocks trial) ⁻¹' good)) :
    law {sample | ∀ trial, blocks trial sample ∉ good} ≤
      ENNReal.ofReal (Real.exp (-successLower * trials)) := by
  have failureMass (trial : Fin trials) :
      law ((blocks trial) ⁻¹' goodᶜ) ≤ ENNReal.ofReal (1 - successLower) := by
    rw [Set.preimage_compl,
      measure_compl (goodMeasurable.preimage (blocksMeasurable trial)) (measure_ne_top _ _)]
    have bound := tsub_le_tsub_left (successMass trial) 1
    simpa only [measure_univ, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 successNonnegative] using bound
  have exactFailure :
      law {sample | ∀ trial, blocks trial sample ∉ good} =
        ∏ trial : Fin trials, law ((blocks trial) ⁻¹' goodᶜ) := by
    have identity := independent.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => goodᶜ) (fun _ _ => goodMeasurable.compl)
    simpa only [Finset.mem_univ, Set.iInter_true, Set.mem_compl_iff,
      Set.mem_preimage, Set.setOf_forall] using identity
  rw [exactFailure]
  calc
    _ ≤ ∏ _trial : Fin trials, ENNReal.ofReal (1 - successLower) :=
      Finset.prod_le_prod' fun trial _ => failureMass trial
    _ = ENNReal.ofReal ((1 - successLower) ^ trials) := by
      simp [ENNReal.ofReal_pow, sub_nonneg.mpr successBelowOne]
    _ ≤ ENNReal.ofReal (Real.exp (-successLower * trials)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (1 - successLower) ^ trials ≤ (Real.exp (-successLower)) ^ trials :=
          pow_le_pow_left₀ (sub_nonneg.mpr successBelowOne)
            (Real.one_sub_le_exp_neg successLower) _
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

def renewalPhaseTrialCount (phase : ℕ) : ℕ := (phase + 1) ^ 2 * 2 ^ phase

theorem summable_renewal_phase_failure :
    Summable (fun phase : ℕ => Real.exp (-((phase + 1 : ℝ) ^ 2))) := by
  apply Real.summable_exp_neg_nat.of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro phase
  apply Real.exp_le_exp.mpr
  have nonnegative : (0 : ℝ) ≤ phase := Nat.cast_nonneg phase
  nlinarith [sq_nonneg (phase : ℝ)]

theorem ae_eventually_independent_renewal_phase_success
    {Sample : Type*} [MeasurableSpace Sample]
    {Alphabet : ℕ → Type*} [∀ phase, MeasurableSpace (Alphabet phase)]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (blocks : ∀ phase, Fin (renewalPhaseTrialCount phase) → Sample → Alphabet phase)
    (independent : ∀ phase, iIndepFun (blocks phase) law)
    (good : ∀ phase, Set (Alphabet phase))
    (goodMeasurable : ∀ phase, MeasurableSet (good phase))
    (blocksMeasurable : ∀ phase trial, Measurable (blocks phase trial))
    (successMass : ∀ phase trial,
      ENNReal.ofReal ((2 : ℝ) ^ phase)⁻¹ ≤
        law ((blocks phase trial) ⁻¹' good phase)) :
    ∀ᵐ sample ∂law, ∀ᶠ phase in atTop,
      ∃ trial, blocks phase trial sample ∈ good phase := by
  have failureBound (phase : ℕ) :
      law {sample | ∀ trial, blocks phase trial sample ∉ good phase} ≤
        ENNReal.ofReal (Real.exp (-((phase + 1 : ℝ) ^ 2))) := by
    have powerPositive : (0 : ℝ) < 2 ^ phase := by positivity
    have powerAboveOne : (1 : ℝ) ≤ 2 ^ phase := one_le_pow₀ (by norm_num)
    have bound := independent_trials_failure_bound law (renewalPhaseTrialCount phase)
      (blocks phase) (independent phase) (good phase) (goodMeasurable phase)
      (blocksMeasurable phase) ((2 : ℝ) ^ phase)⁻¹ (by positivity)
      ((inv_le_one₀ powerPositive).mpr powerAboveOne) (successMass phase)
    convert bound using 1 <;>
      simp only [renewalPhaseTrialCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat] <;> congr 2 <;> field_simp <;> ring
  have summableMass :
      (∑' phase, law {sample | ∀ trial, blocks phase trial sample ∉ good phase}) ≠ ⊤ :=
    ne_top_of_le_ne_top summable_renewal_phase_failure.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum failureBound)
  filter_upwards [ae_eventually_notMem summableMass] with sample eventualSuccess
  simpa only [Set.mem_setOf_eq, not_forall, not_not] using eventualSuccess

end
end EIGS

#print axioms EIGS.independent_trials_failure_bound
#print axioms EIGS.summable_renewal_phase_failure
#print axioms EIGS.ae_eventually_independent_renewal_phase_success
