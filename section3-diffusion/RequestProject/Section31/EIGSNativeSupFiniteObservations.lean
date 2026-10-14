import RequestProject.Section31.EIGSNativeSupTransition
import RequestProject.Section31.BanachBackwardObservations
import Mathlib.Analysis.Normed.Operator.Mul

/-! Finite observations of the genuine discrete walk from each Dirac starting
point, identified with the Banach supremum-space backward recursion. Scheduled
times may coincide. Native clocks use differences of absolute floors, with
no replacement by floors of time differences and no stationary averaging. -/

namespace IGS.Sec31.BanachBackwardObservations

variable {Time Test Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem backwardProduct_append (evolution : Time → Space →L[ℝ] Space)
    (multiplication : Test → Space →L[ℝ] Space)
    (first second : List (Time × Test)) (terminal : Space) :
    backwardProduct evolution multiplication (first ++ second) terminal =
      backwardProduct evolution multiplication first
        (backwardProduct evolution multiplication second terminal) := by
  induction first with
  | nil => rfl
  | cons observation remaining induction =>
      simp only [List.cons_append, backwardProduct, induction]

end IGS.Sec31.BanachBackwardObservations

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiNativeSup_scheduledBackward_eq_backwardProduct (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (schedule : ℕ → ℕ) (tests : ℕ → XiVtx system level → ℝ)
    (count : ℕ) (terminal : XiVtx system level → ℝ) :
    scheduledBackward
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      schedule tests count terminal =
    BanachBackwardObservations.backwardProduct
      (fun index : ℕ => xiNativeSupTransition system rulesConnected level ^
        (schedule (index + 1) - schedule index))
      (fun index : ℕ => ContinuousLinearMap.mul ℝ (XiVtx system level → ℝ) (tests index))
      ((List.range count).map (fun index => (index, index))) terminal := by
  induction count generalizing terminal with
  | zero => rfl
  | succ count induction =>
      have endpointIdentity :
          (fun point : XiVtx system level => tests count point *
            ∫ target, terminal target
              ∂(xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
                plantingNonadjacent level ^ (schedule (count + 1) - schedule count)) point) =
          ContinuousLinearMap.mul ℝ (XiVtx system level → ℝ) (tests count)
            ((xiNativeSupTransition system rulesConnected level ^
              (schedule (count + 1) - schedule count)) terminal) := by
        funext point
        change tests count point * (∫ target, terminal target
          ∂(xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent level ^ (schedule (count + 1) - schedule count)) point) =
          tests count point * ((xiNativeSupTransition system rulesConnected level ^
            (schedule (count + 1) - schedule count)) terminal) point
        rw [xiNativeSupTransition_kernel_power_integral]
      rw [scheduledBackward, induction, endpointIdentity]
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        BanachBackwardObservations.backwardProduct_append, BanachBackwardObservations.backwardProduct]

theorem xiNativeSup_scheduled_pathLaw_integral_backwardProduct (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (schedule : ℕ → ℕ) (scheduleMonotone : Monotone schedule)
    (startsAtZero : schedule 0 = 0) (tests : ℕ → XiVtx system level → ℝ)
    (count : ℕ) (terminal : XiVtx system level → ℝ) (source : XiVtx system level) :
    (∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
      terminal (path (schedule count)) ∂pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (Measure.dirac source)) =
    BanachBackwardObservations.backwardProduct
      (fun index : ℕ => xiNativeSupTransition system rulesConnected level ^
        (schedule (index + 1) - schedule index))
      (fun index : ℕ => ContinuousLinearMap.mul ℝ (XiVtx system level → ℝ) (tests index))
      ((List.range count).map (fun index => (index, index))) terminal source := by
  have actualIntegral := scheduled_pathLaw_integral_backward
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (⟨Measure.dirac source, inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
    schedule scheduleMonotone startsAtZero tests count terminal (fun index => ‖tests index‖) ‖terminal‖
    (fun _ => measurable_of_countable _) (measurable_of_countable _)
    (fun _ => norm_nonneg _) (norm_nonneg _)
    (fun index point => norm_le_pi_norm (tests index) point)
    (fun point => norm_le_pi_norm terminal point)
  simp only [ProbabilityMeasure.coe_mk] at actualIntegral
  rw [actualIntegral, integral_dirac]
  exact congrFun (xiNativeSup_scheduledBackward_eq_backwardProduct system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent level schedule tests count terminal) source

theorem xiNativeSup_absolute_floor_pathLaw_integral_backwardProduct (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
    (tests : ℕ → XiVtx system level → ℝ) (count : ℕ)
    (terminal : XiVtx system level → ℝ) (source : XiVtx system level) :
    (∫ path, (∏ index : Fin count, tests index.val (path (Nat.floor ((times index.val : ℝ) *
      xiNativeFiniteJumpRate system level resistanceRate normalization)))) *
      terminal (path (Nat.floor ((times count : ℝ) *
        xiNativeFiniteJumpRate system level resistanceRate normalization))) ∂pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (Measure.dirac source)) =
    BanachBackwardObservations.backwardProduct
      (fun index : ℕ => xiNativeSupTransition system rulesConnected level ^
        (Nat.floor ((times (index + 1) : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) -
          Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization)))
      (fun index : ℕ => ContinuousLinearMap.mul ℝ (XiVtx system level → ℝ) (tests index))
      ((List.range count).map (fun index => (index, index))) terminal source := by
  apply xiNativeSup_scheduled_pathLaw_integral_backwardProduct system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent level
      (fun index => Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
  · intro first second ordered
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast timesMonotone ordered)
      (xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
        rateNonnegative normalizationNonnegative))
  · simp only [startsAtZero, NNReal.coe_zero, zero_mul, Nat.floor_zero]

end
end EIGS

#print axioms IGS.Sec31.BanachBackwardObservations.backwardProduct_append
#print axioms EIGS.xiNativeSup_scheduledBackward_eq_backwardProduct
#print axioms EIGS.xiNativeSup_scheduled_pathLaw_integral_backwardProduct
#print axioms EIGS.xiNativeSup_absolute_floor_pathLaw_integral_backwardProduct
