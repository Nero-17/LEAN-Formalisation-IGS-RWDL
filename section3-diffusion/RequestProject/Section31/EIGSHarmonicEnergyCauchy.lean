import RequestProject.Section31.EIGSEnergyRecovery
import RequestProject.Section31.TraceEnergyPointwiseClosability

/-! Compatible actual harmonic projections of any finite-energy union function
are energy Cauchy. The union function need not be continuous on the completion. -/

namespace EIGS

open IGS.Sec31 Filter Topology

set_option maxHeartbeats 2400000

variable {K : ℕ}

section Eigenpair

variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily connected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (target : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (approximation : ℕ → xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (harmonic : ∀ level, approximation level ∈ xiHarmonicCoreAt system resistanceRate ratePositive resistanceVector vectorPositive level)
    (boundary : ∀ level vertex, (approximation level).val (xiVertexEmbedding system level vertex) =
      target.val (xiVertexEmbedding system level vertex))

include connected eigenpair harmonic boundary

theorem xiHarmonicCompatible_energy_tendsto :
    Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level)).toReal) atTop
      (nhds ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal)) := by
  have convergence := finite_energy_tendsto_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system connected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair) target
  convert convergence using 1
  ext level
  rw [harmonic level, ENNReal.toReal_ofReal
    ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy_nonneg _)]
  change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
    ((approximation level).val ∘ xiVertexEmbedding system level) =
      (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
        (target.val ∘ xiVertexEmbedding system level)
  exact congrArg _ (funext (boundary level))

theorem xiHarmonicCompatible_residual_tendsto :
    Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target - approximation level)).toReal) atTop (nhds 0) := by
  have convergence := (tendsto_const_nhds (x :=
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal)).sub
      (xiHarmonicCompatible_energy_tendsto system connected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair target approximation harmonic boundary)
  rw [sub_self] at convergence
  apply convergence.congr
  intro level
  have pythagoras := xiHarmonicCoreAt_energy_pythagoras system connected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair level (approximation level) target (harmonic level)
      (fun vertex => (boundary level vertex).symm)
  linarith

theorem xiHarmonicCompatible_energy_cauchy :
    ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (approximation first - approximation second)).toReal < tolerance := by
  intro tolerance positive
  have residualSmall := (xiHarmonicCompatible_residual_tendsto system connected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair target approximation harmonic boundary).eventually
      (gt_mem_nhds (show (0 : ℝ) < tolerance / 4 by positivity))
  obtain ⟨threshold, afterThreshold⟩ := eventually_atTop.1 residualSmall
  refine ⟨threshold, ?_⟩
  intro first firstAfter second secondAfter
  have differenceBound := traceEnergyValue_difference_bound
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (approximation first - approximation second) (target - approximation second)
  have differenceIdentity : approximation first - approximation second - (target - approximation second) =
      -(target - approximation first) := by abel
  rw [differenceIdentity] at differenceBound
  have negationIdentity := (limitTraceQuadraticForm
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system connected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair)).map_neg (target - approximation first)
  change traceEnergyValue _ (-(target - approximation first)) = traceEnergyValue _ (target - approximation first) at negationIdentity
  rw [negationIdentity] at differenceBound
  have firstSmall := afterThreshold first firstAfter
  have secondSmall := afterThreshold second secondAfter
  change (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation first - approximation second)).toReal ≤
    2 * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target - approximation first)).toReal +
    2 * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target - approximation second)).toReal at differenceBound
  linarith

end Eigenpair

end EIGS

#print axioms EIGS.xiHarmonicCompatible_energy_tendsto
#print axioms EIGS.xiHarmonicCompatible_residual_tendsto
#print axioms EIGS.xiHarmonicCompatible_energy_cauchy
