import RequestProject.Section31.EIGSWeightedTrace

/-!
# Constructed extended energy and quadratic domain for actual EIGS

The original connected, distance-positive rule graphs produce the weights,
attained trace minima, increasing finite energies and their limiting quadratic
form on the concrete finite-energy domain. The topology used for lower
semicontinuity and liminf here is pointwise convergence on the vertex union.
The separate completion, measure and varying-space weak L² identification are
not part of this theorem.
-/

namespace EIGS

open IGS.Sec31 Filter Topology
open scoped ENNReal

variable {K : ℕ}

noncomputable def xiWeightedEnergyDomain (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) :
    Submodule ℝ (XiVertexUnion system → ℝ) :=
  traceEnergyDomain (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive)

theorem xiWeightedEnergyDomain_iff (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (values : XiVertexUnion system → ℝ) :
    values ∈ xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive ↔
      xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive values ≠ ∞ :=
  traceEnergyFinite_iff_extendedTraceEnergy_ne_top _ values

theorem xiExtendedWeightedEnergy_lowerSemicontinuous (system : EIGSData K)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) :
    LowerSemicontinuous (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive) :=
  extendedTraceEnergy_lowerSemicontinuous _

/-- A genuine quadratic form and pointwise liminf on the actual common vertex
union, with weights constructed from the original rule assumptions. -/
theorem exists_xiLimitEnergy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ quadraticForm : QuadraticForm ℝ
        (xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
          resistanceVector resistanceVectorPositive),
        (∀ values, quadraticForm values =
          (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive values).toReal) ∧
        (∀ values, 0 ≤ quadraticForm values) ∧
        (∀ values : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive,
          Tendsto (fun level =>
            (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive
              resistanceVector resistanceVectorPositive level).energy values) atTop
                (𝓝 (quadraticForm values))) ∧
        (∀ approximation : ℕ → XiVertexUnion system → ℝ,
          ∀ values : XiVertexUnion system → ℝ,
          (∀ vertex, Tendsto (fun index => approximation index vertex) atTop (𝓝 (values vertex))) →
          xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive values ≤
              liminf (fun index => ENNReal.ofReal
                ((xiUnionWeightedNetwork system resistanceRate resistanceRatePositive
                  resistanceVector resistanceVectorPositive index).energy (approximation index))) atTop) := by
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, traceMinima, energyIncreasing⟩ :=
    exists_xiWeighted_trace system rulesConnected distancePositive
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive,
    limitTraceQuadraticForm _ energyIncreasing, ?_, ?_, ?_, ?_⟩
  · intro values
    rfl
  · exact limitTraceQuadraticForm_nonneg _ energyIncreasing
  · exact finite_energy_tendsto_traceEnergyValue _ energyIncreasing
  · exact extendedTraceEnergy_le_liminf_of_increasing _ energyIncreasing

end EIGS
