import RequestProject.Section31.TraceEnergyAnchoredCompleteness
import RequestProject.Section31.EIGSMetricCompletion
import RequestProject.Section31.EIGSWeightedTrace
import RequestProject.Section31.DirichletThomson

/-! Point evaluation and anchored energy completeness on the actual vertex
union. Every evaluation coefficient is supplied by an actual connected finite
network containing both points. No resistance metric or Hilbert completeness
is assumed. Extending all finite-energy functions to the metric completion is
a separate obligation in the resistanceRate > 1 regime. -/

namespace EIGS

open IGS.Sec31 Filter Topology
noncomputable section
variable {K : ℕ}

theorem exists_xiWeightedEnergy_anchored_evaluation
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (anchor vertex : XiVertexUnion system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ values : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive,
        (values.val vertex) ^ 2 ≤ coefficient *
          ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            values.val).toReal + (values.val anchor) ^ 2) := by
  let level := max (xiUnionBirth system anchor) (xiUnionBirth system vertex)
  let finiteAnchor := xiVertexAtLevel system anchor level (le_max_left _ _)
  let finiteVertex := xiVertexAtLevel system vertex level (le_max_right _ _)
  obtain ⟨bound, nonnegative, control⟩ := (XiNetwork system level).exists_potential_poincare_constant
    resistanceVector vectorPositive finiteAnchor (xiSimpleGraph_connected system rulesConnected level)
  refine ⟨2 * (bound / resistanceRate ^ level + 1), by positivity, ?_⟩
  intro values
  let restriction : XiVtx system level → ℝ := values.val ∘ xiVertexEmbedding system level
  have anchorValue : restriction finiteAnchor = values.val anchor := by
    simp only [restriction, Function.comp_apply, finiteAnchor, xiVertexEmbedding_atLevel]
  have vertexValue : restriction finiteVertex = values.val vertex := by
    simp only [restriction, Function.comp_apply, finiteVertex, xiVertexEmbedding_atLevel]
  have energyShift : ((XiNetwork system level).potentialNetwork resistanceVector vectorPositive).energy
      (fun point => restriction point - values.val anchor) =
      ((XiNetwork system level).potentialNetwork resistanceVector vectorPositive).energy restriction := by
    simp only [FiniteNetwork.energy]
    apply Finset.sum_congr rfl
    intro edge _
    congr 1
    ring
  have oscillation := control (fun point => restriction point - values.val anchor)
    (by rw [anchorValue]; simp) finiteVertex
  rw [energyShift, vertexValue] at oscillation
  have finiteBound := finite_energy_le_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive) values level
  change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
    restriction ≤ _ at finiteBound
  rw [xiWeightedFiniteNetwork_energy_eq_potential] at finiteBound
  have scaledOscillation : (values.val vertex - values.val anchor) ^ 2 ≤
      (bound / resistanceRate ^ level) *
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          values.val).toReal := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos ratePositive level)).2
    calc
      (values.val vertex - values.val anchor) ^ 2 * resistanceRate ^ level ≤
        (bound * ((XiNetwork system level).potentialNetwork resistanceVector vectorPositive).energy restriction) *
          resistanceRate ^ level := mul_le_mul_of_nonneg_right oscillation (pow_pos ratePositive level).le
      _ = bound * (resistanceRate ^ level *
        ((XiNetwork system level).potentialNetwork resistanceVector vectorPositive).energy restriction) := by ring
      _ ≤ bound * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.val).toReal := mul_le_mul_of_nonneg_left finiteBound nonnegative
  have coefficientNonnegative : 0 ≤ bound / resistanceRate ^ level := by positivity
  have energyNonnegative : 0 ≤ (xiExtendedWeightedEnergy system resistanceRate ratePositive
    resistanceVector vectorPositive values.val).toReal := ENNReal.toReal_nonneg
  nlinarith [sq_nonneg (values.val vertex - 2 * values.val anchor),
    mul_nonneg coefficientNonnegative (sq_nonneg (values.val anchor))]

theorem exists_xiWeightedEnergy_anchored_cauchy_limit
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (anchor : XiVertexUnion system)
    (sequence : ℕ → xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (cauchy : ∀ tolerance > 0, ∃ threshold : ℕ,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        traceEnergyValue (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
          (sequence first - sequence second) +
          ((sequence first).val anchor - (sequence second).val anchor) ^ 2 < tolerance) :
    ∃ limit : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive,
      (∀ vertex, Tendsto (fun index => (sequence index).val vertex) atTop (𝓝 (limit.val vertex))) ∧
      ∀ tolerance > 0, ∀ᶠ index in atTop,
        traceEnergyValue (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
          (sequence index - limit) +
          ((sequence index).val anchor - limit.val anchor) ^ 2 ≤ tolerance := by
  exact exists_traceEnergy_anchored_cauchy_limit _ anchor
    (exists_xiWeightedEnergy_anchored_evaluation system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive anchor) sequence cauchy

end
end EIGS

#print axioms EIGS.exists_xiWeightedEnergy_anchored_evaluation
#print axioms EIGS.exists_xiWeightedEnergy_anchored_cauchy_limit
