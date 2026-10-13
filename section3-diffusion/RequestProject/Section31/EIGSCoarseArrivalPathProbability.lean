import RequestProject.Section31.EIGSCoarseArrivalDistance
import RequestProject.Section31.EIGSIncidentStarPathLawExit

/-! The actual walk's displacement event is bounded by completion of its
actual coarse scanner stop. Adjacency is supplied by the actual path law,
not assumed as an extra support condition on the probability estimate. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ProbabilityTheory
open IGS.Sec31.DiscreteMarkov
noncomputable section

variable {K : ℕ}

theorem xiGraphWalkPathLaw_ae_all_adjacent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    [MeasurableSpace (XiVtx system level)] [MeasurableSingletonClass (XiVtx system level)]
    (start : XiVtx system level) :
    ∀ᵐ path ∂xiGraphWalkPathLaw system rulesConnected level start,
      ∀ index, (XiSimpleGraph system level).Adj (path index) (path (index + 1)) := by
  exact ae_all_iff.mpr (fun index => finiteGraphPathLaw_ae_adjacent
    (XiSimpleGraph system level)
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected level vertex)
    start index)

theorem xiGraphWalkPathLaw_displacement_le_coarse_hit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (start : XiVtx system (coarse + steps)) (horizon count : ℕ) :
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
      {path | ∃ time, time ≤ horizon ∧
        (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0))} ≤
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
      {path | ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps))
        count (horizon + 1)).time path).val ≤ horizon} := by
  apply measure_mono_ae
  filter_upwards [xiGraphWalkPathLaw_ae_all_adjacent system rulesConnected (coarse + steps) start]
    with path adjacency
  intro displacement
  exact xiBoundedCoarseArrival_le_of_displacement system rulesConnected parameters rateGeTwo
    coarse steps path horizon count (fun index _ => adjacency index) displacement

theorem xiCanonicalWalk_displacement_le_coarse_hit_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (start : XiVtx system (coarse + steps)) (horizon count : ℕ) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
      {path | ∃ time, time ≤ horizon ∧
        (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0))} ≤
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
      {path | ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps))
        count (horizon + 1)).time path).val ≤ horizon} := by
  intro parameters
  exact xiGraphWalkPathLaw_displacement_le_coarse_hit system rulesConnected parameters
    (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    coarse steps start horizon count

end
end EIGS

#print axioms EIGS.xiGraphWalkPathLaw_ae_all_adjacent
#print axioms EIGS.xiGraphWalkPathLaw_displacement_le_coarse_hit
#print axioms EIGS.xiCanonicalWalk_displacement_le_coarse_hit_of_rules
