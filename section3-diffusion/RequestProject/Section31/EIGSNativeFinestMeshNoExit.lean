import RequestProject.Section31.EIGSNativeRadiusExponentialEnvelope
import RequestProject.Section31.EIGSAnchoredWindowDisplacementTail

/-! At the finest mesh, each actual graph jump has bounded completion
distance. A ball cannot be exited in fewer than the required number of
jumps. This supplies the deterministic fine-mesh branch of the exponential
tail optimization, without a probabilistic tail hypothesis. -/

namespace IGS.Sec31

theorem path_dist_le_index_mul_step_bound
    {State : Type*} [PseudoMetricSpace State] (path : ℕ → State)
    (stepBound : ℝ) (adjacentBound : ∀ index, dist (path (index + 1)) (path index) ≤ stepBound) :
    ∀ index : ℕ, dist (path index) (path 0) ≤ (index : ℝ) * stepBound := by
  intro index
  induction index with
  | zero => simp
  | succ index inductionHypothesis =>
    calc
      _ ≤ dist (path (index + 1)) (path index) + dist (path index) (path 0) := dist_triangle _ _ _
      _ ≤ stepBound + (index : ℝ) * stepBound := add_le_add (adjacentBound index) inductionHypothesis
      _ = _ := by push_cast; ring

end IGS.Sec31

namespace EIGS
open MeasureTheory ProbabilityTheory IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiNativeMaximalDisplacementEvent_eq_zero_of_finest_mesh
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (level horizon : ℕ) (start : XiVtx system level) (radius : ℝ)
    [MeasurableSpace (XiVtx system level)] [MeasurableSingletonClass (XiVtx system level)]
    (beforeExit : (horizon : ℝ) * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ level < radius) :
    xiGraphWalkPathLaw system rulesConnected level start
      (xiNativeMaximalDisplacementEvent system rulesConnected parameters level horizon start radius) = 0 := by
  let law := xiGraphWalkPathLaw system rulesConnected level start
  have starts : ∀ᵐ path ∂law, path 0 = start :=
    finiteGraphPathLaw_ae_start (XiSimpleGraph system level)
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex)) start
  have adjacency : ∀ᵐ path ∂law, ∀ index : ℕ,
      (XiSimpleGraph system level).Adj (path index) (path (index + 1)) := by
    apply ae_all_iff.mpr
    intro index
    simpa only [law, xiGraphWalkPathLaw] using
      finiteGraphPathLaw_ae_adjacent_of_probability (XiSimpleGraph system level)
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex))
        (⟨Measure.dirac start, inferInstance⟩ : ProbabilityMeasure (XiVtx system level)) index
  have noExit : ∀ᵐ path ∂law,
      path ∉ xiNativeMaximalDisplacementEvent system rulesConnected parameters level horizon start radius := by
    filter_upwards [starts, adjacency] with path started adjacent
    have stepBounds (index : ℕ) :
        dist (parameters.vertexEmbedding level (path (index + 1)))
          (parameters.vertexEmbedding level (path index)) ≤
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ level := by
      simpa only [parameters.normalized, one_mul] using
        xiCompletionEmbedding_adj_distance_le system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair level
          (adjacent index).symm
    rintro ⟨index, bounded, displaced⟩
    have distanceBound := path_dist_le_index_mul_step_bound
      (fun index => parameters.vertexEmbedding level (path index))
      ((system.distanceSpectralRadius rulesConnected)⁻¹ ^ level) stepBounds index
    rw [started] at distanceBound
    have indexBound : (index : ℝ) ≤ (horizon : ℝ) := by exact_mod_cast bounded
    have scaled := mul_le_mul_of_nonneg_right indexBound
      (pow_nonneg (inv_nonneg.mpr parameters.ratePositive.le) level)
    exact (not_le_of_gt (distanceBound.trans_lt (scaled.trans_lt beforeExit))) displaced
  simpa only [not_not] using ae_iff.mp noExit

end
end EIGS

#print axioms IGS.Sec31.path_dist_le_index_mul_step_bound
#print axioms EIGS.xiNativeMaximalDisplacementEvent_eq_zero_of_finest_mesh
