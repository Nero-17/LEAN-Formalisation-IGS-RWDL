import RequestProject.Section31.EIGSUnitMesoscopicConvergence
import RequestProject.Section31.EIGSGeometricCellOscillation
import RequestProject.Section31.EIGSAddressSupport

/-! An actual fine unit-resistance minimizer is controlled by its middle-level
restriction and the stationary harmonic oscillation on the very same cell. -/

namespace EIGS

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem abs_sub_le_of_near_endpoint_intervals
    (first second firstLimit secondLimit value limitValue error oscillation : ℝ)
    (valueRange : min first second ≤ value ∧ value ≤ max first second)
    (limitRange : min firstLimit secondLimit ≤ limitValue ∧ limitValue ≤ max firstLimit secondLimit)
    (firstError : |first - firstLimit| ≤ error)
    (secondError : |second - secondLimit| ≤ error)
    (endpointOscillation : |firstLimit - secondLimit| ≤ oscillation) :
    |value - limitValue| ≤ error + 2 * oscillation := by
  have firstBounds := abs_le.1 firstError
  have secondBounds := abs_le.1 secondError
  have oscillationBounds := abs_le.1 endpointOscillation
  have valueLower : firstLimit - (error + oscillation) ≤ value :=
    (le_min (by linarith) (by linarith)).trans valueRange.1
  have valueUpper : value ≤ firstLimit + (error + oscillation) :=
    valueRange.2.trans (max_le (by linarith) (by linarith))
  have limitLower : firstLimit - oscillation ≤ limitValue :=
    (le_min (by linarith [abs_nonneg (firstLimit - secondLimit)]) (by linarith)).trans limitRange.1
  have limitUpper : limitValue ≤ firstLimit + oscillation :=
    limitRange.2.trans (max_le (by linarith [abs_nonneg (firstLimit - secondLimit)]) (by linarith))
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem xiUnitPotentialAt_descendant_endpoint_range (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (initialLevel middleLevel fineOffset : ℕ) (initialMiddle : initialLevel ≤ middleLevel)
    (initialValues : XiVtx system initialLevel → ℝ)
    (edge : XiEdge system.toRuleData (middleLevel + fineOffset)) :
    let values := xiUnitPotentialAt system rulesConnected initialLevel (middleLevel + fineOffset)
      (initialMiddle.trans (Nat.le_add_right _ _)) initialValues
    let middleValues := fun vertex => values
      (xiVertexInclusion system middleLevel (middleLevel + fineOffset) (Nat.le_add_right _ _) vertex)
    let ancestor := xiAncestorEdge system middleLevel fineOffset edge
    (min (middleValues (XiTail system middleLevel ancestor)) (middleValues (XiHead system middleLevel ancestor)) ≤
        values (XiTail system (middleLevel + fineOffset) edge) ∧
      values (XiTail system (middleLevel + fineOffset) edge) ≤
        max (middleValues (XiTail system middleLevel ancestor)) (middleValues (XiHead system middleLevel ancestor))) ∧
    (min (middleValues (XiTail system middleLevel ancestor)) (middleValues (XiHead system middleLevel ancestor)) ≤
        values (XiHead system (middleLevel + fineOffset) edge) ∧
      values (XiHead system (middleLevel + fineOffset) edge) ≤
        max (middleValues (XiTail system middleLevel ancestor)) (middleValues (XiHead system middleLevel ancestor))) := by
  dsimp only
  have endpointRange := xiPotentialValues_descendant_endpoint_range system rulesConnected middleLevel
    (fun vertex => xiUnitPotentialAt system rulesConnected initialLevel (middleLevel + fineOffset)
      (initialMiddle.trans (Nat.le_add_right _ _)) initialValues
        (xiVertexInclusion system middleLevel (middleLevel + fineOffset) (Nat.le_add_right _ _) vertex))
    fineOffset (fun _ => 1) (fun _ => by norm_num) edge
  rw [← xiUnitPotentialAt_eq_mesoscopic_potentialValues system rulesConnected initialLevel middleLevel fineOffset
    initialMiddle initialValues] at endpointRange
  exact endpointRange

theorem xiUnitPotentialAt_uniform_error_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ)
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues offset vertex)
    (middleOffset fineOffset : ℕ) (oscillation : ℝ)
    (middleEdgeBound : ∀ edge : XiEdge system.toRuleData (initialLevel + middleOffset),
      |xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset (XiTail system (initialLevel + middleOffset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset (XiHead system (initialLevel + middleOffset) edge)| ≤ oscillation)
    (vertex : XiVtx system ((initialLevel + middleOffset) + fineOffset)) :
    |xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues vertex -
      extension (xiVertexEmbedding system ((initialLevel + middleOffset) + fineOffset) vertex)| ≤
      ‖(fun middleVertex : XiVtx system (initialLevel + middleOffset) =>
        xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
          (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + fineOffset)
            (Nat.le_add_right _ _) middleVertex)) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset‖ + 2 * oscillation := by
  obtain ⟨edge, incidence⟩ := xiVertex_has_incident_edge system rulesConnected _ vertex
  have endpointRange := xiUnitPotentialAt_descendant_endpoint_range system rulesConnected initialLevel
    (initialLevel + middleOffset) fineOffset (Nat.le_add_right _ _) initialValues edge
  have extensionSteps := xiHarmonic_union_steps system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair initialLevel initialValues extension extensionValues
  have middleExtensionValues := xiUnion_values_eq_harmonicValues_of_steps system rulesConnected resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair (initialLevel + middleOffset) extension
    (fun level afterMiddle => extensionSteps level ((Nat.le_add_right _ _).trans afterMiddle))
  have membership : xiVertexEmbedding system ((initialLevel + middleOffset) + fineOffset) vertex ∈
      xiDescendantCellVertices system (initialLevel + middleOffset)
        (xiAncestorEdge system (initialLevel + middleOffset) fineOffset edge) := by
    exact ⟨fineOffset, edge, rfl, incidence.imp (congrArg _) (congrArg _)⟩
  have limitRange := xiHarmonic_union_cell_range system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair (initialLevel + middleOffset)
    (extension ∘ xiVertexEmbedding system (initialLevel + middleOffset)) extension middleExtensionValues _ _ membership
  simp only [Function.comp_apply, extensionValues] at limitRange
  have endpointErrors : ∀ middleVertex : XiVtx system (initialLevel + middleOffset),
      |xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
          (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + fineOffset)
            (Nat.le_add_right _ _) middleVertex) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset middleVertex| ≤
      ‖(fun middleVertex : XiVtx system (initialLevel + middleOffset) =>
        xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
          (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + fineOffset)
            (Nat.le_add_right _ _) middleVertex)) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset‖ := by
    intro middleVertex
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm
      ((fun middleVertex : XiVtx system (initialLevel + middleOffset) =>
        xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
          (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + fineOffset)
            (Nat.le_add_right _ _) middleVertex)) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues middleOffset) middleVertex
  rcases incidence with tailEquality | headEquality
  · rw [tailEquality] at endpointRange
    exact abs_sub_le_of_near_endpoint_intervals _ _ _ _ _ _ _ _ endpointRange.1 limitRange
      (endpointErrors _) (endpointErrors _) (middleEdgeBound _)
  · rw [headEquality] at endpointRange
    exact abs_sub_le_of_near_endpoint_intervals _ _ _ _ _ _ _ _ endpointRange.2 limitRange
      (endpointErrors _) (endpointErrors _) (middleEdgeBound _)

end EIGS
