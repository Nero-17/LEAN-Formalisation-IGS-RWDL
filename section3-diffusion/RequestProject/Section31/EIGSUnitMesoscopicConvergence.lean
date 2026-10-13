import RequestProject.Section31.EIGSUnitMesoscopicProfiles
import RequestProject.Section31.EIGSHarmonicTraceMinimum

/-! Actual original-unit fine harmonic functions converge on every fixed
mesoscopic vertex set to the constructed stationary weighted harmonics.
Finite trace minima, their identification and the Perron convergence are
proved from original rules in the final theorem. -/

namespace EIGS

open IGS.Sec31 Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem xiHarmonicValues_eq_mesoscopic_boundaryProfile (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel offset : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (middleBoundaryValues : XiVtx system (initialLevel + offset) → ℝ)
    (boundaryAgreement : ∀ vertex,
      middleBoundaryValues (xiForward system initialLevel offset vertex) = initialValues vertex) :
    xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair initialLevel initialValues offset =
      (XiNetwork system (initialLevel + offset)).boundaryPotentialProfile resistanceVector vectorPositive
        (xiSimpleGraph_connected system rulesConnected (initialLevel + offset))
        (xiMesoscopicBoundary system initialLevel (initialLevel + offset) (Nat.le_add_right _ _))
        (xiMesoscopicBoundary_nonempty system initialLevel (initialLevel + offset) (Nat.le_add_right _ _)) middleBoundaryValues := by
  classical
  apply (XiNetwork system (initialLevel + offset)).potential_minimum_unique resistanceVector vectorPositive
    (xiSimpleGraph_connected system rulesConnected (initialLevel + offset))
    (xiMesoscopicBoundary system initialLevel (initialLevel + offset) (Nat.le_add_right _ _))
    (xiMesoscopicBoundary_nonempty system initialLevel (initialLevel + offset) (Nat.le_add_right _ _)) middleBoundaryValues
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    rw [xiVertexInclusion_eq_forward]
    exact (xiHarmonicValues_initial_boundary system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair initialLevel offset initialValues coarseVertex).trans (boundaryAgreement coarseVertex).symm
  · exact (XiNetwork system (initialLevel + offset)).boundaryPotentialProfile_boundary _ _ _ _ _ _
  · intro competitor competitorBoundary
    apply xiHarmonicValues_potential_minimal system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair initialLevel offset initialValues competitor
    intro vertex
    have boundaryValue := competitorBoundary
      (xiVertexInclusion system initialLevel (initialLevel + offset) (Nat.le_add_right _ _) vertex)
      (by simp [xiMesoscopicBoundary])
    rw [xiVertexInclusion_eq_forward] at boundaryValue
    exact boundaryValue.trans (boundaryAgreement vertex)
  · exact (XiNetwork system (initialLevel + offset)).boundaryPotentialProfile_minimal _ _ _ _ _ _

theorem xiUnitPotentialAt_mesoscopic_harmonic_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (initialLevel middleOffset : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    Tendsto (fun offset => ‖(fun vertex : XiVtx system (initialLevel + middleOffset) =>
        xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + offset)
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
          (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + offset) (Nat.le_add_right _ _) vertex)) -
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues middleOffset‖) atTop (nhds 0) := by
  have initialAgreement := xiHarmonicValues_initial_boundary system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair initialLevel middleOffset initialValues
  have middleAgreement : ∀ vertex,
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues middleOffset
          (xiVertexInclusion system initialLevel (initialLevel + middleOffset) (Nat.le_add_right _ _) vertex) = initialValues vertex := by
    intro vertex
    rw [xiVertexInclusion_eq_forward]
    exact initialAgreement vertex
  have convergence := xiUnitPotentialAt_mesoscopic_restriction_tendsto system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence initialLevel (initialLevel + middleOffset)
    (Nat.le_add_right _ _) initialValues
    (xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair initialLevel initialValues middleOffset) middleAgreement
  have limitIdentity := xiHarmonicValues_eq_mesoscopic_boundaryProfile system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair initialLevel middleOffset initialValues
    (xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair initialLevel initialValues middleOffset) initialAgreement
  simpa only [← limitIdentity] using convergence

theorem exists_xiUnitPotentialAt_mesoscopic_harmonic_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate normalization : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ normalizationPositive : 0 < normalization,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel middleOffset (initialValues : XiVtx system initialLevel → ℝ),
        Tendsto (fun offset => ‖(fun vertex : XiVtx system (initialLevel + middleOffset) =>
          xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + offset)
            ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
            (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + offset) (Nat.le_add_right _ _) vertex)) -
          xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair initialLevel initialValues middleOffset‖) atTop (nhds 0) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  exact ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive, vectorPositive, coordinateEigenpair,
    xiUnitPotentialAt_mesoscopic_harmonic_tendsto system rulesConnected resistanceRate normalization ratePositive normalizationPositive
      resistanceVector vectorPositive coordinateEigenpair normalizedConvergence⟩

end EIGS
