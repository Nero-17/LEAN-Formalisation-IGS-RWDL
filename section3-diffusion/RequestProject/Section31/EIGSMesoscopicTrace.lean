import RequestProject.Section31.EIGSNonstationaryHarmonics
import RequestProject.Section31.EIGSVertexInclusion

/-! Actual unit-resistance Dirichlet minima and their restrictions at any
mesoscopic level. Native vertex types and the original fine index are retained.
The minimum and its trace are constructed, rather than supplied as inputs. -/

namespace EIGS

open IGS.Sec31

set_option maxHeartbeats 1800000

variable {K : ℕ}

section Connected

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)

include rulesConnected

theorem exists_xiPotential_atLevel_trace (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (oldValues : XiVtx system coarseLevel → ℝ) :
    ∃ extension : XiVtx system fineLevel → ℝ,
      (∀ vertex, extension (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex) ∧
      ((XiNetwork system fineLevel).potentialNetwork resistances resistancesPositive).energy extension =
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[fineLevel - coarseLevel] resistances)
          (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive (fineLevel - coarseLevel))).energy oldValues ∧
      ∀ competitor : XiVtx system fineLevel → ℝ,
        (∀ vertex, competitor (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex) →
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[fineLevel - coarseLevel] resistances)
          (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive (fineLevel - coarseLevel))).energy oldValues ≤
        ((XiNetwork system fineLevel).potentialNetwork resistances resistancesPositive).energy competitor := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le levelsOrdered
  simpa only [xiVertexInclusion_eq_forward, Nat.add_sub_cancel_left] using
    exists_xiPotential_iterated_trace system rulesConnected coarseLevel offset resistances resistancesPositive oldValues

theorem xiPotential_atLevel_restriction_le (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (values : XiVtx system fineLevel → ℝ) :
    ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[fineLevel - coarseLevel] resistances)
      (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive (fineLevel - coarseLevel))).energy
        (fun vertex => values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex)) ≤
      ((XiNetwork system fineLevel).potentialNetwork resistances resistancesPositive).energy values := by
  obtain ⟨extension, extensionBoundary, extensionEnergy, lowerBound⟩ :=
    exists_xiPotential_atLevel_trace system rulesConnected coarseLevel fineLevel levelsOrdered resistances resistancesPositive
      (fun vertex => values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex))
  exact lowerBound values (fun _ => rfl)

theorem exists_xiUnit_atLevel_minimum (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (oldValues : XiVtx system coarseLevel → ℝ) :
    ∃ extension : XiVtx system fineLevel → ℝ,
      (∀ vertex, extension (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex) ∧
      ∀ competitor : XiVtx system fineLevel → ℝ,
        (∀ vertex, competitor (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex) →
        ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy extension ≤
          ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor := by
  obtain ⟨extension, extensionBoundary, extensionEnergy, lowerBound⟩ :=
    exists_xiPotential_atLevel_trace system rulesConnected coarseLevel fineLevel levelsOrdered (fun _ => 1)
      (fun _ => by norm_num) oldValues
  refine ⟨extension, extensionBoundary, ?_⟩
  intro competitor competitorBoundary
  rw [extensionEnergy]
  exact lowerBound competitor competitorBoundary

noncomputable def xiUnitPotentialAt (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (oldValues : XiVtx system coarseLevel → ℝ) : XiVtx system fineLevel → ℝ :=
  Classical.choose (exists_xiUnit_atLevel_minimum system rulesConnected coarseLevel fineLevel levelsOrdered oldValues)

theorem xiUnitPotentialAt_boundary (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (oldValues : XiVtx system coarseLevel → ℝ) (vertex : XiVtx system coarseLevel) :
    xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered oldValues
      (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex :=
  (Classical.choose_spec (exists_xiUnit_atLevel_minimum system rulesConnected coarseLevel fineLevel levelsOrdered oldValues)).1 vertex

theorem xiUnitPotentialAt_minimal (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (oldValues : XiVtx system coarseLevel → ℝ)
    (competitor : XiVtx system fineLevel → ℝ)
    (competitorBoundary : ∀ vertex, competitor (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = oldValues vertex) :
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
      (xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered oldValues) ≤
      ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor :=
  (Classical.choose_spec (exists_xiUnit_atLevel_minimum system rulesConnected coarseLevel fineLevel levelsOrdered oldValues)).2
    competitor competitorBoundary

theorem xiUnitPotentialAt_mesoscopic_minimal (coarseLevel middleLevel fineLevel : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (middleFine : middleLevel ≤ fineLevel)
    (oldValues : XiVtx system coarseLevel → ℝ) (competitor : XiVtx system middleLevel → ℝ)
    (competitorBoundary : ∀ vertex,
      competitor (xiVertexInclusion system coarseLevel middleLevel coarseMiddle vertex) = oldValues vertex) :
    ((XiNetwork system middleLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[fineLevel - middleLevel] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) (fineLevel - middleLevel))).energy
        (fun vertex => xiUnitPotentialAt system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) oldValues
          (xiVertexInclusion system middleLevel fineLevel middleFine vertex)) ≤
    ((XiNetwork system middleLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[fineLevel - middleLevel] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) (fineLevel - middleLevel))).energy competitor := by
  obtain ⟨extension, extensionBoundary, extensionEnergy, lowerBound⟩ :=
    exists_xiPotential_atLevel_trace system rulesConnected middleLevel fineLevel middleFine (fun _ => 1) (fun _ => by norm_num) competitor
  have extensionCoarse : ∀ vertex,
      extension (xiVertexInclusion system coarseLevel fineLevel (coarseMiddle.trans middleFine) vertex) = oldValues vertex := by
    intro vertex
    rw [← xiVertexInclusion_comp system coarseLevel middleLevel fineLevel coarseMiddle middleFine]
    exact (extensionBoundary _).trans (competitorBoundary vertex)
  exact (xiPotential_atLevel_restriction_le system rulesConnected middleLevel fineLevel middleFine (fun _ => 1)
    (fun _ => by norm_num) _).trans
      ((xiUnitPotentialAt_minimal system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) oldValues
        extension extensionCoarse).trans_eq extensionEnergy)

theorem xiUnitPotentialAt_eq_mesoscopic_potentialValues (coarseLevel middleLevel offset : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (oldValues : XiVtx system coarseLevel → ℝ) :
    xiUnitPotentialAt system rulesConnected coarseLevel (middleLevel + offset)
        (coarseMiddle.trans (Nat.le_add_right _ _)) oldValues =
      xiPotentialValues system rulesConnected middleLevel offset (fun _ => 1) (fun _ => by norm_num)
        (fun vertex => xiUnitPotentialAt system rulesConnected coarseLevel (middleLevel + offset)
          (coarseMiddle.trans (Nat.le_add_right _ _)) oldValues
            (xiVertexInclusion system middleLevel (middleLevel + offset) (Nat.le_add_right _ _) vertex)) := by
  apply xiPotentialValues_unique system rulesConnected middleLevel offset (fun _ => 1) (fun _ => by norm_num)
  · intro vertex
    rw [xiVertexInclusion_eq_forward]
  · intro competitor competitorBoundary
    apply xiUnitPotentialAt_minimal system rulesConnected coarseLevel (middleLevel + offset)
      (coarseMiddle.trans (Nat.le_add_right _ _)) oldValues competitor
    intro vertex
    rw [← xiVertexInclusion_comp system coarseLevel middleLevel (middleLevel + offset) coarseMiddle (Nat.le_add_right _ _),
      xiVertexInclusion_eq_forward, competitorBoundary]
    rw [xiVertexInclusion_comp, xiUnitPotentialAt_boundary]

end Connected

end EIGS
