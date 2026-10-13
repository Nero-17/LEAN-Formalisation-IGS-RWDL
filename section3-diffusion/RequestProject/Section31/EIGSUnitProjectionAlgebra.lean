import RequestProject.Section31.EIGSDiscreteTraceProfileAlgebra
import RequestProject.Section31.EIGSMesoscopicTrace

/-! The actual unit-energy projection onto a finite skeleton. Its orthogonality
and Pythagorean identity refer to graph energy, not to the native L² product. -/

namespace EIGS

variable {K : ℕ}

noncomputable section

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)

def xiUnitEnergyProjection (coarseLevel fineLevel : ℕ) (levelsOrdered : coarseLevel ≤ fineLevel)
    (values : XiVtx system fineLevel → ℝ) : XiVtx system fineLevel → ℝ :=
  (XiNetwork system fineLevel).boundaryPotentialProfile (fun _ => 1) (fun _ => by norm_num)
    (xiSimpleGraph_connected system rulesConnected fineLevel)
    (Finset.univ.image (xiVertexInclusion system coarseLevel fineLevel levelsOrdered))
    ⟨xiVertexInclusion system coarseLevel fineLevel levelsOrdered (xiPositiveTerminal system coarseLevel), by simp⟩ values

theorem xiUnitEnergyProjection_boundary (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ)
    (vertex : XiVtx system coarseLevel) :
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values
      (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) =
        values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) := by
  classical
  exact (XiNetwork system fineLevel).boundaryPotentialProfile_boundary _ _ _ _ _ values _ (by simp)

theorem xiUnitEnergyProjection_minimal (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (values competitor : XiVtx system fineLevel → ℝ)
    (competitorBoundary : ∀ vertex : XiVtx system coarseLevel,
      competitor (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) =
        values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex)) :
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
      (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values) ≤
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor := by
  classical
  apply (XiNetwork system fineLevel).boundaryPotentialProfile_minimal
  intro vertex membership
  obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
  exact competitorBoundary coarseVertex

theorem xiUnitEnergyProjection_eq_potentialAt (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ) :
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values =
      xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
        (fun vertex => values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex)) := by
  classical
  apply (XiNetwork system fineLevel).potential_minimum_unique (fun _ => 1) (fun _ => by norm_num)
    (xiSimpleGraph_connected system rulesConnected fineLevel)
    (Finset.univ.image (xiVertexInclusion system coarseLevel fineLevel levelsOrdered))
    ⟨xiVertexInclusion system coarseLevel fineLevel levelsOrdered (xiPositiveTerminal system coarseLevel), by simp⟩ values
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiUnitEnergyProjection_boundary system rulesConnected coarseLevel fineLevel levelsOrdered values coarseVertex
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiUnitPotentialAt_boundary system rulesConnected coarseLevel fineLevel levelsOrdered _ coarseVertex
  · intro competitor competitorBoundary
    exact xiUnitEnergyProjection_minimal system rulesConnected coarseLevel fineLevel levelsOrdered values competitor
      (fun vertex => competitorBoundary _ (by simp))
  · intro competitor competitorBoundary
    exact xiUnitPotentialAt_minimal system rulesConnected coarseLevel fineLevel levelsOrdered _ competitor
      (fun vertex => competitorBoundary _ (by simp))

theorem xiUnitEnergyProjection_linear (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (first second : XiVtx system fineLevel → ℝ)
    (firstScalar secondScalar : ℝ) :
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered
      (fun vertex => firstScalar * first vertex + secondScalar * second vertex) =
    (fun vertex => firstScalar * xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered first vertex +
      secondScalar * xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered second vertex) := by
  classical
  exact (XiNetwork system fineLevel).boundaryPotentialProfile_linear _ _ _ _ _ first second firstScalar secondScalar

theorem xiUnitEnergyProjection_energy_identity (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ) :
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
      ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values) +
      ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (values - xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values) := by
  classical
  apply ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy_sub_of_min
    (↑(Finset.univ.image (xiVertexInclusion system coarseLevel fineLevel levelsOrdered)) : Set (XiVtx system fineLevel)) values
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiUnitEnergyProjection_boundary system rulesConnected coarseLevel fineLevel levelsOrdered values coarseVertex
  · intro competitor competitorBoundary
    exact xiUnitEnergyProjection_minimal system rulesConnected coarseLevel fineLevel levelsOrdered values competitor
      (fun vertex => competitorBoundary _ (by simp))
  · intro vertex membership
    rfl

theorem xiUnitEnergyProjection_refl (level : ℕ) (values : XiVtx system level → ℝ) :
    xiUnitEnergyProjection system rulesConnected level level le_rfl values = values := by
  funext vertex
  simpa only [xiVertexInclusion_refl] using
    xiUnitEnergyProjection_boundary system rulesConnected level level le_rfl values vertex

theorem xiUnitEnergyProjection_nested (coarseLevel middleLevel fineLevel : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (middleFine : middleLevel ≤ fineLevel)
    (values : XiVtx system fineLevel → ℝ) :
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine)
      (xiUnitEnergyProjection system rulesConnected middleLevel fineLevel middleFine values) =
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values := by
  rw [xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine),
    xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values]
  congr 1
  funext vertex
  rw [← xiVertexInclusion_comp system coarseLevel middleLevel fineLevel coarseMiddle middleFine]
  exact xiUnitEnergyProjection_boundary system rulesConnected middleLevel fineLevel middleFine values _

theorem xiUnitEnergyProjection_increment_zero (coarseLevel middleLevel fineLevel : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (middleFine : middleLevel ≤ fineLevel)
    (values : XiVtx system fineLevel → ℝ) (vertex : XiVtx system coarseLevel) :
    (xiUnitEnergyProjection system rulesConnected middleLevel fineLevel middleFine values -
      xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values)
        (xiVertexInclusion system coarseLevel fineLevel (coarseMiddle.trans middleFine) vertex) = 0 := by
  simp only [Pi.sub_apply]
  rw [xiUnitEnergyProjection_boundary]
  rw [← xiVertexInclusion_comp system coarseLevel middleLevel fineLevel coarseMiddle middleFine,
    xiUnitEnergyProjection_boundary]
  exact sub_self _

theorem xiUnitEnergyProjection_finer_fixed (coarseLevel middleLevel fineLevel : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (middleFine : middleLevel ≤ fineLevel)
    (values : XiVtx system fineLevel → ℝ) :
    xiUnitEnergyProjection system rulesConnected middleLevel fineLevel middleFine
      (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values) =
    xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values := by
  classical
  apply (XiNetwork system fineLevel).potential_minimum_unique (fun _ => 1) (fun _ => by norm_num)
    (xiSimpleGraph_connected system rulesConnected fineLevel)
    (Finset.univ.image (xiVertexInclusion system middleLevel fineLevel middleFine))
    ⟨xiVertexInclusion system middleLevel fineLevel middleFine (xiPositiveTerminal system middleLevel), by simp⟩
    (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values)
  · intro vertex membership
    obtain ⟨middleVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiUnitEnergyProjection_boundary system rulesConnected middleLevel fineLevel middleFine _ middleVertex
  · intro vertex membership
    rfl
  · intro competitor competitorBoundary
    exact xiUnitEnergyProjection_minimal system rulesConnected middleLevel fineLevel middleFine _ competitor
      (fun vertex => competitorBoundary _ (by simp))
  · intro competitor competitorBoundary
    apply xiUnitEnergyProjection_minimal system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values competitor
    intro vertex
    rw [← xiVertexInclusion_comp system coarseLevel middleLevel fineLevel coarseMiddle middleFine]
    rw [competitorBoundary _ (by simp), xiVertexInclusion_comp, xiUnitEnergyProjection_boundary]

theorem xiUnitEnergyProjection_increment_energy_le (coarseLevel middleLevel fineLevel : ℕ)
    (coarseMiddle : coarseLevel ≤ middleLevel) (middleFine : middleLevel ≤ fineLevel)
    (values : XiVtx system fineLevel → ℝ) :
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
      (xiUnitEnergyProjection system rulesConnected middleLevel fineLevel middleFine values -
        xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values) ≤
    ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values := by
  have decomposition := xiUnitEnergyProjection_energy_identity system rulesConnected coarseLevel fineLevel
    (coarseMiddle.trans middleFine) (xiUnitEnergyProjection system rulesConnected middleLevel fineLevel middleFine values)
  rw [xiUnitEnergyProjection_nested system rulesConnected coarseLevel middleLevel fineLevel coarseMiddle middleFine values] at decomposition
  have energyNonnegative := ((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy_nonneg
    (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel (coarseMiddle.trans middleFine) values)
  have projectionBound := xiUnitEnergyProjection_minimal system rulesConnected middleLevel fineLevel middleFine values values (fun _ => rfl)
  linarith

end

end EIGS
