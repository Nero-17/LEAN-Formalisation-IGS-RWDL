import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section2ConcreteSpectralRadius

/-! Actual colour cuts and shortest-path renormalization of Figure 3.
Explicit Lipschitz potentials and two-edge paths show that both actual
weighted terminal distances equal the sum of the two positive lengths.
The canonical minimum path-selection spectral radius is consequently 2.
Candidate source. -/

namespace EIGS
noncomputable section

theorem not_reachable_of_preserved_bool_label {Vertex : Type*} (graph : SimpleGraph Vertex)
    (label : Vertex → Bool) (source sink : Vertex) (different : label source ≠ label sink)
    (preserved : ∀ first second, graph.Adj first second → label first = label second) :
    ¬ graph.Reachable source sink := by
  have alongWalk {first second : Vertex} (walk : graph.Walk first second) : label first = label second := by
    induction walk with
    | nil => rfl
    | cons adjacent rest induction => exact (preserved _ _ adjacent).trans induction
  rintro ⟨walk⟩
  exact different (alongWalk walk)

theorem twoColourSystem_distancePositive (ruleColour edgeColour : Fin 2) :
    ¬ ((twoColourSystem.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      (twoColourSystem.plantPlus ruleColour) (twoColourSystem.plantMinus ruleColour) := by
  fin_cases ruleColour <;> fin_cases edgeColour
  · apply not_reachable_of_preserved_bool_label _ ![false, true, false, false, true] 0 4 (by decide)
    intro first second
    fin_cases first <;> fin_cases second <;>
      dsimp [Network.withoutColour, SimpleGraph.fromRel, EIGSData.ruleNetwork,
        twoColourSystem, twoColourRule, twoColourRedRule, twoColourBlueRule] <;> decide
  · apply not_reachable_of_preserved_bool_label _ ![false, false, false, true, true] 0 4 (by decide)
    intro first second
    fin_cases first <;> fin_cases second <;>
      dsimp [Network.withoutColour, SimpleGraph.fromRel, EIGSData.ruleNetwork,
        twoColourSystem, twoColourRule, twoColourRedRule, twoColourBlueRule] <;> decide
  · apply not_reachable_of_preserved_bool_label _ ![false, false, true, false, true] 0 4 (by decide)
    intro first second
    fin_cases first <;> fin_cases second <;>
      dsimp [Network.withoutColour, SimpleGraph.fromRel, EIGSData.ruleNetwork,
        twoColourSystem, twoColourRule, twoColourRedRule, twoColourBlueRule] <;> decide
  · apply not_reachable_of_preserved_bool_label _ ![false, false, false, true, true] 0 4 (by decide)
    intro first second
    fin_cases first <;> fin_cases second <;>
      dsimp [Network.withoutColour, SimpleGraph.fromRel, EIGSData.ruleNetwork,
        twoColourSystem, twoColourRule, twoColourRedRule, twoColourBlueRule] <;> decide

def twoColourRedMetricPotential (lengths : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![lengths 0 + lengths 1, lengths 1, lengths 0 + lengths 1, lengths 0, 0]

def twoColourBlueMetricPotential (lengths : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![lengths 0 + lengths 1, lengths 0, 0, lengths 0, 0]

theorem twoColourRedMetricPotential_lipschitz (lengths : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < lengths colour) :
    (twoColourSystem.ruleNetwork 0).EdgeLipschitz lengths (twoColourRedMetricPotential lengths) := by
  intro edge
  fin_cases edge <;>
    norm_num [twoColourSystem, twoColourRule, EIGSData.ruleNetwork, twoColourRedRule,
      twoColourRedMetricPotential] <;>
    ring_nf <;>
    simp [abs_neg, abs_of_pos (positive 0), abs_of_pos (positive 1), (positive 0).le, (positive 1).le]

theorem twoColourBlueMetricPotential_lipschitz (lengths : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < lengths colour) :
    (twoColourSystem.ruleNetwork 1).EdgeLipschitz lengths (twoColourBlueMetricPotential lengths) := by
  intro edge
  fin_cases edge <;>
    norm_num [twoColourSystem, twoColourRule, EIGSData.ruleNetwork, twoColourBlueRule,
      twoColourBlueMetricPotential] <;>
    ring_nf <;>
    simp [abs_neg, abs_of_pos (positive 0), abs_of_pos (positive 1), (positive 0).le, (positive 1).le]

def twoColourRedShortPath : (twoColourSystem.ruleNetwork 0).EdgeWalk 0 4 :=
  .cons 0 (Or.inl ⟨rfl, rfl⟩) (.cons 1 (Or.inl ⟨rfl, rfl⟩) (.nil 4))

def twoColourBlueShortPath : (twoColourSystem.ruleNetwork 1).EdgeWalk 0 4 :=
  .cons 3 (Or.inl ⟨rfl, rfl⟩) (.cons 4 (Or.inl ⟨rfl, rfl⟩) (.nil 4))

theorem twoColourSystem_metricLengths (lengths : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < lengths colour) :
    (twoColourSystem.ruleFamily twoColourSystem_connected).metricLengths lengths =
      fun _ => lengths 0 + lengths 1 := by
  ext colour
  fin_cases colour
  · change (twoColourSystem.ruleNetwork 0).weightedDistance lengths 0 4 = lengths 0 + lengths 1
    apply le_antisymm
    · have upper := (twoColourSystem.ruleNetwork 0).weightedDistance_le_cost
        (fun colour => (positive colour).le) twoColourRedShortPath
      simpa [twoColourRedShortPath, Network.EdgeWalk.cost, twoColourSystem, twoColourRule,
        EIGSData.ruleNetwork, twoColourRedRule] using upper
    · have lower := (twoColourSystem.ruleNetwork 0).potential_difference_le_weightedDistance
        (twoColourSystem_connected 0) (twoColourRedMetricPotential_lipschitz lengths positive) 0 4
      simpa [twoColourRedMetricPotential, abs_of_pos (add_pos (positive 0) (positive 1))] using lower
  · change (twoColourSystem.ruleNetwork 1).weightedDistance lengths 0 4 = lengths 0 + lengths 1
    apply le_antisymm
    · have upper := (twoColourSystem.ruleNetwork 1).weightedDistance_le_cost
        (fun colour => (positive colour).le) twoColourBlueShortPath
      simpa [twoColourBlueShortPath, Network.EdgeWalk.cost, twoColourSystem, twoColourRule,
        EIGSData.ruleNetwork, twoColourBlueRule, add_comm] using upper
    · have lower := (twoColourSystem.ruleNetwork 1).potential_difference_le_weightedDistance
        (twoColourSystem_connected 1) (twoColourBlueMetricPotential_lipschitz lengths positive) 0 4
      simpa [twoColourBlueMetricPotential, abs_of_pos (add_pos (positive 0) (positive 1))] using lower

theorem twoColourSystem_distanceSpectralRadius :
    twoColourSystem.distanceSpectralRadius twoColourSystem_connected = 2 := by
  obtain ⟨lengths, positive, ratePositive, normalized, eigenpair⟩ :=
    twoColourSystem.metricLengths_spectral_eigenpair twoColourSystem_connected twoColourSystem_loopless
      twoColourSystem_edgesUnique twoColourSystem_distancePositive
  rw [twoColourSystem_metricLengths lengths positive] at eigenpair
  have first := congrFun eigenpair 0
  have second := congrFun eigenpair 1
  norm_num [Fin.sum_univ_succ] at normalized
  simp only [Pi.smul_apply, smul_eq_mul] at first second
  nlinarith

end
end EIGS

#print axioms EIGS.twoColourSystem_distancePositive
#print axioms EIGS.twoColourSystem_metricLengths
#print axioms EIGS.twoColourSystem_distanceSpectralRadius
