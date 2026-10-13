import RequestProject.Section31.WatchedChain
import RequestProject.Section31.EIGSDiscreteTrace
import RequestProject.Section2ResistanceSpectralRadius

/-! A uniform terminal-hitting jump bound on the fixed actual rule carriers.
The graph descent is constructed from connectivity. The actual nonlinear
resistance scale cancels in transition ratios, including when that scale is
less than one. This file asserts no global ambient-cell jump bound. -/

namespace IGS.Sec31

open scoped BigOperators Classical
noncomputable section

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem connected_distance_descent (graph : SimpleGraph Vertex)
    (connected : graph.Connected) (source terminal : Vertex) (different : source ≠ terminal) :
    ∃ target, graph.Adj source target ∧ graph.dist target terminal < graph.dist source terminal := by
  obtain ⟨walk, length⟩ := connected.exists_walk_length_eq_dist source terminal
  have nonempty : ¬ walk.Nil := SimpleGraph.Walk.not_nil_of_ne different
  refine ⟨walk.snd, SimpleGraph.Walk.adj_snd nonempty, ?_⟩
  have tailBound := SimpleGraph.dist_le walk.tail
  have tailLength := SimpleGraph.Walk.length_tail_add_one nonempty
  omega

def graphConductanceJumpBound (graph : SimpleGraph Vertex) (terminal : Vertex)
    (lower upper : ℝ) : ℝ :=
  let depth := (Finset.univ.sup (fun vertex => graph.dist vertex terminal)) + 1
  (depth : ℝ) / (lower / ((Fintype.card Vertex : ℝ) * upper)) ^ depth

theorem graphConductanceJumpBound_positive (graph : SimpleGraph Vertex) (terminal : Vertex)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper) :
    0 < graphConductanceJumpBound graph terminal lower upper := by
  haveI : Nonempty Vertex := ⟨terminal⟩
  have cardPositive : (0 : ℝ) < Fintype.card Vertex := by
    exact_mod_cast Fintype.card_pos
  unfold graphConductanceJumpBound
  positivity

theorem connected_conductance_partialHit_le [Nontrivial Vertex]
    (graph : SimpleGraph Vertex) (connected : graph.Connected)
    (conductance : Vertex → Vertex → ℝ)
    (nonnegative : ∀ source target, 0 ≤ conductance source target)
    (rowPositive : ∀ source, 0 < ∑ target, conductance source target)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (edgeLower : ∀ source target, graph.Adj source target → lower ≤ conductance source target)
    (allUpper : ∀ source target, conductance source target ≤ upper)
    (terminal : Vertex) (boundary : Finset Vertex) (terminalInside : terminal ∈ boundary)
    (time : ℕ) (source : Vertex) :
    partialHit (condChain conductance nonnegative rowPositive) boundary time source ≤
      graphConductanceJumpBound graph terminal lower upper := by
  have lowerUpper : lower ≤ upper := by
    obtain ⟨target, adjacent⟩ := connected.preconnected.exists_adj_of_nontrivial terminal
    exact (edgeLower terminal target adjacent).trans (allUpper terminal target)
  apply condChain_partialHit_le conductance nonnegative rowPositive boundary
    lowerPositive upperPositive lowerUpper allUpper (fun vertex => graph.dist vertex terminal)
    (by omega : 1 ≤ Finset.univ.sup (fun vertex => graph.dist vertex terminal) + 1)
  · intro vertex
    exact (Finset.le_sup (f := fun vertex => graph.dist vertex terminal)
      (Finset.mem_univ vertex)).trans (Nat.le_succ _)
  · intro vertex outside
    have different : vertex ≠ terminal := by
      intro equality
      exact outside (equality.symm ▸ terminalInside)
    obtain ⟨target, adjacent, smaller⟩ :=
      connected_distance_descent graph connected vertex terminal different
    exact ⟨target, edgeLower vertex target adjacent, smaller⟩

theorem condChain_scale (conductance : Vertex → Vertex → ℝ)
    (nonnegative : ∀ source target, 0 ≤ conductance source target)
    (rowPositive : ∀ source, 0 < ∑ target, conductance source target)
    (scale : ℝ) (scalePositive : 0 < scale) :
    condChain (fun source target => scale * conductance source target)
      (fun source target => mul_nonneg scalePositive.le (nonnegative source target))
      (fun source => by rw [← Finset.mul_sum]; exact mul_pos scalePositive (rowPositive source)) =
      condChain conductance nonnegative rowPositive := by
  apply FinChain.ext
  funext source target
  change (scale * conductance source target) / (∑ other, scale * conductance source other) =
    conductance source target / ∑ other, conductance source other
  rw [← Finset.mul_sum]
  field_simp [scalePositive.ne', (rowPositive source).ne']

end
end IGS.Sec31

namespace EIGS

open IGS.Sec31
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)

def xiRuleEffectiveConductance (colour : Fin K) (steps : ℕ)
    (source target : (system.ruleNetwork colour).V) : ℝ :=
  ∑ edge : (system.ruleNetwork colour).E,
    if ((system.ruleNetwork colour).tail edge = source ∧ (system.ruleNetwork colour).head edge = target) ∨
        ((system.ruleNetwork colour).tail edge = target ∧ (system.ruleNetwork colour).head edge = source) then
      (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
        ((system.ruleNetwork colour).color edge))⁻¹ else 0

theorem xiRuleEffectiveConductance_nonnegative (colour : Fin K) (steps : ℕ)
    (source target : (system.ruleNetwork colour).V) :
    0 ≤ xiRuleEffectiveConductance system rulesConnected colour steps source target := by
  unfold xiRuleEffectiveConductance
  apply Finset.sum_nonneg
  intro edge _
  split
  · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rulesConnected
      (fun _ => 1) (fun _ => by norm_num) steps _)).le
  · exact le_rfl

theorem xiRuleEffectiveConductance_row_positive (colour : Fin K) (steps : ℕ)
    (source : (system.ruleNetwork colour).V) :
    0 < ∑ target, xiRuleEffectiveConductance system rulesConnected colour steps source target := by
  letI : Nontrivial (system.rule colour).V :=
    ⟨⟨system.plantPlus colour, system.plantMinus colour, system.plant_ne colour⟩⟩
  obtain ⟨target, adjacent⟩ := (rulesConnected colour).preconnected.exists_adj_of_nontrivial source
  change (system.ruleNetwork colour).toSimpleGraph.Adj source target at adjacent
  obtain ⟨edge, endpoints⟩ : ∃ edge : (system.ruleNetwork colour).E,
      ((system.ruleNetwork colour).tail edge = source ∧ (system.ruleNetwork colour).head edge = target) ∨
        ((system.ruleNetwork colour).tail edge = target ∧ (system.ruleNetwork colour).head edge = source) := by
    rcases adjacent.2 with ⟨edge, first, second⟩ | ⟨edge, first, second⟩
    · exact ⟨edge, Or.inl ⟨first, second⟩⟩
    · exact ⟨edge, Or.inr ⟨first, second⟩⟩
  have termPositive : 0 < (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
      ((system.ruleNetwork colour).color edge))⁻¹ :=
    inv_pos.mpr (ruleFamily_Psi_iterate_positive system rulesConnected
      (fun _ => 1) (fun _ => by norm_num) steps _)
  have entryPositive : 0 < xiRuleEffectiveConductance system rulesConnected colour steps source target := by
    apply termPositive.trans_le
    unfold xiRuleEffectiveConductance
    have termBound := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : (system.ruleNetwork colour).E =>
        if ((system.ruleNetwork colour).tail candidate = source ∧ (system.ruleNetwork colour).head candidate = target) ∨
            ((system.ruleNetwork colour).tail candidate = target ∧ (system.ruleNetwork colour).head candidate = source) then
          (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
            ((system.ruleNetwork colour).color candidate))⁻¹ else 0)
      (fun candidate _ => by
        dsimp only
        split
        · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rulesConnected
            (fun _ => 1) (fun _ => by norm_num) steps _)).le
        · exact le_rfl)
      (Finset.mem_univ edge)
    simpa only [if_pos endpoints] using termBound
  exact entryPositive.trans_le (Finset.single_le_sum
    (fun target _ => xiRuleEffectiveConductance_nonnegative system rulesConnected colour steps source target)
    (Finset.mem_univ target))

def xiRuleConductanceChain (colour : Fin K) (steps : ℕ) : FinChain (system.ruleNetwork colour).V :=
  condChain (xiRuleEffectiveConductance system rulesConnected colour steps)
    (xiRuleEffectiveConductance_nonnegative system rulesConnected colour steps)
    (xiRuleEffectiveConductance_row_positive system rulesConnected colour steps)

variable (distancePositive : ∀ ruleColour edgeColour : Fin K,
    ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include distancePositive

theorem xiRuleConductanceChain_uniform_terminal_jumps :
    ∃ jumpBound : ℝ, 0 < jumpBound ∧ ∀ colour steps time (source : (system.ruleNetwork colour).V),
      partialHit (xiRuleConductanceChain system rulesConnected colour steps)
        {system.plantPlus colour, system.plantMinus colour} time source ≤ jumpBound := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, resistanceBounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds rulesConnected distancePositive
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  have normalizedEdgeBounds (steps : ℕ) (edgeColour : Fin K) :
      1 / upper ≤ (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
        (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹ ∧
      (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
        (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹ ≤ 1 / lower := by
    have resistancePositive := ruleFamily_Psi_iterate_positive system rulesConnected
      (fun _ => 1) (fun _ => by norm_num) steps edgeColour
    constructor
    · rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ upperPositive resistancePositive).2
      nlinarith [(resistanceBounds steps edgeColour).2]
    · rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ resistancePositive lowerPositive).2
      nlinarith [(resistanceBounds steps edgeColour).1]
  let normalizedConductance (colour : Fin K) (steps : ℕ)
      (source target : (system.ruleNetwork colour).V) :=
    (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
      xiRuleEffectiveConductance system rulesConnected colour steps source target
  have normalizedNonnegative (colour : Fin K) (steps : ℕ) :
      ∀ source target, 0 ≤ normalizedConductance colour steps source target :=
    fun source target => mul_nonneg (pow_pos ratePositive steps).le
      (xiRuleEffectiveConductance_nonnegative system rulesConnected colour steps source target)
  have normalizedRowPositive (colour : Fin K) (steps : ℕ) :
      ∀ source, 0 < ∑ target, normalizedConductance colour steps source target := by
    intro source
    dsimp only [normalizedConductance]
    rw [← Finset.mul_sum]
    exact mul_pos (pow_pos ratePositive steps)
      (xiRuleEffectiveConductance_row_positive system rulesConnected colour steps source)
  have normalizedUpper (colour : Fin K) (steps : ℕ) (source target : (system.ruleNetwork colour).V) :
      normalizedConductance colour steps source target ≤
        ((Fintype.card (system.ruleNetwork colour).E : ℝ) + 1) / lower := by
    unfold normalizedConductance xiRuleEffectiveConductance
    rw [Finset.mul_sum]
    have bound :
        (∑ edge : (system.ruleNetwork colour).E,
          (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
            (if ((system.ruleNetwork colour).tail edge = source ∧ (system.ruleNetwork colour).head edge = target) ∨
                ((system.ruleNetwork colour).tail edge = target ∧ (system.ruleNetwork colour).head edge = source) then
              (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
                ((system.ruleNetwork colour).color edge))⁻¹ else 0)) ≤
        ∑ _edge : (system.ruleNetwork colour).E, 1 / lower := by
      apply Finset.sum_le_sum
      intro edge _
      split
      · exact (normalizedEdgeBounds steps _).2
      · simp only [mul_zero]
        positivity
    have sumBound :
        (∑ _edge : (system.ruleNetwork colour).E, 1 / lower) ≤
          ((Fintype.card (system.ruleNetwork colour).E : ℝ) + 1) / lower := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
      nlinarith [inv_pos.mpr lowerPositive]
    exact bound.trans sumBound
  have normalizedLower (colour : Fin K) (steps : ℕ)
      (source target : (system.ruleNetwork colour).V) (adjacent : (ruleSG system colour).Adj source target) :
      1 / upper ≤ normalizedConductance colour steps source target := by
    change (system.ruleNetwork colour).toSimpleGraph.Adj source target at adjacent
    obtain ⟨edge, endpoints⟩ : ∃ edge : (system.ruleNetwork colour).E,
        ((system.ruleNetwork colour).tail edge = source ∧ (system.ruleNetwork colour).head edge = target) ∨
          ((system.ruleNetwork colour).tail edge = target ∧ (system.ruleNetwork colour).head edge = source) := by
      rcases adjacent.2 with ⟨edge, first, second⟩ | ⟨edge, first, second⟩
      · exact ⟨edge, Or.inl ⟨first, second⟩⟩
      · exact ⟨edge, Or.inr ⟨first, second⟩⟩
    apply (normalizedEdgeBounds steps ((system.ruleNetwork colour).color edge)).1.trans
    unfold normalizedConductance xiRuleEffectiveConductance
    rw [Finset.mul_sum]
    have termBound := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : (system.ruleNetwork colour).E =>
        (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
          (if ((system.ruleNetwork colour).tail candidate = source ∧ (system.ruleNetwork colour).head candidate = target) ∨
              ((system.ruleNetwork colour).tail candidate = target ∧ (system.ruleNetwork colour).head candidate = source) then
            (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
              ((system.ruleNetwork colour).color candidate))⁻¹ else 0))
      (fun candidate _ => by
        apply mul_nonneg (pow_pos ratePositive steps).le
        split
        · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rulesConnected
            (fun _ => 1) (fun _ => by norm_num) steps _)).le
        · exact le_rfl)
      (Finset.mem_univ edge)
    simpa only [if_pos endpoints] using termBound
  have boundPositive (colour : Fin K) :
      0 < graphConductanceJumpBound (ruleSG system colour) (system.plantPlus colour)
        (1 / upper) (((Fintype.card (system.ruleNetwork colour).E : ℝ) + 1) / lower) :=
    graphConductanceJumpBound_positive _ _ _ _ (one_div_pos.mpr upperPositive) (by positivity)
  haveI : Nonempty (Fin K) := ⟨system.initCol⟩
  refine ⟨∑ colour : Fin K,
    graphConductanceJumpBound (ruleSG system colour) (system.plantPlus colour)
      (1 / upper) (((Fintype.card (system.ruleNetwork colour).E : ℝ) + 1) / lower),
    Finset.sum_pos (fun colour _ => boundPositive colour) Finset.univ_nonempty, ?_⟩
  intro colour steps time source
  letI : Nontrivial (system.rule colour).V :=
    ⟨⟨system.plantPlus colour, system.plantMinus colour, system.plant_ne colour⟩⟩
  have scaleIdentity := condChain_scale (xiRuleEffectiveConductance system rulesConnected colour steps)
    (xiRuleEffectiveConductance_nonnegative system rulesConnected colour steps)
    (xiRuleEffectiveConductance_row_positive system rulesConnected colour steps)
    ((system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps) (pow_pos ratePositive steps)
  have localBound := connected_conductance_partialHit_le (ruleSG system colour) (rulesConnected colour)
    (normalizedConductance colour steps) (normalizedNonnegative colour steps) (normalizedRowPositive colour steps)
    (1 / upper) (((Fintype.card (system.ruleNetwork colour).E : ℝ) + 1) / lower)
    (one_div_pos.mpr upperPositive) (by positivity) (normalizedLower colour steps) (normalizedUpper colour steps)
    (system.plantPlus colour) {system.plantPlus colour, system.plantMinus colour}
    (by simp) time source
  rw [scaleIdentity] at localBound
  exact localBound.trans (Finset.single_le_sum (fun other _ => (boundPositive other).le)
    (Finset.mem_univ colour))

end
end EIGS

#print axioms IGS.Sec31.connected_distance_descent
#print axioms IGS.Sec31.graphConductanceJumpBound_positive
#print axioms IGS.Sec31.connected_conductance_partialHit_le
#print axioms IGS.Sec31.condChain_scale
#print axioms EIGS.xiRuleEffectiveConductance_nonnegative
#print axioms EIGS.xiRuleEffectiveConductance_row_positive
#print axioms EIGS.xiRuleConductanceChain_uniform_terminal_jumps
