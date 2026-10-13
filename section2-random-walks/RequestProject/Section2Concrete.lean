import RequestProject.Section1Connected
import RequestProject.Section2FlowConnectivity
import RequestProject.Section2Substitution
import RequestProject.Section2Perron
import RequestProject.Section2PerronConvergence

namespace EIGS



variable {K : ℕ}

/-- A rule graph with its unchanged oriented coloured edges as an electrical network. -/
def EIGSData.ruleNetwork (system : EIGSData K) (colour : Fin K) : Network K where
  V := (system.rule colour).V
  E := (system.rule colour).E
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := (system.rule colour).tail
  head := (system.rule colour).head
  color := (system.rule colour).col

@[simp] theorem EIGSData.ruleNetwork_toSimpleGraph (system : EIGSData K)
    (colour : Fin K) :
    (system.ruleNetwork colour).toSimpleGraph = ruleSG system colour := rfl

/-- The rule family is obtained from connected original rule graphs, with no
electrical connectivity hypothesis supplied separately. -/
noncomputable def EIGSData.ruleFamily (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) : RuleFamily K where
  R := system.ruleNetwork
  βplus := system.plantPlus
  βminus := system.plantMinus
  plant_ne := system.plant_ne
  connected := fun colour => (system.ruleNetwork colour).flow_nonempty_of_connected
    (rule_connected colour) _ _ (system.plant_ne colour)

noncomputable def EIGSData.connectedRuleSystem (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) : RuleSystem K where
  R := system.ruleNetwork
  βplus := system.plantPlus
  βminus := system.plantMinus
  connected := fun colour => (system.ruleNetwork colour).flow_nonempty_of_connected
    (rule_connected colour) _ _ (system.plant_ne colour)

@[simp] theorem EIGSData.ruleFamily_Psi (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) :
    (system.ruleFamily rule_connected).Psi =
      (system.connectedRuleSystem rule_connected).toRenormMap.apply := rfl

@[simp] theorem xiNetwork_zero (system : EIGSData K) :
    XiNetwork system 0 = Network.singleEdge system.initCol := rfl

/-- One substitution in the graph construction is exactly one substitution of
the corresponding finite electrical network. -/
theorem xiNetwork_succ (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    XiNetwork system (level + 1) =
      (XiNetwork system level).subst (system.ruleFamily rule_connected) := by
  unfold XiNetwork Network.subst
  congr
  exact Subsingleton.elim _ _

theorem xiNetwork_succ_div (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    (current : (XiNetwork system (level + 1)).E → ℝ)
    (vertex : XiVtx system (level + 1)) :
    (XiNetwork system (level + 1)).div current vertex =
      ((XiNetwork system level).subst (system.ruleFamily rule_connected)).div current vertex := by
  unfold Network.div
  congr <;> funext edge
  · have tails_equal : (XiNetwork system (level + 1)).tail edge =
        ((XiNetwork system level).subst (system.ruleFamily rule_connected)).tail edge := rfl
    simp only [tails_equal]
  · have heads_equal : (XiNetwork system (level + 1)).head edge =
        ((XiNetwork system level).subst (system.ruleFamily rule_connected)).head edge := rfl
    simp only [heads_equal]

theorem xiNetwork_succ_unitFlow_iff (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    (source sink : XiVtx system (level + 1))
    (current : (XiNetwork system (level + 1)).E → ℝ) :
    (XiNetwork system (level + 1)).IsUnitFlow source sink current ↔
      ((XiNetwork system level).subst (system.ruleFamily rule_connected)).IsUnitFlow
        source sink current := by
  constructor
  all_goals
    intro unit_flow vertex
    have divergence := unit_flow vertex
    rw [xiNetwork_succ_div system rule_connected level] at *
    convert divergence using 1 <;> split_ifs <;> rfl

/-- The positive endpoint of the original edge, tracked through vertex nesting. -/
def xiPositiveTerminal (system : EIGSData K) : (level : ℕ) → XiVtx system level
  | 0 => false
  | level + 1 => Sum.inl (xiPositiveTerminal system level)

/-- The negative endpoint of the original edge, tracked through vertex nesting. -/
def xiNegativeTerminal (system : EIGSData K) : (level : ℕ) → XiVtx system level
  | 0 => true
  | level + 1 => Sum.inl (xiNegativeTerminal system level)

theorem xiNetwork_terminal_flow (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    Nonempty ((XiNetwork system level).Flow (xiPositiveTerminal system level)
      (xiNegativeTerminal system level)) := by
  induction level with
  | zero => exact Network.singleEdge_connected system.initCol
  | succ level induction =>
      obtain ⟨current, current_divergence⟩ :=
        (XiNetwork system level).subst_connected (system.ruleFamily rule_connected)
          (xiPositiveTerminal system level) (xiNegativeTerminal system level) induction
      exact ⟨current, (xiNetwork_succ_unitFlow_iff system rule_connected level
        (xiPositiveTerminal system (level + 1)) (xiNegativeTerminal system (level + 1))
        current).mpr current_divergence⟩

/-- Lemma 2.4 on precisely the concrete graph `XiNetwork`, for arbitrary
nonnegative coloured edge resistances. -/
theorem xiNetwork_terminal_effRes (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistances_nonneg : 0 ≤ resistances) (level : ℕ) :
    (XiNetwork system level).effRes (xiPositiveTerminal system level)
      (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
      resistances = ((system.ruleFamily rule_connected).Psi^[level] resistances) system.initCol := by
  induction level generalizing resistances with
  | zero => exact Network.singleEdge_effRes system.initCol resistances
  | succ level induction =>
      have substitution := (XiNetwork system level).subst_effRes
        (system.ruleFamily rule_connected) (xiPositiveTerminal system level)
        (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
        resistances_nonneg
      have nonnegative := Network.Psi_nonneg (system.ruleFamily rule_connected)
        resistances_nonneg
      rw [Function.iterate_succ_apply]
      rw [← induction _ nonnegative]
      convert substitution using 1
      rw [Network.effRes_eq_iInf, Network.effRes_eq_iInf]
      exact (Equiv.subtypeEquivRight
        (xiNetwork_succ_unitFlow_iff system rule_connected level
          (xiPositiveTerminal system (level + 1))
          (xiNegativeTerminal system (level + 1)))).iInf_congr (fun _ => rfl)

/-- The geometric resistance bound is now on the actual substitution graph,
and its positive rate is constructed from the original distance-positive rules. -/
theorem xiNetwork_terminal_resistance_growth (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate lower upper : ℝ, 0 < rate ∧ 0 < lower ∧ 0 < upper ∧ ∀ level : ℕ,
      lower * rate ^ level ≤ (XiNetwork system level).effRes
        (xiPositiveTerminal system level) (xiNegativeTerminal system level)
        (xiNetwork_terminal_flow system rule_connected level) (fun _ => 1) ∧
      (XiNetwork system level).effRes (xiPositiveTerminal system level)
        (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
        (fun _ => 1) ≤ upper * rate ^ level := by
  have colours_positive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val)
    system.initCol.isLt
  obtain ⟨rate, lower, upper, rate_positive, lower_positive, upper_positive, growth⟩ :=
    (system.connectedRuleSystem rule_connected).distance_positive_iterate_growth
      colours_positive distance_positive
  refine ⟨rate, lower, upper, rate_positive, lower_positive, upper_positive, fun level => ?_⟩
  rw [xiNetwork_terminal_effRes system rule_connected (fun _ => 1)
    (fun _ => zero_le_one) level]
  simpa only [EIGSData.ruleFamily_Psi] using growth level system.initCol

/-- Normalized terminal resistance of the actual iterated graph converges to a
strictly positive limit; the eigenpair and convergence are constructed. -/
theorem xiNetwork_terminal_resistance_normalized_limit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate limit : ℝ, 0 < rate ∧ 0 < limit ∧
      Filter.Tendsto (fun level =>
        (XiNetwork system level).effRes (xiPositiveTerminal system level)
          (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
          (fun _ => 1) / rate ^ level) Filter.atTop (nhds limit) := by
  have colours_positive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val)
    system.initCol.isLt
  obtain ⟨rate, limit, vector, rate_positive, limit_positive, vector_positive,
    normalized, eigenpair, convergence⟩ :=
    (system.connectedRuleSystem rule_connected).distance_positive_normalized_iterate_limit
      colours_positive distance_positive
  refine ⟨rate, limit * vector system.initCol, rate_positive,
    mul_pos limit_positive (vector_positive system.initCol), ?_⟩
  have coordinate_limit := (tendsto_pi_nhds.mp convergence) system.initCol
  convert coordinate_limit using 1
  ext level
  rw [xiNetwork_terminal_effRes system rule_connected (fun _ => 1)
    (fun _ => zero_le_one) level]
  rfl

end EIGS

