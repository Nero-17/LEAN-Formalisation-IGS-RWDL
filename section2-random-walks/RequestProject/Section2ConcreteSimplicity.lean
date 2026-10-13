import RequestProject.Section2Concrete
import RequestProject.Section2Simplicity

/-!
This file encodes the paper's underlying simple-graph convention by explicit
looplessness and uniqueness of unordered endpoints. These conditions are not
inferred from the larger legacy directed-multigraph data type.
-/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiNetwork_loopless (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless) (level : ℕ) :
    (XiNetwork system level).Loopless := by
  induction level with
  | zero => intro edge; exact Bool.false_ne_true
  | succ level induction =>
      rw [xiNetwork_succ system rule_connected level]
      exact Network.subst_loopless _ _ induction rules_loopless

theorem xiNetwork_edges_unique (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    (XiNetwork system level).EdgesUnique := by
  cases level with
  | zero => intro first second _; cases first; cases second; rfl
  | succ level =>
      rw [xiNetwork_succ system rule_connected level]
      exact Network.subst_edges_unique _ _
        (xiNetwork_loopless system rule_connected rules_loopless level) rules_unique
        (fun colour => Network.rule_edge_has_interior_endpoint (system.ruleFamily rule_connected) colour
          (rules_loopless colour) (planting_nonadjacent colour))

/-- The mass in the electrical model equals the mass used by the simple walk
on the actual Xi graph, under the stated underlying simple-graph convention. -/
theorem xiNetwork_card_edges_eq_simpleGraph (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    Fintype.card (XiNetwork system level).E = (XiSimpleGraph system level).edgeFinset.card := by
  exact Network.card_edges_eq_simpleGraph _
    (xiNetwork_loopless system rule_connected rules_loopless level)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique
      planting_nonadjacent level)

end EIGS
