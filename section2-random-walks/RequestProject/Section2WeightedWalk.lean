import RequestProject.Section2Simplicity
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Edge-labelled walks in the actual finite network and exact substitution
lifts. Edge identities are retained, so the construction also detects repeated
or antiparallel edges in the larger network type. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K)

inductive EdgeWalk : network.V → network.V → Type
  | nil (vertex : network.V) : EdgeWalk vertex vertex
  | cons {source next sink : network.V} (edge : network.E)
      (joins : (network.tail edge = source ∧ network.head edge = next) ∨
        (network.tail edge = next ∧ network.head edge = source))
      (rest : EdgeWalk next sink) : EdgeWalk source sink

namespace EdgeWalk

variable {network}

def cost (lengths : Fin K → ℝ) {source sink : network.V} :
    network.EdgeWalk source sink → ℝ
  | nil _ => 0
  | cons edge _ rest => lengths (network.color edge) + rest.cost lengths

def edges {source sink : network.V} : network.EdgeWalk source sink → List network.E
  | nil _ => []
  | cons edge _ rest => edge :: rest.edges

def append {source middle sink : network.V}
    (first : network.EdgeWalk source middle) (second : network.EdgeWalk middle sink) :
    network.EdgeWalk source sink :=
  match first with
  | nil _ => second
  | cons edge joins rest => cons edge joins (rest.append second)

@[simp] theorem cost_append (lengths : Fin K → ℝ) {source middle sink : network.V}
    (first : network.EdgeWalk source middle) (second : network.EdgeWalk middle sink) :
    (first.append second).cost lengths = first.cost lengths + second.cost lengths := by
  induction first with
  | nil => simp [append, cost]
  | cons edge joins rest induction_hypothesis =>
    simp [append, cost, induction_hypothesis, add_assoc]

def copy {source sink first last : network.V} (walk : network.EdgeWalk source sink)
    (source_eq : source = first) (sink_eq : sink = last) : network.EdgeWalk first last :=
  source_eq ▸ sink_eq ▸ walk

@[simp] theorem cost_copy (lengths : Fin K → ℝ)
    {source sink first last : network.V} (walk : network.EdgeWalk source sink)
    (source_eq : source = first) (sink_eq : sink = last) :
    (walk.copy source_eq sink_eq).cost lengths = walk.cost lengths := by
  cases source_eq
  cases sink_eq
  rfl

def reverse {source sink : network.V} (walk : network.EdgeWalk source sink) :
    network.EdgeWalk sink source :=
  match walk with
  | nil vertex => nil vertex
  | cons edge joins rest => rest.reverse.append
      (cons edge (joins.elim (fun pair => Or.inr pair) (fun pair => Or.inl pair)) (nil _))

@[simp] theorem cost_reverse (lengths : Fin K → ℝ) {source sink : network.V}
    (walk : network.EdgeWalk source sink) : walk.reverse.cost lengths = walk.cost lengths := by
  induction walk with
  | nil => rfl
  | cons edge joins rest induction_hypothesis =>
    simp [reverse, cost, induction_hypothesis, add_comm]

def toGraphWalk (loopless : network.Loopless) {source sink : network.V} :
    network.EdgeWalk source sink → network.toSimpleGraph.Walk source sink
  | nil _ => .nil
  | cons edge joins rest => .cons
      ⟨by rcases joins with ⟨tail_eq, head_eq⟩ | ⟨tail_eq, head_eq⟩
          · exact fun same => loopless edge (tail_eq.trans (same.trans head_eq.symm))
          · exact fun same => loopless edge (tail_eq.trans (same.symm.trans head_eq.symm)),
        joins.elim (fun pair => Or.inl ⟨edge, pair⟩) (fun pair => Or.inr ⟨edge, pair⟩)⟩
      (rest.toGraphWalk loopless)

noncomputable def ofGraphWalk {source sink : network.V}
    (walk : network.toSimpleGraph.Walk source sink) : network.EdgeWalk source sink := by
  induction walk with
  | nil => exact nil _
  | @cons source next sink adjacent rest lifted =>
    have exists_edge : ∃ edge : network.E,
        (network.tail edge = source ∧ network.head edge = next) ∨
          (network.tail edge = next ∧ network.head edge = source) := by
      rcases adjacent.2 with ⟨edge, endpoints⟩ | ⟨edge, endpoints⟩
      · exact ⟨edge, Or.inl endpoints⟩
      · exact ⟨edge, Or.inr endpoints⟩
    exact cons (Classical.choose exists_edge) (Classical.choose_spec exists_edge) lifted

@[simp] theorem toGraphWalk_ofGraphWalk (loopless : network.Loopless)
    {source sink : network.V} (walk : network.toSimpleGraph.Walk source sink) :
    (ofGraphWalk walk).toGraphWalk loopless = walk := by
  induction walk with
  | nil => rfl
  | cons adjacent rest induction_hypothesis =>
    change SimpleGraph.Walk.cons _ ((ofGraphWalk rest).toGraphWalk loopless) = _
    rw [induction_hypothesis]

theorem cost_nonnegative {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {source sink : network.V} (walk : network.EdgeWalk source sink) : 0 ≤ walk.cost lengths := by
  induction walk with
  | nil => exact le_rfl
  | cons edge joins rest induction_hypothesis =>
    exact add_nonneg (nonnegative _) induction_hypothesis

theorem cost_eq_sum_edges (lengths : Fin K → ℝ) {source sink : network.V}
    (walk : network.EdgeWalk source sink) :
    walk.cost lengths = (walk.edges.map (fun edge => lengths (network.color edge))).sum := by
  induction walk with
  | nil => rfl
  | cons edge joins rest induction_hypothesis =>
    simpa only [cost, edges, List.map_cons, List.sum_cons] using
      congrArg (lengths (network.color edge) + ·) induction_hypothesis

end EdgeWalk

variable (rules : RuleFamily K)

@[simp] theorem substEmbed_plantPlus (edge : network.E) :
    network.substEmbed rules edge (rules.βplus (network.color edge)) =
      Sum.inl (network.tail edge) := by simp [substEmbed]

@[simp] theorem substEmbed_plantMinus (edge : network.E) :
    network.substEmbed rules edge (rules.βminus (network.color edge)) =
      Sum.inl (network.head edge) := by
  simp [substEmbed, (rules.plant_ne (network.color edge)).symm]

noncomputable def embedRuleEdgeWalk (edge : network.E)
    {source sink : (rules.R (network.color edge)).V}
    (walk : (rules.R (network.color edge)).EdgeWalk source sink) :
    (network.subst rules).EdgeWalk
      (network.substEmbed rules edge source) (network.substEmbed rules edge sink) := by
  induction walk with
  | nil => exact .nil _
  | cons ruleEdge joins rest lifted =>
    refine EdgeWalk.cons (network := network.subst rules) ⟨edge, ruleEdge⟩ ?_ lifted
    rcases joins with ⟨tail_eq, head_eq⟩ | ⟨tail_eq, head_eq⟩
    · exact Or.inl ⟨congrArg (network.substEmbed rules edge) tail_eq,
        congrArg (network.substEmbed rules edge) head_eq⟩
    · exact Or.inr ⟨congrArg (network.substEmbed rules edge) tail_eq,
        congrArg (network.substEmbed rules edge) head_eq⟩

@[simp] theorem cost_embedRuleEdgeWalk (lengths : Fin K → ℝ) (edge : network.E)
    {source sink : (rules.R (network.color edge)).V}
    (walk : (rules.R (network.color edge)).EdgeWalk source sink) :
    (network.embedRuleEdgeWalk rules edge walk).cost lengths = walk.cost lengths := by
  induction walk with
  | nil => rfl
  | cons ruleEdge joins rest induction_hypothesis =>
    simpa only [embedRuleEdgeWalk, EdgeWalk.cost, subst] using
      congrArg (lengths ((rules.R (network.color edge)).color ruleEdge) + ·) induction_hypothesis

noncomputable def terminalRuleEdgeWalk (edge : network.E)
    (walk : (rules.R (network.color edge)).EdgeWalk
      (rules.βplus (network.color edge)) (rules.βminus (network.color edge))) :
    (network.subst rules).EdgeWalk (Sum.inl (network.tail edge)) (Sum.inl (network.head edge)) :=
  (network.embedRuleEdgeWalk rules edge walk).copy
    (network.substEmbed_plantPlus rules edge) (network.substEmbed_plantMinus rules edge)

@[simp] theorem cost_terminalRuleEdgeWalk (lengths : Fin K → ℝ) (edge : network.E)
    (walk : (rules.R (network.color edge)).EdgeWalk
      (rules.βplus (network.color edge)) (rules.βminus (network.color edge))) :
    (network.terminalRuleEdgeWalk rules edge walk).cost lengths = walk.cost lengths := by
  simp [terminalRuleEdgeWalk]

noncomputable def liftEdgeWalk (selected : ∀ colour, (rules.R colour).EdgeWalk
    (rules.βplus colour) (rules.βminus colour))
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    (network.subst rules).EdgeWalk (Sum.inl source) (Sum.inl sink) := by
  induction walk with
  | nil => exact .nil _
  | @cons source next sink edge joins rest lifted =>
    if forward : network.tail edge = source ∧ network.head edge = next then
      exact ((network.terminalRuleEdgeWalk rules edge (selected (network.color edge))).copy
        (congrArg Sum.inl forward.1) (congrArg Sum.inl forward.2)).append lifted
    else
      have backward := joins.resolve_left forward
      exact ((network.terminalRuleEdgeWalk rules edge (selected (network.color edge))).reverse.copy
        (congrArg Sum.inl backward.2) (congrArg Sum.inl backward.1)).append lifted

/-- Splicing the selected actual rule walks into every base step preserves
exactly the weighted path cost prescribed by those rule walks. -/
theorem cost_liftEdgeWalk (lengths : Fin K → ℝ)
    (selected : ∀ colour, (rules.R colour).EdgeWalk
      (rules.βplus colour) (rules.βminus colour))
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    (network.liftEdgeWalk rules selected walk).cost lengths =
      walk.cost (fun colour => (selected colour).cost lengths) := by
  induction walk with
  | nil => rfl
  | cons edge joins rest induction_hypothesis =>
    simp only [liftEdgeWalk]
    split_ifs <;> simp only [EdgeWalk.cost_append, EdgeWalk.cost_copy,
      EdgeWalk.cost_reverse, cost_terminalRuleEdgeWalk, EdgeWalk.cost]
    all_goals
      apply congrArg ((selected (network.color edge)).cost lengths + ·)
      change (network.liftEdgeWalk rules selected rest).cost lengths = _
      exact induction_hypothesis

end EIGS.Network
