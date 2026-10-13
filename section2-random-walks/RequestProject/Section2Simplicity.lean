import RequestProject.Section2Substitution
import RequestProject.Section2FlowConnectivity

/-!
# Simplicity of substituted networks

Directed edges here represent chosen orientations of undirected edges. Simplicity
therefore means that distinct edges cannot have the same unordered pair of
endpoints. The statements below retain this combinatorial requirement explicitly;
the larger legacy `EIGSData` type alone does not enforce it.
-/

namespace EIGS.Network

open scoped Classical

variable {K : ℕ} (network : EIGS.Network K) (rules : EIGS.RuleFamily K)

def Loopless : Prop := ∀ edge : network.E, network.tail edge ≠ network.head edge

def EdgesUnique : Prop := ∀ first second : network.E,
  ((network.tail first = network.tail second ∧ network.head first = network.head second) ∨
    (network.tail first = network.head second ∧ network.head first = network.tail second)) →
      first = second

/-- The oriented electrical edge set and the simple undirected graph edge set
are equivalent precisely when the network has no loops or repeated edges. -/
noncomputable def simpleEdgeEquiv (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) : network.E ≃ network.toSimpleGraph.edgeSet := by
  classical
  let edge_map : network.E → network.toSimpleGraph.edgeSet := fun edge =>
    ⟨s(network.tail edge, network.head edge),
      ⟨loopless edge, Or.inl ⟨edge, rfl, rfl⟩⟩⟩
  apply Equiv.ofBijective edge_map
  constructor
  · intro first second same
    apply unique_edges first second
    exact Sym2.eq_iff.mp (congrArg Subtype.val same)
  · rintro ⟨pair, edge_mem⟩
    induction pair using Sym2.inductionOn with
    | _ source sink =>
      change network.toSimpleGraph.Adj source sink at edge_mem
      rcases edge_mem.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
      · refine ⟨edge, Subtype.ext ?_⟩
        change s(network.tail edge, network.head edge) = s(source, sink)
        simp [tail_eq, head_eq]
      · refine ⟨edge, Subtype.ext ?_⟩
        change s(network.tail edge, network.head edge) = s(source, sink)
        simp [tail_eq, head_eq, Sym2.eq_iff]

/-- Electrical-network mass is the exact mass appearing in simple-random-walk
commute time, whenever edges are chosen orientations of simple graph edges. -/
theorem card_edges_eq_simpleGraph (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) :
    Fintype.card network.E = network.toSimpleGraph.edgeFinset.card := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  exact Fintype.card_congr (network.simpleEdgeEquiv loopless unique_edges)

/-- A copy vertex embeds injectively when the two skeleton endpoints differ. -/
theorem substEmbed_injective (loopless : network.Loopless) (edge : network.E) :
    Function.Injective (network.substEmbed rules edge) := by
  intro first second same
  unfold Network.substEmbed at same
  split_ifs at same <;> simp_all
  all_goals first | exact (loopless edge same).elim | exact (loopless edge same.symm).elim | grind

theorem subst_loopless (loopless : network.Loopless)
    (rules_loopless : ∀ colour, (rules.R colour).Loopless) :
    (network.subst rules).Loopless := by
  intro edge same
  apply rules_loopless (network.color edge.1) edge.2
  exact network.substEmbed_injective rules loopless edge.1 same

/-- A shared embedded interior vertex must belong to the same rule copy. -/
theorem substEmbed_copy_of_inner (first second : network.E)
    (interior : network.SubstInner rules first)
    (vertex : (rules.R (network.color second)).V)
    (same : network.substEmbed rules first interior.1 =
      network.substEmbed rules second vertex) : first = second := by
  unfold Network.substEmbed at same
  simp only [interior.property.1, interior.property.2, ↓reduceDIte] at same
  split_ifs at same <;> simp_all

/-- Nonadjacent distinct planting vertices and looplessness force every rule
edge to have an interior endpoint. -/
theorem rule_edge_has_interior_endpoint (colour : Fin K)
    (loopless : (rules.R colour).Loopless)
    (planting_nonadjacent : ¬ (rules.R colour).toSimpleGraph.Adj
      (rules.βplus colour) (rules.βminus colour)) (edge : (rules.R colour).E) :
    (((rules.R colour).tail edge ≠ rules.βplus colour ∧
      (rules.R colour).tail edge ≠ rules.βminus colour) ∨
     ((rules.R colour).head edge ≠ rules.βplus colour ∧
      (rules.R colour).head edge ≠ rules.βminus colour)) := by
  by_contra no_interior
  push_neg at no_interior
  have tail_planting : (rules.R colour).tail edge = rules.βplus colour ∨
      (rules.R colour).tail edge = rules.βminus colour := by tauto
  have head_planting : (rules.R colour).head edge = rules.βplus colour ∨
      (rules.R colour).head edge = rules.βminus colour := by tauto
  rcases tail_planting with tail_plus | tail_minus <;>
    rcases head_planting with head_plus | head_minus
  · exact loopless edge (tail_plus.trans head_plus.symm)
  · exact planting_nonadjacent ⟨rules.plant_ne colour,
      Or.inl ⟨edge, tail_plus, head_minus⟩⟩
  · exact planting_nonadjacent ⟨rules.plant_ne colour,
      Or.inr ⟨edge, tail_minus, head_plus⟩⟩
  · exact loopless edge (tail_minus.trans head_minus.symm)

/-- Rule edges touching an interior vertex prevent different copies from
creating parallel undirected edges. -/
theorem subst_edges_unique (loopless : network.Loopless)
    (rules_unique : ∀ colour, (rules.R colour).EdgesUnique)
    (rule_edges_interior : ∀ colour (edge : (rules.R colour).E),
      (((rules.R colour).tail edge ≠ rules.βplus colour ∧
        (rules.R colour).tail edge ≠ rules.βminus colour) ∨
       ((rules.R colour).head edge ≠ rules.βplus colour ∧
        (rules.R colour).head edge ≠ rules.βminus colour))) :
    (network.subst rules).EdgesUnique := by
  rintro ⟨first, firstEdge⟩ ⟨second, secondEdge⟩ (same | reverse)
  · have same_copy : first = second := by
      rcases rule_edges_interior (network.color first) firstEdge with interior | interior
      · exact network.substEmbed_copy_of_inner rules first second
          ⟨_, interior⟩ _ same.1
      · exact network.substEmbed_copy_of_inner rules first second
          ⟨_, interior⟩ _ same.2
    subst second
    have same_edge : firstEdge = secondEdge := rules_unique _ _ _ (Or.inl
      ⟨network.substEmbed_injective rules loopless first same.1,
        network.substEmbed_injective rules loopless first same.2⟩)
    cases same_edge
    rfl
  · have same_copy : first = second := by
      rcases rule_edges_interior (network.color first) firstEdge with interior | interior
      · exact network.substEmbed_copy_of_inner rules first second
          ⟨_, interior⟩ _ reverse.1
      · exact network.substEmbed_copy_of_inner rules first second
          ⟨_, interior⟩ _ reverse.2
    subst second
    have same_edge : firstEdge = secondEdge := rules_unique _ _ _ (Or.inr
      ⟨network.substEmbed_injective rules loopless first reverse.1,
        network.substEmbed_injective rules loopless first reverse.2⟩)
    cases same_edge
    rfl

theorem substIter_loopless (loopless : network.Loopless)
    (rules_loopless : ∀ colour, (rules.R colour).Loopless) (level : ℕ) :
    (network.substIter rules level).Loopless := by
  induction level with
  | zero => exact loopless
  | succ level induction =>
      exact (network.substIter rules level).subst_loopless
        rules induction rules_loopless

theorem substIter_edges_unique (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique)
    (rules_loopless : ∀ colour, (rules.R colour).Loopless)
    (rules_unique : ∀ colour, (rules.R colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (rules.R colour).toSimpleGraph.Adj
      (rules.βplus colour) (rules.βminus colour)) (level : ℕ) :
    (network.substIter rules level).EdgesUnique := by
  induction level with
  | zero => exact unique_edges
  | succ level induction =>
      exact (network.substIter rules level).subst_edges_unique rules
        (network.substIter_loopless rules loopless rules_loopless level) rules_unique
        (fun colour edge => rule_edge_has_interior_endpoint rules colour
          (rules_loopless colour) (planting_nonadjacent colour) edge)

/-- Exact edge mass at every substitution level, with no loss of multiplicity
when passing from the electrical edge set to the walk's simple graph. -/
theorem substIter_card_edges_eq_simpleGraph (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique)
    (rules_loopless : ∀ colour, (rules.R colour).Loopless)
    (rules_unique : ∀ colour, (rules.R colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (rules.R colour).toSimpleGraph.Adj
      (rules.βplus colour) (rules.βminus colour)) (level : ℕ) :
    Fintype.card (network.substIter rules level).E =
      (network.substIter rules level).toSimpleGraph.edgeFinset.card := by
  exact (network.substIter rules level).card_edges_eq_simpleGraph
    (network.substIter_loopless rules loopless rules_loopless level)
    (network.substIter_edges_unique rules loopless unique_edges rules_loopless rules_unique
      planting_nonadjacent level)

end EIGS.Network
