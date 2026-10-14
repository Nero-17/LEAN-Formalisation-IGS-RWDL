import RequestProject.Section1Connected
import RequestProject.Section2Simplicity
import Mathlib.Tactic

/-! The actual one-colour flower rule: `branches` parallel chains, each
with `segments` edges. The first chain is oriented backwards and all
others forwards. This changes no undirected edge or resistance, and for
at least two branches supplies both endpoint degree states. Scalar
dimension formulas are not treated as an actual rule construction. -/

namespace EIGS
noncomputable section
open scoped Classical

def flowerPoint (branches segments : ℕ) (branch : Fin branches)
    (position : Fin (segments + 1)) : Bool ⊕ (Fin branches × Fin (segments - 1)) :=
  if atSource : position.val = 0 then Sum.inl false
  else if atSink : position.val = segments then Sum.inl true
  else Sum.inr (branch, ⟨position.val - 1, by omega⟩)

def flowerHeight (branches segments : ℕ) : Bool ⊕ (Fin branches × Fin (segments - 1)) → ℕ
  | Sum.inl terminal => if terminal then segments else 0
  | Sum.inr interior => interior.2.val + 1

@[simp] theorem flowerPoint_height (branches segments : ℕ) (branch : Fin branches)
    (position : Fin (segments + 1)) :
    flowerHeight branches segments (flowerPoint branches segments branch position) = position.val := by
  unfold flowerPoint
  split_ifs with atSource atSink
  · simp [flowerHeight, atSource]
  · simp [flowerHeight, atSink]
  · simp only [flowerHeight]
    omega

def flowerEdgeStart (branches segments : ℕ) (edge : Fin branches × Fin segments) :
    Bool ⊕ (Fin branches × Fin (segments - 1)) :=
  flowerPoint branches segments edge.1 ⟨edge.2.val, by omega⟩

def flowerEdgeEnd (branches segments : ℕ) (edge : Fin branches × Fin segments) :
    Bool ⊕ (Fin branches × Fin (segments - 1)) :=
  flowerPoint branches segments edge.1 ⟨edge.2.val + 1, by omega⟩

def flowerGraph (branches segments : ℕ) : ColGraph 1 where
  V := Bool ⊕ (Fin branches × Fin (segments - 1))
  E := Fin branches × Fin segments
  tail edge := if edge.1.val = 0 then flowerEdgeEnd branches segments edge
    else flowerEdgeStart branches segments edge
  head edge := if edge.1.val = 0 then flowerEdgeStart branches segments edge
    else flowerEdgeEnd branches segments edge
  col _ := 0

def flowerSystem (branches segments : ℕ) : EIGSData 1 where
  initCol := 0
  rule _ := flowerGraph branches segments
  plantPlus _ := Sum.inl false
  plantMinus _ := Sum.inl true
  plant_ne _ := by simp

theorem flowerGraph_edge_height (branches segments : ℕ)
    (edge : Fin branches × Fin segments) :
    (flowerHeight branches segments ((flowerGraph branches segments).tail edge) = edge.2.val ∧
      flowerHeight branches segments ((flowerGraph branches segments).head edge) = edge.2.val + 1) ∨
    (flowerHeight branches segments ((flowerGraph branches segments).tail edge) = edge.2.val + 1 ∧
      flowerHeight branches segments ((flowerGraph branches segments).head edge) = edge.2.val) := by
  by_cases backwards : edge.1.val = 0
  · right
    simp [flowerGraph, backwards, flowerEdgeStart, flowerEdgeEnd]
  · left
    simp [flowerGraph, backwards, flowerEdgeStart, flowerEdgeEnd]

theorem flowerGraph_edges (branches segments : ℕ) :
    Fintype.card (flowerGraph branches segments).E = branches * segments := by
  simp [flowerGraph]

theorem flowerGraph_vertices (branches segments : ℕ) :
    Fintype.card (flowerGraph branches segments).V = 2 + branches * (segments - 1) := by
  simp [flowerGraph]

theorem flowerSystem_loopless (branches segments : ℕ) (colour : Fin 1) :
    ((flowerSystem branches segments).ruleNetwork colour).Loopless := by
  intro edge equality
  have equalHeight := congrArg (flowerHeight branches segments) equality
  change flowerHeight branches segments ((flowerGraph branches segments).tail edge) =
    flowerHeight branches segments ((flowerGraph branches segments).head edge) at equalHeight
  rcases flowerGraph_edge_height branches segments edge with heights | heights <;>
    omega

end
end EIGS

#print axioms EIGS.flowerPoint_height
#print axioms EIGS.flowerGraph_edge_height
#print axioms EIGS.flowerGraph_edges
#print axioms EIGS.flowerGraph_vertices
#print axioms EIGS.flowerSystem_loopless
