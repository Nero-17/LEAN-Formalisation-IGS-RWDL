import RequestProject.Section1Vertices
import Mathlib.Tactic

/-! The genuine (u,v)-flower: two internally disjoint paths of lengths u
and v with common planting endpoints. The first path is oriented from
minus to plus, the second from plus to minus. This directed representative
is chosen at the definition of the new model; its underlying undirected
rule is the standard two-path cycle. It is distinct from the legacy source
family named Flower, which represents u parallel paths each of length v.
Candidate source, awaiting compilation. -/

namespace EIGS
noncomputable section

abbrev UVFlowerVertex (firstLength secondLength : ℕ) : Type :=
  Bool ⊕ (Fin (firstLength - 1) ⊕ Fin (secondLength - 1))

abbrev UVFlowerEdge (firstLength secondLength : ℕ) : Type :=
  Fin firstLength ⊕ Fin secondLength

def uvFlowerPathTail (length : ℕ) (edge : Fin length) : Bool ⊕ Fin (length - 1) :=
  if first : edge.val = 0 then Sum.inl false
  else Sum.inr ⟨edge.val - 1, by have bound := edge.isLt; omega⟩

def uvFlowerPathHead (length : ℕ) (edge : Fin length) : Bool ⊕ Fin (length - 1) :=
  if last : edge.val + 1 = length then Sum.inl true
  else Sum.inr ⟨edge.val, by have bound := edge.isLt; omega⟩

def uvFlowerLeftEmbedding (firstLength secondLength : ℕ) :
    Bool ⊕ Fin (firstLength - 1) → UVFlowerVertex firstLength secondLength
  | Sum.inl endpoint => Sum.inl endpoint
  | Sum.inr vertex => Sum.inr (Sum.inl vertex)

def uvFlowerRightEmbedding (firstLength secondLength : ℕ) :
    Bool ⊕ Fin (secondLength - 1) → UVFlowerVertex firstLength secondLength
  | Sum.inl endpoint => Sum.inl endpoint
  | Sum.inr vertex => Sum.inr (Sum.inr vertex)

abbrev uvFlowerRuleGraph (firstLength secondLength : ℕ) : ColGraph 1 where
  V := UVFlowerVertex firstLength secondLength
  E := UVFlowerEdge firstLength secondLength
  tail := Sum.elim
    (fun edge => uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge))
    (fun edge => uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge))
  head := Sum.elim
    (fun edge => uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge))
    (fun edge => uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge))
  col _ := 0

abbrev uvFlowerSystem (firstLength secondLength : ℕ) : EIGSData 1 where
  initCol := 0
  rule _ := uvFlowerRuleGraph firstLength secondLength
  plantPlus _ := (Sum.inl false : UVFlowerVertex firstLength secondLength)
  plantMinus _ := (Sum.inl true : UVFlowerVertex firstLength secondLength)
  plant_ne _ := by
    intro equality
    cases Sum.inl.inj equality

end
end EIGS

#print axioms EIGS.uvFlowerRuleGraph
#print axioms EIGS.uvFlowerSystem
