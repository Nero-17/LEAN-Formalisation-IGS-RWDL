import RequestProject.Section31.EIGSTwoColourBirthAndMaximumDegree
import RequestProject.Section31.EIGSVertexInclusion

/-! The stationary normalized degree on the actual common vertex union,
using the finite graph degree divided by its actual maximum degree.
This implements the objects in Li--Britz, arXiv:2109.14463v2, Definition 3.1.
The multiplicity/support limit in Definition 3.2 is a separate obligation.
Candidate source. -/

namespace EIGS
open Filter Topology
open scoped Classical
noncomputable section
variable {K : ℕ}

def xiUnionBirthVertex (system : EIGSData K) :
    (vertex : XiVertexUnion system) → XiVtx system (xiUnionBirth system vertex)
  | Sum.inl vertex => vertex
  | Sum.inr ⟨level, privateVertex⟩ => Sum.inr privateVertex

theorem xiUnionBirthVertex_embedding (system : EIGSData K) (vertex : XiVertexUnion system) :
    xiVertexEmbedding system (xiUnionBirth system vertex) (xiUnionBirthVertex system vertex) =
      vertex := by
  rcases vertex with vertex | ⟨level, privateVertex⟩ <;> rfl

def twoColourStationaryNormalizedDegree (vertex : XiVertexUnion twoColourSystem) : ℝ :=
  2 * ((XiSimpleGraph twoColourSystem (xiUnionBirth twoColourSystem vertex)).degree
    (xiUnionBirthVertex twoColourSystem vertex) : ℝ) /
      (3 * (2 : ℝ) ^ xiUnionBirth twoColourSystem vertex)

theorem twoColourSystem_normalized_degree_at_every_later_level
    (vertex : XiVertexUnion twoColourSystem) (age : ℕ) :
    ((XiSimpleGraph twoColourSystem (xiUnionBirth twoColourSystem vertex + (age + 1))).degree
      (xiForward twoColourSystem (xiUnionBirth twoColourSystem vertex) (age + 1)
        (xiUnionBirthVertex twoColourSystem vertex)) : ℝ) /
    ((XiSimpleGraph twoColourSystem (xiUnionBirth twoColourSystem vertex + (age + 1))).maxDegree : ℝ) =
      twoColourStationaryNormalizedDegree vertex := by
  rw [twoColourSystem_simpleGraph_degree_forward]
  change _ / ((XiSimpleGraph twoColourSystem
    ((xiUnionBirth twoColourSystem vertex + age) + 1)).maxDegree : ℝ) = _
  rw [twoColourSystem_maxDegree]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    twoColourStationaryNormalizedDegree, pow_add, pow_succ]
  field_simp <;> ring

theorem twoColourSystem_stationary_normalized_degree (vertex : XiVertexUnion twoColourSystem) :
    Tendsto (fun age : ℕ =>
      ((XiSimpleGraph twoColourSystem (xiUnionBirth twoColourSystem vertex + (age + 1))).degree
        (xiForward twoColourSystem (xiUnionBirth twoColourSystem vertex) (age + 1)
          (xiUnionBirthVertex twoColourSystem vertex)) : ℝ) /
      ((XiSimpleGraph twoColourSystem
        (xiUnionBirth twoColourSystem vertex + (age + 1))).maxDegree : ℝ))
      atTop (𝓝 (twoColourStationaryNormalizedDegree vertex)) := by
  exact tendsto_const_nhds.congr
    (fun age => (twoColourSystem_normalized_degree_at_every_later_level vertex age).symm)

theorem twoColourSystem_original_normalized_degree (vertex : Bool) :
    twoColourStationaryNormalizedDegree (Sum.inl vertex) = 2 / 3 := by
  simp only [twoColourStationaryNormalizedDegree, xiUnionBirth, xiUnionBirthVertex,
    twoColourSystem_initial_degree]
  norm_num

theorem twoColourSystem_private_normalized_degree (level : ℕ)
    (edge : XiEdge twoColourSystem.toRuleData level)
    (privateVertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4}) :
    twoColourStationaryNormalizedDegree (Sum.inr ⟨level, ⟨edge, privateVertex⟩⟩) =
      if XiCol twoColourSystem.toRuleData level edge = 0 ∧
        (privateVertex.val = 1 ∨ privateVertex.val = 3)
      then 1 / (2 : ℝ) ^ level else (2 / 3) / (2 : ℝ) ^ level := by
  simp only [twoColourStationaryNormalizedDegree, xiUnionBirth, xiUnionBirthVertex,
    twoColourSystem_private_birth_degree, pow_succ]
  split_ifs <;> norm_num <;> field_simp <;> ring

theorem twoColourSystem_stationary_normalized_degree_positive
    (vertex : XiVertexUnion twoColourSystem) :
    0 < twoColourStationaryNormalizedDegree vertex := by
  rcases vertex with vertex | ⟨level, edge, privateVertex⟩
  · rw [twoColourSystem_original_normalized_degree]
    norm_num
  · rw [twoColourSystem_private_normalized_degree]
    split_ifs <;> positivity

end
end EIGS

#print axioms EIGS.xiUnionBirthVertex_embedding
#print axioms EIGS.twoColourSystem_stationary_normalized_degree
#print axioms EIGS.twoColourSystem_private_normalized_degree
#print axioms EIGS.twoColourSystem_stationary_normalized_degree_positive
