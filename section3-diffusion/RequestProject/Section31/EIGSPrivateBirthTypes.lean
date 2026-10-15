import RequestProject.Section31.EIGSPrimitiveDegreeUnionLimit
import RequestProject.Section2MassGrowth

/-! Literal finite birth types, their actual vertex counts, and their
Perron amplitudes. Each type is a rule colour and a private vertex of that
rule. Equal amplitudes of different types are allowed. Candidate source. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def XiPrivateBirthType (system : EIGSData K) : Type :=
  Σ colour : Fin K, {vertex : (system.rule colour).V //
    vertex ≠ system.plantPlus colour ∧ vertex ≠ system.plantMinus colour}

instance (system : EIGSData K) : Fintype (XiPrivateBirthType system) := by
  unfold XiPrivateBirthType
  infer_instance

def xiPrivateBirthTypeOf (system : EIGSData K) (level : ℕ)
    (vertex : XiNewVertices system level) : XiPrivateBirthType system :=
  ⟨XiCol system.toRuleData level vertex.1, vertex.2⟩

def xiPrivateBirthTypeFiberEquiv (system : EIGSData K) (level : ℕ)
    (colour : Fin K) (privateVertex : {vertex : (system.rule colour).V //
      vertex ≠ system.plantPlus colour ∧ vertex ≠ system.plantMinus colour}) :
    {vertex : XiNewVertices system level // xiPrivateBirthTypeOf system level vertex = ⟨colour, privateVertex⟩} ≃
      {edge : XiEdge system.toRuleData level // XiCol system.toRuleData level edge = colour} where
  toFun := fun vertex => ⟨vertex.val.1, congrArg Sigma.fst vertex.property⟩
  invFun := fun edge => by
    obtain ⟨edge, sameColour⟩ := edge
    cases sameColour
    exact ⟨⟨edge, privateVertex⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨edge, vertex⟩, sameType⟩
    have sameColour := congrArg Sigma.fst sameType
    cases sameColour
    have sameVertex : vertex = privateVertex :=
      eq_of_heq (Sigma.mk.inj_iff.1 sameType).2
    apply Subtype.ext
    change (⟨edge, privateVertex⟩ : XiNewVertices system level) = ⟨edge, vertex⟩
    exact congrArg (fun value => (⟨edge, value⟩ : XiNewVertices system level)) sameVertex.symm
  right_inv := by
    rintro ⟨edge, sameColour⟩
    cases sameColour
    rfl

theorem xiPrivateBirthType_fiber_count (system : EIGSData K) (level : ℕ)
    (kind : XiPrivateBirthType system) :
    Fintype.card {vertex : XiNewVertices system level // xiPrivateBirthTypeOf system level vertex = kind} =
      chiCount system.toRuleData level kind.1 := by
  obtain ⟨colour, privateVertex⟩ := kind
  rw [Fintype.card_congr (xiPrivateBirthTypeFiberEquiv system level colour privateVertex)]
  exact Fintype.card_subtype _

theorem xiPrivateBirthType_occurs_at_level_one (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (kind : XiPrivateBirthType system) :
    ∃ vertex : XiNewVertices system 1, xiPrivateBirthTypeOf system 1 vertex = kind := by
  obtain ⟨colour, privateVertex⟩ := kind
  obtain ⟨ruleEdge, sameColour⟩ :=
    rule_contains_each_colour system connected distancePositive system.initCol colour
  let edge : XiEdge system.toRuleData 1 := ⟨(), ruleEdge⟩
  have colouring : XiCol system.toRuleData 1 edge = colour := by
    simpa only [edge, XiCol, XiLvl, EIGSData.toRuleData] using sameColour
  cases colouring
  exact ⟨⟨edge, privateVertex⟩, rfl⟩

theorem private_vertex_degree_weight_eq_rule_weight (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (level : ℕ) (vertex : XiNewVertices system level) :
    (∑ state, degVec system (level + 1) (Sum.inr vertex) state * weights state) =
      xiRuleDegreeWeight system weights (xiPrivateBirthTypeOf system level vertex).1
        (xiPrivateBirthTypeOf system level vertex).2.val := by
  obtain ⟨edge, privateVertex⟩ := vertex
  rw [Fintype.sum_sum_type]
  unfold xiRuleDegreeWeight
  rw [Fintype.sum_sum_type]
  simp only [degVec, Sum.elim_inl, Sum.elim_inr, outDeg_private, inDeg_private,
    xiPrivateBirthTypeOf]

theorem xiPrivateBirthType_weight_positive (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (kind : XiPrivateBirthType system) :
    0 < xiRuleDegreeWeight system weights kind.1 kind.2.val := by
  obtain ⟨vertex, sameType⟩ := xiPrivateBirthType_occurs_at_level_one system connected distancePositive kind
  have positive := degVec_weighted_positive system connected 2 (Sum.inr vertex) weights weightsPositive
  rw [private_vertex_degree_weight_eq_rule_weight system weights 1 vertex, sameType] at positive
  exact positive

theorem xiDegreeLimitAmplitude_private_birth (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate : ℝ)
    (level : ℕ) (vertex : XiNewVertices system level) :
    xiDegreeLimitAmplitude system weights coefficient rate (Sum.inr ⟨level, vertex⟩) =
      coefficient * xiRuleDegreeWeight system weights
        (xiPrivateBirthTypeOf system level vertex).1 (xiPrivateBirthTypeOf system level vertex).2.val /
        rate ^ (level + 1) := by
  have representative : xiVertexAtLevel system (Sum.inr ⟨level, vertex⟩) (level + 1) le_rfl =
      Sum.inr vertex := by
    apply xiVertexEmbedding_injective system (level + 1)
    rw [xiVertexEmbedding_atLevel]
    rfl
  unfold xiDegreeLimitAmplitude
  change coefficient * (∑ state, degVec system (level + 1)
    (xiVertexAtLevel system (Sum.inr ⟨level, vertex⟩) (level + 1) le_rfl) state * weights state) /
      rate ^ (level + 1) = _
  rw [representative, private_vertex_degree_weight_eq_rule_weight]

end
end EIGS

#print axioms EIGS.xiPrivateBirthTypeFiberEquiv
#print axioms EIGS.xiPrivateBirthType_fiber_count
#print axioms EIGS.xiPrivateBirthType_occurs_at_level_one
#print axioms EIGS.xiPrivateBirthType_weight_positive
#print axioms EIGS.xiDegreeLimitAmplitude_private_birth
