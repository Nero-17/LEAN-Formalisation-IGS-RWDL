import RequestProject.Section31.EIGSStationaryDegreeBirthFormula
import RequestProject.Section31.FiniteGeometricLadderCollisions

/-! The full stationary degree point fiber on the actual vertex union is
the disjoint sum of the initial endpoint fiber and the actual private
birth fibers of all colliding codes. This is a point count, not a tail
probability or a mass-to-degree ratio. Candidate source. -/

namespace EIGS
noncomputable section
variable {K : ℕ}

def XiStationaryDegreeCode (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer value : ℝ) : Type :=
  {code : XiPrivateBirthType system × ℕ //
    xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer code.1 /
      rate ^ code.2 = value}

def xiStationaryDegreeFiberEquiv (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer value : ℝ) :
    {vertex : XiVertexUnion system //
      xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} ≃
    ({vertex : Bool // xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer
        (Sum.inl vertex) = value} ⊕
      Σ code : XiStationaryDegreeCode system weights coefficient rate normalizer value,
        {vertex : XiNewVertices system code.val.2 // xiPrivateBirthTypeOf system code.val.2 vertex = code.val.1}) where
  toFun := fun vertex => by
    obtain ⟨vertex, sameValue⟩ := vertex
    cases vertex with
    | inl initial => exact Sum.inl ⟨initial, sameValue⟩
    | inr privateBirth =>
      obtain ⟨level, privateVertex⟩ := privateBirth
      refine Sum.inr ⟨⟨(xiPrivateBirthTypeOf system level privateVertex, level), ?_⟩,
        ⟨privateVertex, rfl⟩⟩
      exact (xiStationaryDegree_private_birth_formula system weights coefficient rate normalizer
        level privateVertex).symm.trans sameValue
  invFun := fun vertex => by
    cases vertex with
    | inl initial => exact ⟨Sum.inl initial.val, initial.property⟩
    | inr privateBirth =>
      obtain ⟨code, privateVertex⟩ := privateBirth
      refine ⟨Sum.inr ⟨code.val.2, privateVertex.val⟩, ?_⟩
      rw [xiStationaryDegree_private_birth_formula, privateVertex.property]
      exact code.property
  left_inv := by
    rintro ⟨initial | ⟨level, privateVertex⟩, sameValue⟩ <;> rfl
  right_inv := by
    rintro (⟨initial, sameValue⟩ | ⟨⟨⟨kind, level⟩, sameValue⟩, ⟨privateVertex, sameType⟩⟩)
    · rfl
    · apply congrArg Sum.inr
      apply Sigma.ext
      · apply Subtype.ext
        exact Prod.ext sameType rfl
      · exact (Subtype.heq_iff_coe_eq (fun vertex => by
          change xiPrivateBirthTypeOf system level vertex =
              xiPrivateBirthTypeOf system level privateVertex ↔
            xiPrivateBirthTypeOf system level vertex = kind
          rw [sameType])).2 rfl

theorem xiStationaryDegree_fiber_finite (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (coefficient rate normalizer : ℝ) (coefficientPositive : 0 < coefficient)
    (rateGreaterThanOne : 1 < rate) (normalizerPositive : 0 < normalizer) (value : ℝ) :
    Finite {vertex : XiVertexUnion system //
      xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} := by
  classical
  have codeFinite := (finite_geometric_ladder_fiber_bound
    (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer)
    (xiPrivateDegreeLadderCoefficient_positive system connected distancePositive weights weightsPositive
      coefficient rate normalizer coefficientPositive (zero_lt_one.trans rateGreaterThanOne) normalizerPositive)
    rate rateGreaterThanOne value).1
  letI : Finite (XiStationaryDegreeCode system weights coefficient rate normalizer value) := codeFinite
  exact Finite.of_equiv _ (xiStationaryDegreeFiberEquiv system weights coefficient rate normalizer value).symm

end
end EIGS

#print axioms EIGS.xiStationaryDegreeFiberEquiv
#print axioms EIGS.xiStationaryDegree_fiber_finite
