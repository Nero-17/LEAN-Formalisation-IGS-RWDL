import RequestProject.Section31.EIGSPrivateVertexDegree

/-! Actual Perron-weighted degrees are exactly geometric along old vertices.
The weights of all actual private birth states have a finite rule-only bound.
This supplies the uniform recent-birth tail for global maximum normalization.
Candidate source. -/

namespace EIGS
open scoped BigOperators
noncomputable section
variable {K : ℕ}

def xiRuleDegreeWeight (system : EIGSData K) (weights : Fin K ⊕ Fin K → ℝ)
    (colour : Fin K) (vertex : (system.rule colour).V) : ℝ :=
  ∑ state, (Sum.elim
    (fun edgeColour => (ruleTailDeg system colour vertex edgeColour : ℝ))
    (fun edgeColour => (ruleHeadDeg system colour vertex edgeColour : ℝ)) state) * weights state

def xiPrivateBirthWeightBound (system : EIGSData K) (weights : Fin K ⊕ Fin K → ℝ) : ℝ :=
  1 + ∑ colour, ∑ vertex : (system.rule colour).V, xiRuleDegreeWeight system weights colour vertex

theorem xiRuleDegreeWeight_nonnegative (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (nonnegative : ∀ state, 0 ≤ weights state)
    (colour : Fin K) (vertex : (system.rule colour).V) :
    0 ≤ xiRuleDegreeWeight system weights colour vertex := by
  apply Finset.sum_nonneg
  intro state _
  cases state <;> exact mul_nonneg (Nat.cast_nonneg _) (nonnegative _)

theorem xiPrivateBirthWeightBound_positive (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (nonnegative : ∀ state, 0 ≤ weights state) :
    0 < xiPrivateBirthWeightBound system weights := by
  have sumNonnegative : 0 ≤ ∑ colour, ∑ vertex : (system.rule colour).V,
      xiRuleDegreeWeight system weights colour vertex :=
    Finset.sum_nonneg (fun colour _ => Finset.sum_nonneg
      (fun vertex _ => xiRuleDegreeWeight_nonnegative system weights nonnegative colour vertex))
  unfold xiPrivateBirthWeightBound
  linarith

theorem xiRuleDegreeWeight_le_birth_bound (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (nonnegative : ∀ state, 0 ≤ weights state)
    (colour : Fin K) (vertex : (system.rule colour).V) :
    xiRuleDegreeWeight system weights colour vertex ≤ xiPrivateBirthWeightBound system weights := by
  have vertexBound := Finset.single_le_sum
    (fun other _ => xiRuleDegreeWeight_nonnegative system weights nonnegative colour other)
    (Finset.mem_univ vertex)
  have colourBound :
      (∑ vertex : (system.rule colour).V, xiRuleDegreeWeight system weights colour vertex) ≤
        ∑ other : Fin K, ∑ vertex : (system.rule other).V,
          xiRuleDegreeWeight system weights other vertex := Finset.single_le_sum
    (f := fun other : Fin K => ∑ vertex : (system.rule other).V,
      xiRuleDegreeWeight system weights other vertex)
    (fun other _ => Finset.sum_nonneg
      (fun vertex _ => xiRuleDegreeWeight_nonnegative system weights nonnegative other vertex))
    (Finset.mem_univ colour)
  have combined := vertexBound.trans colourBound
  unfold xiPrivateBirthWeightBound
  linarith

theorem private_vertex_degree_weight_le_birth_bound (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (nonnegative : ∀ state, 0 ≤ weights state)
    (level : ℕ) (edge : XiEdge system.toRuleData level)
    (privateVertex : {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
      vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)}) :
    (∑ state, degVec system (level + 1) (Sum.inr ⟨edge, privateVertex⟩) state * weights state) ≤
      xiPrivateBirthWeightBound system weights := by
  have identity :
      (∑ state, degVec system (level + 1) (Sum.inr ⟨edge, privateVertex⟩) state * weights state) =
        xiRuleDegreeWeight system weights (XiCol system.toRuleData level edge) privateVertex.val := by
    rw [Fintype.sum_sum_type]
    unfold xiRuleDegreeWeight
    rw [Fintype.sum_sum_type]
    simp only [degVec, Sum.elim_inl, Sum.elim_inr, outDeg_private, inDeg_private]
  rw [identity]
  exact xiRuleDegreeWeight_le_birth_bound system weights nonnegative _ _

theorem degree_eigenweight_forward (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (rate : ℝ)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights)
    (birth age : ℕ) (vertex : XiVtx system birth) :
    (∑ state, degVec system (birth + age) (xiForward system birth age vertex) state * weights state) =
      rate ^ age * (∑ state, degVec system birth vertex state * weights state) := by
  induction age with
  | zero => simp [xiForward]
  | succ age induction =>
      rw [degVec_xiForward_succ]
      have step :
          (∑ state, (Matrix.vecMul
            (degVec system (birth + age) (xiForward system birth age vertex))
            (degreeMatrix system)) state * weights state) =
          rate * (∑ state, degVec system (birth + age)
            (xiForward system birth age vertex) state * weights state) := by
        change dotProduct (Matrix.vecMul _ (degreeMatrix system)) weights = _
        rw [← Matrix.dotProduct_mulVec, eigenpair]
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro state _
        ring
      rw [step, induction, pow_succ]
      ring

end
end EIGS

#print axioms EIGS.xiPrivateBirthWeightBound_positive
#print axioms EIGS.private_vertex_degree_weight_le_birth_bound
#print axioms EIGS.degree_eigenweight_forward
