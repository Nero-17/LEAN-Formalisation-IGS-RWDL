import RequestProject.Section31.EIGSRecentVertexIncidence
import RequestProject.Section2SpectralGrowth

/-! Uniform actual incidence bound, including vertices inherited from the
initial graph. Recent-vertex bounds and the two initial vertex orbits are
combined without a bound on birth ages as an assumption. -/

namespace EIGS
open scoped Classical BigOperators
noncomputable section
variable {K : ℕ}

theorem exists_xiUniformVertex_incidence_bound (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ level (vertex : XiVtx system level),
      (xiVertexIncidenceCount system level vertex : ℝ) ≤
        coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ level := by
  obtain ⟨recentConstant, recentPositive, recentBound⟩ :=
    exists_xiRecentVertex_incidence_bound system primitiveDegree
  obtain ⟨degreePositive, degreeGrowth⟩ :=
    degree_spectral_growth_from_primitive_rules system connected primitiveDegree
  choose lower upper lowerPositive upperPositive bounds using degreeGrowth 0
  let coefficient := recentConstant + 1 + ∑ initial : XiVtx system 0, upper initial
  have coefficientPositive : 0 < coefficient := by
    dsimp only [coefficient]
    exact add_pos_of_pos_of_nonneg (by linarith) (Finset.sum_nonneg (fun _ _ => (upperPositive _).le))
  have recentComparison : recentConstant ≤ coefficient := by
    have sumNonnegative := Finset.sum_nonneg (s := Finset.univ) (fun initial _ => (upperPositive initial).le)
    dsimp only [coefficient]
    linarith
  have initialComparison (initial : XiVtx system 0) : upper initial ≤ coefficient := by
    have summand := Finset.single_le_sum (fun other _ => (upperPositive other).le)
      (Finset.mem_univ initial)
    dsimp only [coefficient]
    linarith
  refine ⟨coefficient, coefficientPositive, ?_⟩
  suffices allLevels : ∀ level (vertex : XiVtx system (0 + level)),
      (xiVertexIncidenceCount system (0 + level) vertex : ℝ) ≤
        coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ level by
    intro level
    have transported : ∀ index : ℕ, 0 + level = index → ∀ vertex : XiVtx system index,
        (xiVertexIncidenceCount system index vertex : ℝ) ≤
          coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ level := by
      intro index equality
      subst index
      exact allLevels level
    exact transported level (Nat.zero_add level)
  intro level vertex
  by_cases inherited : ∃ initial : XiVtx system 0, xiForward system 0 level initial = vertex
  · obtain ⟨initial, equality⟩ := inherited
    have initialBound := (bounds initial level).2
    rw [← xiVertexIncidenceCount_eq_degree_state_sum] at initialBound
    have actual : (xiVertexIncidenceCount system (0 + level) vertex : ℝ) ≤
        upper initial * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ level := by
      simpa only [equality] using initialBound
    exact actual.trans (mul_le_mul_of_nonneg_right (initialComparison initial)
      (pow_nonneg degreePositive.le level))
  · have noInitial : ∀ initial : XiVtx system 0, xiForward system 0 level initial ≠ vertex := by
      simpa only [not_exists] using inherited
    have recent := recentBound 0 level vertex noInitial
    exact recent.trans (mul_le_mul_of_nonneg_right recentComparison (pow_nonneg degreePositive.le level))

end
end EIGS

#print axioms EIGS.exists_xiUniformVertex_incidence_bound
