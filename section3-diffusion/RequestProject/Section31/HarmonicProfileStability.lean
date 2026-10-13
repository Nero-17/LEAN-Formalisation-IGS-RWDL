import RequestProject.Section31.EIGSCellConvexity
import RequestProject.Section31.EnergyOrthogonality

/-! Quantitative stability of actual finite harmonic profiles. The edge set and
endpoint maps remain unchanged; only positive colour resistances vary. -/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K)

theorem potential_energy_change_le_conductance_difference
    (firstResistances secondResistances : Fin K → ℝ)
    (firstPositive : ∀ colour, 0 < firstResistances colour)
    (secondPositive : ∀ colour, 0 < secondResistances colour)
    (potential : network.V → ℝ)
    (potentialRange : ∀ vertex, 0 ≤ potential vertex ∧ potential vertex ≤ 1) :
    |(network.potentialNetwork secondResistances secondPositive).energy potential -
        (network.potentialNetwork firstResistances firstPositive).energy potential| ≤
      ∑ edge, |(secondResistances (network.color edge))⁻¹ -
        (firstResistances (network.color edge))⁻¹| := by
  classical
  have energyDifference :
      (network.potentialNetwork secondResistances secondPositive).energy potential -
        (network.potentialNetwork firstResistances firstPositive).energy potential =
      ∑ edge, ((secondResistances (network.color edge))⁻¹ -
        (firstResistances (network.color edge))⁻¹) *
          (potential (network.tail edge) - potential (network.head edge)) ^ 2 := by
    simp only [FiniteNetwork.energy, potentialNetwork, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  rw [energyDifference]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro edge _
  rw [abs_mul, abs_of_nonneg (sq_nonneg (potential (network.tail edge) - potential (network.head edge)))]
  have differenceBound : |potential (network.tail edge) - potential (network.head edge)| ≤ 1 :=
    abs_le.2 ⟨by linarith [(potentialRange (network.tail edge)).1, (potentialRange (network.head edge)).2],
      by linarith [(potentialRange (network.tail edge)).2, (potentialRange (network.head edge)).1]⟩
  have squareBound : (potential (network.tail edge) - potential (network.head edge)) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 differenceBound
  exact mul_le_of_le_one_right (abs_nonneg _) squareBound

theorem unit_potential_profiles_residual_energy_bound
    (firstResistances secondResistances : Fin K → ℝ)
    (firstPositive : ∀ colour, 0 < firstResistances colour)
    (secondPositive : ∀ colour, 0 < secondResistances colour)
    (connected : network.toSimpleGraph.Connected) (source sink : network.V)
    (firstProfile secondProfile : network.V → ℝ)
    (firstSource : firstProfile source = 1) (firstSink : firstProfile sink = 0)
    (secondSource : secondProfile source = 1) (secondSink : secondProfile sink = 0)
    (firstMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork firstResistances firstPositive).energy firstProfile ≤
          (network.potentialNetwork firstResistances firstPositive).energy competitor)
    (secondMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork secondResistances secondPositive).energy secondProfile ≤
          (network.potentialNetwork secondResistances secondPositive).energy competitor) :
    (network.potentialNetwork firstResistances firstPositive).energy (secondProfile - firstProfile) ≤
      2 * ∑ edge, |(secondResistances (network.color edge))⁻¹ -
        (firstResistances (network.color edge))⁻¹| := by
  have firstRange := network.unit_potential_minimum_range firstResistances firstPositive connected
    source sink firstProfile firstSource firstSink firstMinimal
  have secondRange := network.unit_potential_minimum_range secondResistances secondPositive connected
    source sink secondProfile secondSource secondSink secondMinimal
  have firstError := network.potential_energy_change_le_conductance_difference firstResistances secondResistances
    firstPositive secondPositive firstProfile firstRange
  have secondError := network.potential_energy_change_le_conductance_difference firstResistances secondResistances
    firstPositive secondPositive secondProfile secondRange
  have pythagoras := (network.potentialNetwork firstResistances firstPositive).energy_sub_of_min
    {vertex | vertex = source ∨ vertex = sink} firstProfile firstProfile (fun _ _ => rfl)
    (by
      intro competitor competitorBoundary
      apply firstMinimal competitor
      · exact (competitorBoundary source (Or.inl rfl)).trans firstSource
      · exact (competitorBoundary sink (Or.inr rfl)).trans firstSink)
    secondProfile (by
      intro vertex membership
      rcases membership with rfl | rfl
      · rw [secondSource, firstSource]
      · rw [secondSink, firstSink])
  have secondComparison := secondMinimal firstProfile firstSource firstSink
  linarith [(abs_le.1 firstError).2, (abs_le.1 secondError).1]

theorem exists_unit_potential_profile_stability_bound
    (firstResistances : Fin K → ℝ) (firstPositive : ∀ colour, 0 < firstResistances colour)
    (connected : network.toSimpleGraph.Connected) (source sink : network.V)
    (firstProfile : network.V → ℝ)
    (firstSource : firstProfile source = 1) (firstSink : firstProfile sink = 0)
    (firstMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork firstResistances firstPositive).energy firstProfile ≤
          (network.potentialNetwork firstResistances firstPositive).energy competitor) :
    ∃ stabilityConstant : ℝ, 0 ≤ stabilityConstant ∧
      ∀ (secondResistances : Fin K → ℝ) (secondPositive : ∀ colour, 0 < secondResistances colour)
        (secondProfile : network.V → ℝ),
        secondProfile source = 1 → secondProfile sink = 0 →
        (∀ competitor : network.V → ℝ,
          competitor source = 1 → competitor sink = 0 →
            (network.potentialNetwork secondResistances secondPositive).energy secondProfile ≤
              (network.potentialNetwork secondResistances secondPositive).energy competitor) →
        ∀ vertex, (secondProfile vertex - firstProfile vertex) ^ 2 ≤
          stabilityConstant * ∑ edge, |(secondResistances (network.color edge))⁻¹ -
            (firstResistances (network.color edge))⁻¹| := by
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant firstResistances firstPositive source connected
  refine ⟨2 * poincareConstant, mul_nonneg (by norm_num) poincareNonnegative, ?_⟩
  intro secondResistances secondPositive secondProfile secondSource secondSink secondMinimal vertex
  have residualEnergy := network.unit_potential_profiles_residual_energy_bound firstResistances secondResistances
    firstPositive secondPositive connected source sink firstProfile secondProfile
      firstSource firstSink secondSource secondSink firstMinimal secondMinimal
  calc
    (secondProfile vertex - firstProfile vertex) ^ 2 ≤
        poincareConstant * (network.potentialNetwork firstResistances firstPositive).energy
          (secondProfile - firstProfile) :=
      poincareBound (secondProfile - firstProfile) (by simp [secondSource, firstSource]) vertex
    _ ≤ poincareConstant * (2 * ∑ edge, |(secondResistances (network.color edge))⁻¹ -
          (firstResistances (network.color edge))⁻¹|) :=
      mul_le_mul_of_nonneg_left residualEnergy poincareNonnegative
    _ = (2 * poincareConstant) * ∑ edge, |(secondResistances (network.color edge))⁻¹ -
          (firstResistances (network.color edge))⁻¹| := by ring

end EIGS.Network
