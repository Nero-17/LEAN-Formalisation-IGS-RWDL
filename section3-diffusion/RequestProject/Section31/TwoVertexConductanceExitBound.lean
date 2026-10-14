import RequestProject.Section31.WatchedChain

/-! A uniform mean-jump bound for leaving two distinct states. One state
has an exterior conductance bounded below, while its conductance to the other
state is bounded above. All additional exterior edges improve the estimate;
no degree or ambient-cardinality upper bound is used. Candidate source. -/

namespace IGS.Sec31
open scoped Classical BigOperators
noncomputable section
variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem two_vertex_partialHit_le (chain : FinChain Vertex) (first second : Vertex)
    (distinct : first ≠ second) (firstNoSelf : chain.P first first = 0)
    (secondNoSelf : chain.P second second = 0)
    (escapeProbability : ℝ) (escapePositive : 0 < escapeProbability)
    (escapeAtMostOne : escapeProbability ≤ 1)
    (escape : chain.P first second ≤ 1 - escapeProbability) :
    ∀ time source, partialHit chain ({first, second} : Finset Vertex)ᶜ time source ≤
      2 / escapeProbability := by
  have quotientAtLeastTwo : (2 : ℝ) ≤ 2 / escapeProbability :=
    (le_div_iff₀ escapePositive).mpr (by nlinarith)
  have firstValueNonnegative : 0 ≤ 2 / escapeProbability - 1 := by linarith
  have quotientPositive : 0 < (2 : ℝ) / escapeProbability := div_pos (by norm_num) escapePositive
  have cancellation : escapeProbability * (2 / escapeProbability) = 2 := by
    field_simp [escapePositive.ne']
  let value : Vertex → ℝ := fun source =>
    (if source = first then 2 / escapeProbability - 1 else 0) +
      (if source = second then 2 / escapeProbability else 0)
  have valueNonnegative : ∀ source, 0 ≤ value source := by
    intro source
    exact add_nonneg (by split <;> first | exact firstValueNonnegative | exact le_rfl)
      (by split <;> first | exact quotientPositive.le | exact le_rfl)
  have sumIdentity (source : Vertex) :
      ∑ target, chain.P source target * value target =
        chain.P source first * (2 / escapeProbability - 1) +
          chain.P source second * (2 / escapeProbability) := by
    simp [value, mul_add, mul_ite, Finset.sum_add_distrib]
  have supersolution : ∀ source ∉ ({first, second} : Finset Vertex)ᶜ,
      1 + ∑ target, chain.P source target * value target ≤ value source := by
    intro source outside
    have pairMembership : source ∈ ({first, second} : Finset Vertex) := by
      by_contra notInside
      exact outside (Finset.mem_compl.mpr notInside)
    have inside : source = first ∨ source = second := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using pairMembership
    rcases inside with equality | equality
    · subst source
      rw [sumIdentity, firstNoSelf]
      simp only [zero_mul, zero_add, value, if_pos rfl, if_true, if_neg distinct, add_zero]
      have multiplied := mul_le_mul_of_nonneg_right escape quotientPositive.le
      nlinarith
    · subst source
      rw [sumIdentity, secondNoSelf]
      simp only [zero_mul, add_zero, value, if_neg distinct.symm, if_pos rfl, if_true, zero_add]
      have multiplied := mul_le_mul_of_nonneg_right (chain.P_le_one second first) firstValueNonnegative
      linarith
  intro time source
  apply (partialHit_le_of_supersolution chain ({first, second} : Finset Vertex)ᶜ
    valueNonnegative supersolution time source).trans
  by_cases atFirst : source = first
  · subst source
    simp only [value, if_pos rfl, if_true, if_neg distinct, add_zero]
    linarith
  · by_cases atSecond : source = second
    · subst source
      simp only [value, if_neg distinct.symm, if_pos rfl, if_true, zero_add]
      exact le_rfl
    · simp only [value, if_neg atFirst, if_neg atSecond, zero_add]
      exact quotientPositive.le

theorem conductance_one_exterior_edge_escape
    (conductance : Vertex → Vertex → ℝ)
    (nonnegative : ∀ source target, 0 ≤ conductance source target)
    (rowPositive : ∀ source, 0 < ∑ target, conductance source target)
    (source other exterior : Vertex) (exteriorDistinct : exterior ≠ other)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (internalUpper : conductance source other ≤ upper)
    (exteriorLower : lower ≤ conductance source exterior) :
    (condChain conductance nonnegative rowPositive).P source other ≤
      1 - lower / (upper + lower) := by
  have pairBound : conductance source other + conductance source exterior ≤
      ∑ target, conductance source target := by
    have bound := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({other, exterior} : Finset Vertex))
      (fun target _ _ => nonnegative source target)
    simpa only [Finset.sum_pair exteriorDistinct.symm] using bound
  have rowBound : conductance source other + lower ≤ ∑ target, conductance source target := by
    linarith
  have denominatorPositive : 0 < upper + lower := add_pos upperPositive lowerPositive
  have ratioIdentity : 1 - lower / (upper + lower) = upper / (upper + lower) := by
    field_simp [denominatorPositive.ne']
    <;> ring
  rw [ratioIdentity]
  change conductance source other / (∑ target, conductance source target) ≤ upper / (upper + lower)
  apply (div_le_div_iff₀ (rowPositive source) denominatorPositive).mpr
  have firstProduct := mul_le_mul_of_nonneg_left rowBound upperPositive.le
  have secondProduct := mul_le_mul_of_nonneg_left internalUpper lowerPositive.le
  nlinarith

end
end IGS.Sec31

#print axioms IGS.Sec31.two_vertex_partialHit_le
#print axioms IGS.Sec31.conductance_one_exterior_edge_escape
