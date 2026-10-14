import RequestProject.Section31.FiniteMarkovVectorRange
import Mathlib.Data.Finite.Card
import Mathlib.Analysis.SpecificLimits.Basic

/-! A finite family of geometric degree ladders may overlap. At any
occupied value there is at most one level per type, and all colliding
levels differ by a uniform finite offset. No disjointness is assumed.
Candidate source. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem geometric_ladder_level_injective (coefficient rate : ℝ)
    (coefficientPositive : 0 < coefficient) (rateGreaterThanOne : 1 < rate) :
    Function.Injective (fun level : ℕ => coefficient / rate ^ level) := by
  intro first second equality
  have cross := (div_eq_div_iff (pow_ne_zero first (zero_lt_one.trans rateGreaterThanOne).ne')
    (pow_ne_zero second (zero_lt_one.trans rateGreaterThanOne).ne')).1 equality
  have powers : rate ^ second = rate ^ first := mul_left_cancel₀ coefficientPositive.ne' cross
  exact ((pow_right_strictMono₀ rateGreaterThanOne).injective powers).symm

theorem finite_geometric_ladder_fiber_bound {Kind : Type*} [Fintype Kind]
    (coefficients : Kind → ℝ) (coefficientsPositive : ∀ kind, 0 < coefficients kind)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) (value : ℝ) :
    Finite {code : Kind × ℕ // coefficients code.1 / rate ^ code.2 = value} ∧
      Nat.card {code : Kind × ℕ // coefficients code.1 / rate ^ code.2 = value} ≤ Fintype.card Kind := by
  let project : {code : Kind × ℕ // coefficients code.1 / rate ^ code.2 = value} → Kind :=
    fun code => code.val.1
  have injective : Function.Injective project := by
    rintro ⟨⟨kind, first⟩, firstValue⟩ ⟨⟨other, second⟩, secondValue⟩ sameKind
    change kind = other at sameKind
    subst other
    have sameLevel := geometric_ladder_level_injective (coefficients kind) rate
      (coefficientsPositive kind) rateGreaterThanOne (firstValue.trans secondValue.symm)
    exact Subtype.ext (Prod.ext rfl sameLevel)
  letI := Finite.of_injective project injective
  refine ⟨inferInstance, ?_⟩
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective project injective

theorem finite_geometric_ladder_collision_offsets {Kind : Type*} [Fintype Kind] [Nonempty Kind]
    (coefficients : Kind → ℝ) (coefficientsPositive : ∀ kind, 0 < coefficients kind)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) :
    ∃ offset : ℕ, ∀ firstKind secondKind firstLevel secondLevel,
      coefficients firstKind / rate ^ firstLevel = coefficients secondKind / rate ^ secondLevel →
        secondLevel ≤ firstLevel + offset ∧ firstLevel ≤ secondLevel + offset := by
  classical
  let ratios : Kind × Kind → ℝ := fun pair => coefficients pair.2 / coefficients pair.1
  obtain ⟨offset, offsetBound⟩ := ((tendsto_pow_atTop_atTop_of_one_lt rateGreaterThanOne).eventually
    (eventually_ge_atTop (finiteVectorMaximum ratios))).exists
  have oneDirection : ∀ firstKind secondKind firstLevel secondLevel,
      coefficients firstKind / rate ^ firstLevel = coefficients secondKind / rate ^ secondLevel →
        secondLevel ≤ firstLevel + offset := by
    intro firstKind secondKind firstLevel secondLevel equality
    have ratioBound : coefficients secondKind ≤ rate ^ offset * coefficients firstKind :=
      (div_le_iff₀ (coefficientsPositive firstKind)).1
        (((finiteVector_range_bounds ratios (firstKind, secondKind)).2).trans offsetBound)
    have cross := (div_eq_div_iff (pow_ne_zero firstLevel (zero_lt_one.trans rateGreaterThanOne).ne')
      (pow_ne_zero secondLevel (zero_lt_one.trans rateGreaterThanOne).ne')).1 equality
    have powerBound : rate ^ secondLevel ≤ rate ^ (firstLevel + offset) := by
      apply (mul_le_mul_iff_right₀ (coefficientsPositive firstKind)).mp
      calc
        coefficients firstKind * rate ^ secondLevel = coefficients secondKind * rate ^ firstLevel := cross
        _ ≤ (rate ^ offset * coefficients firstKind) * rate ^ firstLevel :=
          mul_le_mul_of_nonneg_right ratioBound (pow_pos (zero_lt_one.trans rateGreaterThanOne) _).le
        _ = coefficients firstKind * rate ^ (firstLevel + offset) := by rw [pow_add]; ring
    by_contra notBounded
    exact (not_lt_of_ge powerBound) (pow_lt_pow_right₀ rateGreaterThanOne (Nat.lt_of_not_ge notBounded))
  refine ⟨offset, ?_⟩
  intro firstKind secondKind firstLevel secondLevel equality
  exact ⟨oneDirection firstKind secondKind firstLevel secondLevel equality,
    oneDirection secondKind firstKind secondLevel firstLevel equality.symm⟩

end
end EIGS

#print axioms EIGS.geometric_ladder_level_injective
#print axioms EIGS.finite_geometric_ladder_fiber_bound
#print axioms EIGS.finite_geometric_ladder_collision_offsets
