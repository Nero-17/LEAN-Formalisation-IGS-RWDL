import RequestProject.Section31.EIGSUnitProjectionScale
import Mathlib.Algebra.Order.Field.GeomSum

/-! Native finite-level projection tails, obtained by summing the actual
adjacent energy projection increments. No L² orthogonality is asserted. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem xiFiniteSpeedL2_sub (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (first second : XiVtx system level → ℝ) :
    xiFiniteSpeedL2 system mass level (first - second) =
      xiFiniteSpeedL2 system mass level first - xiFiniteSpeedL2 system mass level second :=
  MeasureTheory.MemLp.toLp_sub (MeasureTheory.MemLp.of_discrete) (MeasureTheory.MemLp.of_discrete)

theorem exists_xiUnitProjection_native_tail (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (scaleGreaterOne : 1 < mass.rate * resistanceRate)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ coarseLevel fineLevel
      (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ),
      ‖xiFiniteSpeedL2 system mass fineLevel values -
        xiFiniteSpeedL2 system mass fineLevel
          (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values)‖ ≤
      constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
        Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) := by
  classical
  obtain ⟨constant, constantPositive, incrementBound⟩ := exists_xiUnitProjectionIncrement_scaled_bound
    system rulesConnected distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive
  have scalePositive := mul_pos mass.rate_positive ratePositive
  have sqrtGreaterOne : 1 < Real.sqrt (mass.rate * resistanceRate) := by
    nlinarith [Real.sq_sqrt scalePositive.le, Real.sqrt_nonneg (mass.rate * resistanceRate)]
  have decayPositive : 0 < (Real.sqrt (mass.rate * resistanceRate))⁻¹ := inv_pos.2 (by linarith)
  have decayLessOne : (Real.sqrt (mass.rate * resistanceRate))⁻¹ < 1 := by
    exact (inv_lt_one₀ (by linarith)).2 sqrtGreaterOne
  refine ⟨Real.sqrt constant / (1 - (Real.sqrt (mass.rate * resistanceRate))⁻¹),
    div_pos (Real.sqrt_pos.2 constantPositive) (sub_pos.2 decayLessOne), ?_⟩
  intro coarseLevel fineLevel levelsOrdered values
  have energyNonnegative : 0 ≤ xiScaledUnitEnergy system resistanceRate normalization fineLevel values :=
    mul_nonneg (mul_pos normalizationPositive (pow_pos ratePositive _)).le
      (((XiNetwork system fineLevel).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy_nonneg values)
  let projections : ℕ → MeasureTheory.Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel) :=
    fun level => if ordered : level ≤ fineLevel then
      xiFiniteSpeedL2 system mass fineLevel (xiUnitEnergyProjection system rulesConnected level fineLevel ordered values)
    else xiFiniteSpeedL2 system mass fineLevel values
  have projectionAtEnd : projections fineLevel = xiFiniteSpeedL2 system mass fineLevel values := by
    simp only [projections, dif_pos le_rfl, xiUnitEnergyProjection_refl]
  have projectionAtStart : projections coarseLevel = xiFiniteSpeedL2 system mass fineLevel
      (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values) := by
    simp only [projections, dif_pos levelsOrdered]
  have adjacentBound : ∀ level, level < fineLevel →
      dist (projections level) (projections (level + 1)) ≤
        Real.sqrt constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ level *
          Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) := by
    intro level levelLess
    have levelOrdered : level ≤ fineLevel := levelLess.le
    have nextOrdered : level + 1 ≤ fineLevel := levelLess
    simp only [projections, dif_pos levelOrdered, dif_pos nextOrdered]
    rw [dist_comm, dist_eq_norm, ← xiFiniteSpeedL2_sub]
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le nextOrdered
    have squareBound := incrementBound level offset values
    have powerIdentity : ((Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ (level + 1)) ^ 2 =
        1 / (mass.rate * resistanceRate) ^ (level + 1) := by
      rw [← pow_mul, Nat.mul_comm (level + 1) 2, pow_mul]
      simp only [inv_pow, Real.sq_sqrt scalePositive.le, one_div]
    have normBound :
        ‖xiFiniteSpeedL2 system mass (level + 1 + offset)
          (xiUnitProjectionIncrement system rulesConnected level offset values)‖ ≤
        Real.sqrt constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ (level + 1) *
          Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization (level + 1 + offset) values) := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      calc
        _ ≤ _ := squareBound
        _ = _ := by
          simp only [mul_pow, Real.sq_sqrt constantPositive.le,
            Real.sq_sqrt energyNonnegative, powerIdentity]
          ring
    have powerStep : (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ (level + 1) ≤
        (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ level := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg decayPositive.le level) decayLessOne.le
    exact normBound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left powerStep (Real.sqrt_nonneg constant)) (Real.sqrt_nonneg _))
  have telescope := dist_le_Ico_sum_of_dist_le (f := projections) levelsOrdered
    (fun {_} _ upper => adjacentBound _ upper)
  rw [projectionAtStart, projectionAtEnd, dist_comm, dist_eq_norm] at telescope
  have seriesBound := geom_sum_Ico_le_of_lt_one (m := coarseLevel) (n := fineLevel) decayPositive.le decayLessOne
  calc
    _ ≤ _ := telescope
    _ = Real.sqrt constant * (∑ level ∈ Finset.Ico coarseLevel fineLevel,
        (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ level) *
          Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ Real.sqrt constant *
        ((Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel /
          (1 - (Real.sqrt (mass.rate * resistanceRate))⁻¹)) *
          Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left seriesBound (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end EIGS
