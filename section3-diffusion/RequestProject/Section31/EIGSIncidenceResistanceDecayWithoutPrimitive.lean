import RequestProject.Section2DegreeResistanceGap
import RequestProject.Section31.EIGSSpeedWeakConvergence

/-! Strict finite subinvariance, rather than a primitive degree matrix, gives
the actual incidence-resistance decay at every fixed-birth vertex. -/

namespace EIGS

open Filter Topology
open scoped BigOperators Classical

variable {K : ℕ}

theorem degreeMatrix_reciprocal_resistance_strict (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    ∀ row : Fin K ⊕ Fin K,
      resistanceRate⁻¹ * Sum.elim (fun colour => (resistanceVector colour)⁻¹)
          (fun colour => (resistanceVector colour)⁻¹) row <
        (degreeMatrix system).mulVec (Sum.elim (fun colour => (resistanceVector colour)⁻¹)
          (fun colour => (resistanceVector colour)⁻¹)) row := by
  have plusStrict : ∀ colour,
      (((system.ruleFamily rulesConnected).Psi resistanceVector) colour)⁻¹ <
        ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantPlus colour then (resistanceVector ((system.rule colour).col edge))⁻¹ else 0) +
           (if (system.rule colour).head edge = system.plantPlus colour then (resistanceVector ((system.rule colour).col edge))⁻¹ else 0)) := by
    intro colour
    obtain ⟨potential, _, _, minimal, energy⟩ :=
      (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes
        resistanceVector vectorPositive (rulesConnected colour) _ _ (system.plant_ne colour)
    have strict := (system.ruleNetwork colour).minimum_energy_lt_incident_conductance
      resistanceVector vectorPositive (rulesConnected colour) _ _ (system.plant_ne colour)
      (plantingNonadjacent colour) potential minimal
    rw [energy] at strict
    exact strict
  have minusStrict : ∀ colour,
      (((system.ruleFamily rulesConnected).Psi resistanceVector) colour)⁻¹ <
        ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantMinus colour then (resistanceVector ((system.rule colour).col edge))⁻¹ else 0) +
           (if (system.rule colour).head edge = system.plantMinus colour then (resistanceVector ((system.rule colour).col edge))⁻¹ else 0)) := by
    intro colour
    obtain ⟨potential, _, _, minimal, energy⟩ :=
      (system.ruleNetwork colour).exists_minimum_potential_energy_terminal_values
        resistanceVector vectorPositive (rulesConnected colour) _ _ (system.plant_ne colour) 0 1
    have strict := (system.ruleNetwork colour).minimum_energy_lt_incident_conductance
      resistanceVector vectorPositive (rulesConnected colour) _ _ (system.plant_ne colour).symm
      (fun adjacency => plantingNonadjacent colour adjacency.symm) potential
      (fun competitor sourceValue sinkValue => minimal competitor sinkValue sourceValue)
    rw [energy] at strict
    simpa only [zero_sub, neg_one_sq, one_mul] using strict
  intro row
  rw [degreeMatrix_mulVec_duplicate]
  cases row with
  | inl colour =>
    have bound := plusStrict colour
    rw [eigenpair colour] at bound
    simpa only [Sum.elim_inl, mul_inv_rev, mul_comm] using bound
  | inr colour =>
    have bound := minusStrict colour
    rw [eigenpair colour] at bound
    simpa only [Sum.elim_inr, mul_inv_rev, mul_comm] using bound

theorem exists_uniform_subinvariant_rate {index : Type*} [Fintype index] [Nonempty index]
    (matrix : Matrix index index ℝ) (weights : index → ℝ)
    (weightsPositive : ∀ row, 0 < weights row) (rate : ℝ)
    (strict : ∀ row, rate * weights row < matrix.mulVec weights row) :
    ∃ growth : ℝ, rate < growth ∧ ∀ row, growth * weights row ≤ matrix.mulVec weights row := by
  obtain ⟨minimumRow, _, minimumRatio⟩ := Finset.univ.exists_min_image
    (fun row => matrix.mulVec weights row / weights row) Finset.univ_nonempty
  refine ⟨matrix.mulVec weights minimumRow / weights minimumRow,
    (lt_div_iff₀ (weightsPositive minimumRow)).mpr (strict minimumRow), ?_⟩
  intro row
  exact (le_div_iff₀ (weightsPositive row)).mp (minimumRatio row (Finset.mem_univ _))

theorem vecMul_recursion_subinvariant_lower {index : Type*} [Fintype index] [Nonempty index]
    (matrix : Matrix index index ℝ) (sequence : ℕ → index → ℝ) (weights : index → ℝ)
    (weightsPositive : ∀ row, 0 < weights row)
    (sequenceNonnegative : ∀ age row, 0 ≤ sequence age row)
    (initialPositive : 0 < ∑ row, sequence 0 row * weights row)
    (recursion : ∀ age, sequence (age + 1) = Matrix.vecMul (sequence age) matrix)
    (growth : ℝ) (growthPositive : 0 < growth)
    (subinvariant : ∀ row, growth * weights row ≤ matrix.mulVec weights row) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ age, lower * growth ^ age ≤ ∑ row, sequence age row := by
  have weightedGrowth : ∀ age,
      (∑ row, sequence 0 row * weights row) * growth ^ age ≤ ∑ row, sequence age row * weights row := by
    intro age
    induction age with
    | zero => simp
    | succ age induction =>
      have stepBound : growth * (∑ row, sequence age row * weights row) ≤
          ∑ row, sequence (age + 1) row * weights row := by
        rw [recursion]
        calc
          growth * (∑ row, sequence age row * weights row) =
              ∑ row, sequence age row * (growth * weights row) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro row _
            ring
          _ ≤ ∑ row, sequence age row * matrix.mulVec weights row :=
            Finset.sum_le_sum (fun row _ => mul_le_mul_of_nonneg_left (subinvariant row) (sequenceNonnegative age row))
          _ = ∑ column, Matrix.vecMul (sequence age) matrix column * weights column := by
            simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro column _
            apply Finset.sum_congr rfl
            intro row _
            ring
      have multiplied := mul_le_mul_of_nonneg_left induction growthPositive.le
      have bound := multiplied.trans stepBound
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using bound
  have weightsTotalPositive : 0 < ∑ row, weights row :=
    Finset.sum_pos (fun row _ => weightsPositive row) Finset.univ_nonempty
  have weightsBound : ∀ row, weights row ≤ ∑ column, weights column :=
    fun row => Finset.single_le_sum (fun column _ => (weightsPositive column).le) (Finset.mem_univ row)
  refine ⟨(∑ row, sequence 0 row * weights row) / (∑ row, weights row),
    div_pos initialPositive weightsTotalPositive, ?_⟩
  intro age
  have weightedBound : (∑ row, sequence age row * weights row) ≤
      (∑ row, sequence age row) * (∑ row, weights row) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun row _ => mul_le_mul_of_nonneg_left (weightsBound row) (sequenceNonnegative age row))
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ weightsTotalPositive).mpr ((weightedGrowth age).trans weightedBound)

theorem xiVertexIncidenceCount_eq_degree_state_sum (system : EIGSData K)
    (level : ℕ) (vertex : XiVtx system level) :
    (xiVertexIncidenceCount system level vertex : ℝ) = ∑ state, degVec system level vertex state := by
  have outSum : (∑ colour, (outDeg system level vertex colour : ℝ)) =
      ∑ edge, if XiTail system level edge = vertex then (1 : ℝ) else 0 := by
    simp only [outDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases incident : XiTail system level edge = vertex <;> simp [incident]
  have inSum : (∑ colour, (inDeg system level vertex colour : ℝ)) =
      ∑ edge, if XiHead system level edge = vertex then (1 : ℝ) else 0 := by
    simp only [inDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases incident : XiHead system level edge = vertex <;> simp [incident]
  rw [Fintype.sum_sum_type]
  change (xiVertexIncidenceCount system level vertex : ℝ) =
    (∑ colour, (outDeg system level vertex colour : ℝ)) + ∑ colour, (inDeg system level vertex colour : ℝ)
  rw [outSum, inSum]
  simp only [xiVertexIncidenceCount, Nat.cast_add, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem xiIncidence_resistance_inverse_tendsto_zero_without_primitive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (birth : ℕ) (vertex : XiVtx system birth) :
    Tendsto (fun age : ℕ =>
      1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
        resistanceRate ^ (birth + age))) atTop (nhds 0) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have weightsPositive : ∀ row : Fin K ⊕ Fin K,
      0 < Sum.elim (fun colour => (resistanceVector colour)⁻¹) (fun colour => (resistanceVector colour)⁻¹) row := by
    intro row
    cases row <;> exact inv_pos.mpr (vectorPositive _)
  obtain ⟨growth, growthGreater, subinvariant⟩ := exists_uniform_subinvariant_rate
    (degreeMatrix system)
    (Sum.elim (fun colour => (resistanceVector colour)⁻¹) (fun colour => (resistanceVector colour)⁻¹))
    weightsPositive resistanceRate⁻¹
    (degreeMatrix_reciprocal_resistance_strict system rulesConnected plantingNonadjacent resistanceRate resistanceVector vectorPositive eigenpair)
  have growthPositive : 0 < growth := (inv_pos.mpr ratePositive).trans growthGreater
  have productGap : 1 < growth * resistanceRate := by
    have multiplied := mul_lt_mul_of_pos_right growthGreater ratePositive
    simpa only [inv_mul_cancel₀ ratePositive.ne'] using multiplied
  obtain ⟨lower, lowerPositive, growthBound⟩ := vecMul_recursion_subinvariant_lower
    (degreeMatrix system) (fun age => degVec system (birth + age) (xiForward system birth age vertex))
    (Sum.elim (fun colour => (resistanceVector colour)⁻¹) (fun colour => (resistanceVector colour)⁻¹))
    weightsPositive (by intro age row; cases row <;> exact Nat.cast_nonneg _)
    (by simpa only [Nat.add_zero, xiForward] using degVec_weighted_positive system rulesConnected birth vertex _ weightsPositive)
    (fun age => degVec_xiForward_succ system birth age vertex) growth growthPositive subinvariant
  have lowerBound : ∀ age : ℕ,
      lower * resistanceRate ^ birth * (growth * resistanceRate) ^ age ≤
        (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
          resistanceRate ^ (birth + age) := by
    intro age
    have degreeBound := growthBound age
    rw [← xiVertexIncidenceCount_eq_degree_state_sum] at degreeBound
    have multiplied := mul_le_mul_of_nonneg_right degreeBound (pow_pos ratePositive (birth + age)).le
    convert multiplied using 1 <;> rw [pow_add, mul_pow] <;> ring
  have inverseBound : ∀ age : ℕ,
      1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
          resistanceRate ^ (birth + age)) ≤
        (lower * resistanceRate ^ birth)⁻¹ * (growth * resistanceRate)⁻¹ ^ age := by
    intro age
    have comparison := one_div_le_one_div_of_le
      (mul_pos (mul_pos lowerPositive (pow_pos ratePositive birth)) (pow_pos (mul_pos growthPositive ratePositive) age))
      (lowerBound age)
    simpa only [one_div, mul_inv_rev, mul_pow, inv_pow, mul_comm, mul_left_comm, mul_assoc] using comparison
  have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_pos.2 (mul_pos growthPositive ratePositive)).le
    ((inv_lt_one₀ (mul_pos growthPositive ratePositive)).2 productGap)
  have upperConvergence := geometric.const_mul (lower * resistanceRate ^ birth)⁻¹
  apply squeeze_zero (fun age => by positivity) inverseBound
  simpa only [mul_zero] using upperConvergence

end EIGS

#print axioms EIGS.degreeMatrix_reciprocal_resistance_strict
#print axioms EIGS.exists_uniform_subinvariant_rate
#print axioms EIGS.vecMul_recursion_subinvariant_lower
#print axioms EIGS.xiVertexIncidenceCount_eq_degree_state_sum
#print axioms EIGS.xiIncidence_resistance_inverse_tendsto_zero_without_primitive
