import RequestProject.Section31.J1FiniteJumpFunctions
import RequestProject.Section31.J1UnitGridReconstruction

/-! Deterministic fixed-grid approximation of finitely jumping paths in
the genuine time-change J1 distance. Endpoint jumps are retained exactly. -/

namespace IGS.Sec31.DiscreteMarkov
open Filter Set Topology MeasureTheory
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000

def unitGridPoint (grid : ℕ) (index : Fin (grid + 2)) : UnitJ1Time :=
  ⟨(index.val : ℝ) / (grid + 1 : ℝ), by
    have denominator : 0 < (grid + 1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) denominator.le
    · apply (div_le_one denominator).mpr
      exact_mod_cast Nat.le_of_lt_succ index.isLt⟩

def unitGridFunctionReconstruction {State : Type*} (grid : ℕ)
    (values : Fin (grid + 2) → State) (time : UnitJ1Time) : State := values (unitGridIndex grid time)

theorem unitGridMesh_tendsto :
    Tendsto (fun grid : ℕ => 1 / (grid + 1 : ℝ)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat

variable {Space : Type*} [MetricSpace Space]

def roundedIntervalKnot (grid : ℕ) (time : UnitJ1Time) :
    UnitJ1Time :=
  ⟨(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ), by
    have positive : 0 < (grid+1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) positive.le
    · apply (div_le_one positive).mpr
      have bound : ⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ ≤ grid+1 := Nat.ceil_le.mpr (by
        simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
          mul_le_mul_of_nonneg_left time.property.2 positive.le)
      exact_mod_cast bound⟩

theorem roundedIntervalKnot_distance (grid : ℕ)
    (time : UnitJ1Time) :
    dist (roundedIntervalKnot grid time) time ≤ 1 / (grid+1 : ℝ) := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  have lower := Nat.le_ceil ((grid+1 : ℝ) * (time : ℝ))
  have upper := Nat.ceil_lt_add_one (mul_nonneg positive.le time.property.1)
  change |(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) - (time : ℝ)| ≤ _
  have quotientLower : (time : ℝ) ≤ (⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) :=
    (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using lower)
  rw [abs_of_nonneg (sub_nonneg.mpr quotientLower)]
  apply (le_div_iff₀ positive).mpr
  rw [sub_mul, div_mul_cancel₀ _ positive.ne']
  nlinarith

theorem roundedIntervalKnot_tendsto
    (time : UnitJ1Time) :
    Tendsto (fun grid => roundedIntervalKnot grid time) atTop (𝓝 time) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [unitGridMesh_tendsto.eventually (gt_mem_nhds positive)] with grid small
  exact (roundedIntervalKnot_distance grid time).trans_lt small

theorem roundedIntervalKnot_grid_inequality (grid : ℕ)
    (knot time : UnitJ1Time) :
    knot ≤ unitGridPoint grid (unitGridIndex grid time) ↔
      roundedIntervalKnot grid knot ≤ time := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  change (knot : ℝ) ≤ (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ↔
    (⌈(grid+1 : ℝ) * (knot : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
  rw [le_div_iff₀ positive, div_le_iff₀ positive]
  rw [mul_comm (knot : ℝ), ← Nat.ceil_le,
    mul_comm (time : ℝ), ← Nat.le_floor_iff (mul_nonneg positive.le time.property.1)]

theorem finiteEndpointJump_grid_identity {count : ℕ}
    (knots : Fin count → UnitJ1Time)
    (states : Fin (count+1) → Space) (endpoint : Space) (grid : ℕ) :
    unitGridFunctionReconstruction grid
      (fun index => finiteEndpointJumpFunction knots states endpoint
        (unitGridPoint grid index)) =
      finiteEndpointJumpFunction (fun index => roundedIntervalKnot grid (knots index)) states endpoint := by
  classical
  funext time
  by_cases terminal : time.val = 1
  · have gridTerminal : (unitGridPoint grid
        (unitGridIndex grid time)).val = 1 := by
      change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) = 1
      rw [terminal, mul_one]
      have floorIdentity : ⌊(grid+1 : ℝ)⌋₊ = grid+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (grid+1)
      rw [floorIdentity]
      push_cast
      exact div_self (by positivity)
    simp only [unitGridFunctionReconstruction,
      finiteEndpointJumpFunction, terminal, gridTerminal, if_true]
  · have gridNotTerminal : (unitGridPoint grid
        (unitGridIndex grid time)).val ≠ 1 := by
      have bound := Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (grid+1 : ℝ)) time.property.1)
      have quotientBound : (unitGridPoint grid
          (unitGridIndex grid time)).val ≤ time.val := by
        change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
        apply (div_le_iff₀ (by positivity : 0 < (grid+1 : ℝ))).mpr
        simpa only [mul_comm] using bound
      exact ne_of_lt (quotientBound.trans_lt (lt_of_le_of_ne time.property.2 terminal))
    simp only [unitGridFunctionReconstruction,
      finiteEndpointJumpFunction, terminal, gridNotTerminal, if_false]
    change states _ = states _
    congr 1
    apply Fin.ext
    unfold finiteJumpCount
    change (Finset.univ.filter (fun index => knots index ≤ unitGridPoint grid
      (unitGridIndex grid time))).card =
        (Finset.univ.filter (fun index => roundedIntervalKnot grid (knots index) ≤ time)).card
    apply congrArg Finset.card
    apply Finset.ext
    intro index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact roundedIntervalKnot_grid_inequality grid (knots index) time

theorem finiteEndpointJump_grid_j1_approximation [BoundedSpace Space] {count : ℕ}
    (knots : Fin count → UnitJ1Time) (increasing : StrictMono knots)
    (interior : ∀ index, 0 < (knots index).val ∧ (knots index).val < 1)
    (states : Fin (count + 1) → Space) (endpoint : Space) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ grid : ℕ in atTop,
      skorokhodJ1Distance (finiteEndpointJumpFunction knots states endpoint)
        (unitGridFunctionReconstruction grid (fun index => finiteEndpointJumpFunction knots states endpoint
          (unitGridPoint grid index))) < tolerance := by
  have increasingEventually : ∀ᶠ grid : ℕ in atTop,
      StrictMono (fun index => roundedIntervalKnot grid (knots index)) := by
    have pairs : ∀ first second : Fin count, ∀ᶠ grid : ℕ in atTop,
        first < second → roundedIntervalKnot grid (knots first) < roundedIntervalKnot grid (knots second) := by
      intro first second
      by_cases before : first < second
      · exact ((roundedIntervalKnot_tendsto (knots first)).eventually_lt
          (roundedIntervalKnot_tendsto (knots second)) (increasing before)).mono (fun _ bound _ => bound)
      · exact Eventually.of_forall (fun _ impossible => (before impossible).elim)
    exact (Filter.eventually_all.mpr (fun first => Filter.eventually_all.mpr (pairs first))).mono
      (fun _ pairBound => pairBound)
  have interiorEventually : ∀ᶠ grid : ℕ in atTop, ∀ index,
      0 < (roundedIntervalKnot grid (knots index)).val ∧
        (roundedIntervalKnot grid (knots index)).val < 1 := by
    apply Filter.eventually_all.mpr
    intro index
    have convergence := continuous_subtype_val.tendsto (knots index) |>.comp (roundedIntervalKnot_tendsto (knots index))
    exact convergence.eventually (Ioo_mem_nhds (interior index).1 (interior index).2)
  have factorNonnegative : 0 ≤ (2 : ℝ) ^ count - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have errorConvergence : Tendsto (fun grid : ℕ => ((2 : ℝ) ^ count - 1) * (1 / (grid + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using unitGridMesh_tendsto.const_mul ((2 : ℝ) ^ count - 1)
  intro tolerance positive
  filter_upwards [increasingEventually, interiorEventually, errorConvergence.eventually (gt_mem_nhds positive)]
    with grid roundedIncreasing roundedInterior errorSmall
  obtain ⟨change, knotIdentity, displacement⟩ := interval_finite_knots_orderIso count knots
    (fun index => roundedIntervalKnot grid (knots index)) increasing roundedIncreasing interior roundedInterior
    (1 / (grid + 1 : ℝ)) (fun index => by simpa only [dist_comm] using roundedIntervalKnot_distance grid (knots index))
  rw [finiteEndpointJump_grid_identity]
  exact (finiteEndpointJumpFunction_J1_le_clock_error knots _ states endpoint change knotIdentity
    (((2 : ℝ) ^ count - 1) * (1 / (grid + 1 : ℝ)))
    (mul_nonneg factorNonnegative (by positivity)) displacement).trans_lt errorSmall

theorem unitGridJ1Reconstruction_tendsto_of_finite_jumps [BoundedSpace Space]
    (path : UnitCadlagJ1Path Space)
    (finite : ∃ count : ℕ, ∃ knots : Fin count → UnitJ1Time,
      StrictMono knots ∧ (∀ index, 0 < (knots index).val ∧ (knots index).val < 1) ∧
        ∃ states : Fin (count + 1) → Space, ∃ endpoint : Space,
          path.val.toFun = finiteEndpointJumpFunction knots states endpoint) :
    Tendsto (fun grid => unitGridJ1Reconstruction grid (fun index => path.val.toFun (unitGridPoint grid index)))
      atTop (𝓝 path) := by
  obtain ⟨count, knots, increasing, interior, states, endpoint, representation⟩ := finite
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [finiteEndpointJump_grid_j1_approximation knots increasing interior states endpoint tolerance positive]
    with grid close
  change skorokhodJ1Distance
    (unitGridFunctionReconstruction grid (fun index => path.val.toFun (unitGridPoint grid index))) path.val.toFun < tolerance
  rw [skorokhodJ1Distance_comm, representation]
  exact close

theorem unitCadlagJ1Sample_aemeasurable_of_finite_jumps
    [BoundedSpace Space] [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {Outcome : Type*} [MeasurableSpace Outcome] (law : Measure Outcome)
    (sample : Outcome → UnitCadlagJ1Path Space)
    (evaluations : ∀ time, AEMeasurable (fun outcome => (sample outcome).val.toFun time) law)
    (finite : ∀ᵐ outcome ∂law, ∃ count : ℕ, ∃ knots : Fin count → UnitJ1Time,
      StrictMono knots ∧ (∀ index, 0 < (knots index).val ∧ (knots index).val < 1) ∧
        ∃ states : Fin (count + 1) → Space, ∃ endpoint : Space,
          (sample outcome).val.toFun = finiteEndpointJumpFunction knots states endpoint) :
    AEMeasurable sample law := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (f := fun grid outcome => unitGridJ1Reconstruction grid
      (fun index => (sample outcome).val.toFun (unitGridPoint grid index)))
  · intro grid
    exact (unitGridJ1Reconstruction_measurable grid).comp_aemeasurable
      (aemeasurable_pi_lambda _ (fun index => evaluations (unitGridPoint grid index)))
  · exact finite.mono (fun outcome regular => unitGridJ1Reconstruction_tendsto_of_finite_jumps (sample outcome) regular)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointJump_grid_identity
#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointJump_grid_j1_approximation
#print axioms IGS.Sec31.DiscreteMarkov.unitGridJ1Reconstruction_tendsto_of_finite_jumps
#print axioms IGS.Sec31.DiscreteMarkov.unitCadlagJ1Sample_aemeasurable_of_finite_jumps


