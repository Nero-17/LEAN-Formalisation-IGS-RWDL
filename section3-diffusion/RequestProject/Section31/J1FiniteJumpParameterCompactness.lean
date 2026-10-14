import RequestProject.Section31.J1FiniteJumpCadlag

/-! Compact finite-jump parameter families for the genuine J1 carrier.
Jump times stay a positive distance from each other and both endpoints.
This proves compact capture sets directly, without a Polish assertion for D. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set
open scoped Topology NNReal
set_option maxHeartbeats 4000000

abbrev InteriorOrderedKnots (count : ℕ) :=
  {knots : Fin count → UnitJ1Time // StrictMono knots ∧
    ∀ index, 0 < (knots index).val ∧ (knots index).val < 1}

theorem finiteEndpointCadlagJ1Path_knots_lipschitz
    {State : Type*} [MetricSpace State] [BoundedSpace State] (count : ℕ)
    (states : Fin (count + 1) → State) (endpoint : State) :
    LipschitzWith ⟨(2 : ℝ) ^ count - 1, by
      have bound : (1 : ℝ) ≤ 2 ^ count := one_le_pow₀ (by norm_num)
      linarith⟩
      (fun knots : InteriorOrderedKnots count => finiteEndpointCadlagJ1Path knots.val states endpoint) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  obtain ⟨change, aligned, clockBound⟩ := interval_finite_knots_orderIso count first.val second.val
    first.property.1 second.property.1 first.property.2 second.property.2 (dist first second)
      (fun index => dist_le_pi_dist first.val second.val index)
  change skorokhodJ1Distance (finiteEndpointJumpFunction first.val states endpoint)
    (finiteEndpointJumpFunction second.val states endpoint) ≤
      ((2 : ℝ) ^ count - 1) * dist first second
  exact finiteEndpointJumpFunction_J1_le_clock_error first.val second.val states endpoint change aligned
    _ (mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) dist_nonneg) clockBound

def separatedJumpKnots (count : ℕ) (gap : ℝ) : Set (Fin count → UnitJ1Time) :=
  {knots | (∀ index, gap ≤ (knots index).val ∧ (knots index).val ≤ 1 - gap) ∧
    ∀ first second, first < second → gap ≤ (knots second).val - (knots first).val}

theorem separatedJumpKnots_isClosed (count : ℕ) (gap : ℝ) :
    IsClosed (separatedJumpKnots count gap) := by
  have coordinateContinuous (index : Fin count) :
      Continuous (fun knots : Fin count → UnitJ1Time => (knots index).val) :=
    continuous_subtype_val.comp (continuous_apply index)
  unfold separatedJumpKnots
  simp only [setOf_and, setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro index
    exact (isClosed_le continuous_const (coordinateContinuous index)).inter
      (isClosed_le (coordinateContinuous index) continuous_const)
  · apply isClosed_iInter
    intro first
    apply isClosed_iInter
    intro second
    apply isClosed_iInter
    intro ordered
    exact isClosed_le continuous_const ((coordinateContinuous second).sub (coordinateContinuous first))

theorem separatedJumpKnots_isCompact (count : ℕ) (gap : ℝ) :
    IsCompact (separatedJumpKnots count gap) :=
  (separatedJumpKnots_isClosed count gap).isCompact

def separatedJumpKnots_toInterior (count : ℕ) (gap : ℝ) (gapPositive : 0 < gap)
    (knots : separatedJumpKnots count gap) : InteriorOrderedKnots count := by
  refine ⟨knots.val, ?_, ?_⟩
  · intro first second ordered
    have separated := knots.property.2 first second ordered
    change (knots.val first).val < (knots.val second).val
    linarith
  · intro index
    have bounded := knots.property.1 index
    constructor <;> linarith

theorem finiteEndpointCadlagJ1Path_separated_range_isCompact
    {State : Type*} [MetricSpace State] [BoundedSpace State] (count : ℕ)
    (states : Fin (count + 1) → State) (endpoint : State)
    (gap : ℝ) (gapPositive : 0 < gap) :
    IsCompact (Set.range (fun knots : separatedJumpKnots count gap =>
      finiteEndpointCadlagJ1Path knots.val states endpoint)) := by
  letI : CompactSpace (separatedJumpKnots count gap) :=
    isCompact_iff_compactSpace.mp (separatedJumpKnots_isCompact count gap)
  have interiorContinuous : Continuous (separatedJumpKnots_toInterior count gap gapPositive) :=
    continuous_subtype_val.subtype_mk _
  have pathContinuous := (finiteEndpointCadlagJ1Path_knots_lipschitz count states endpoint).continuous.comp
    interiorContinuous
  exact isCompact_range pathContinuous

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointCadlagJ1Path_knots_lipschitz
#print axioms IGS.Sec31.DiscreteMarkov.separatedJumpKnots_isCompact
#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointCadlagJ1Path_separated_range_isCompact
