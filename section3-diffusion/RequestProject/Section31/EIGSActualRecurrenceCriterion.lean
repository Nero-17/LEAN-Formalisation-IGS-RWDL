import RequestProject.Section31.EIGSOriginalEccentricityGrowth
import RequestProject.Section2StarResistance
import RequestProject.Section2GroundedResistanceBounds
import RequestProject.Section2MesoscopicResistance
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-! The recurrence criterion for the original simple graphs, using exactly
the fractional eccentricity balls in the manuscript. Resistance bounds and
eccentricity growth are derived from the original rules, never assumed as
final recurrence hypotheses. -/

namespace EIGS

open Filter Topology
open scoped Classical ENNReal
noncomputable section
variable {K : ℕ}

def xiFractionalEccentricityBallResistance (system : EIGSData K)
    (birth : ℕ) (center : XiVtx system birth) (fraction : ℝ) (age : ℕ) : ℝ :=
  effResToBoundary (XiSimpleGraph system (birth + age))
    (finiteGraphBall (XiSimpleGraph system (birth + age))
      (xiForward system birth age center)
      (fraction * finiteGraphEccentricity (XiSimpleGraph system (birth + age))
        (xiForward system birth age center))) (xiForward system birth age center)

theorem xi_liminf_ofReal_eq_top_iff_tendsto_atTop (sequence : ℕ → ℝ) :
    liminf (fun age => ENNReal.ofReal (sequence age)) atTop = ∞ ↔
      Tendsto sequence atTop atTop := by
  constructor
  · intro infiniteLowerLimit
    exact ENNReal.tendsto_ofReal_nhds_top.mp
      (tendsto_of_le_liminf_of_limsup_le infiniteLowerLimit.ge le_top)
  · intro divergence
    exact (ENNReal.tendsto_ofReal_nhds_top.mpr divergence).liminf_eq

def xiActualRecurrent (system : EIGSData K) : Prop :=
  ∀ birth (center : XiVtx system birth) fraction,
    0 < fraction → fraction < 1 →
      liminf (fun age => ENNReal.ofReal
        (xiFractionalEccentricityBallResistance system birth center fraction age)) atTop = ∞

theorem xiFractionalEccentricityBallResistance_trans (system : EIGSData K)
    (birth first second : ℕ) (center : XiVtx system birth) (fraction : ℝ) :
    xiFractionalEccentricityBallResistance system (birth + first)
        (xiForward system birth first center) fraction second =
      xiFractionalEccentricityBallResistance system birth center fraction (first + second) := by
  exact congrArg (fun point : Σ level, XiVtx system level =>
    effResToBoundary (XiSimpleGraph system point.1)
      (finiteGraphBall (XiSimpleGraph system point.1) point.2
        (fraction * finiteGraphEccentricity (XiSimpleGraph system point.1) point.2)) point.2)
    (xiForward_sigma_trans system birth first second center)

variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include connected loopless unique plantingNonadjacent distancePositive

theorem xiFractionalEccentricityBallResistance_tendsto_of_one_lt
    (resistanceGreaterThanOne : 1 < system.resistanceSpectralRadius connected distancePositive)
    (birth : ℕ) (center : XiVtx system birth) (fraction : ℝ)
    (fractionPositive : 0 < fraction) (fractionStrict : fraction < 1) :
    Tendsto (xiFractionalEccentricityBallResistance system birth center fraction) atTop atTop := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, growth⟩ :=
    xiOriginalEccentricity_spectral_growth system connected loopless unique
      plantingNonadjacent distancePositive
  obtain ⟨coefficient, resistanceLower, coefficientPositive, resistanceLowerPositive, lowerBound⟩ :=
    xiSimpleGraph_large_ball_resistance_spectral_lower system connected loopless unique
      plantingNonadjacent distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  obtain ⟨buffer, bufferBound⟩ := pow_unbounded_of_one_lt
    (coefficient / (fraction * lower * (system.distanceSpectralRadius connected) ^ birth))
    distanceGreaterThanOne
  have bufferConstant : coefficient ≤ fraction * lower *
      (system.distanceSpectralRadius connected) ^ (birth + buffer) := by
    have positive : 0 < fraction * lower * (system.distanceSpectralRadius connected) ^ birth :=
      by positivity
    calc
      coefficient ≤ (system.distanceSpectralRadius connected) ^ buffer *
          (fraction * lower * (system.distanceSpectralRadius connected) ^ birth) :=
        (le_of_lt ((div_lt_iff₀ positive).mp bufferBound))
      _ = fraction * lower * (system.distanceSpectralRadius connected) ^ (birth + buffer) := by
        rw [pow_add]
        ring
  have shiftedGrowth : ∀ᶠ steps in atTop, ∀ vertex : XiVtx system ((birth + buffer) + steps),
      lower * (system.distanceSpectralRadius connected) ^ ((birth + buffer) + steps) ≤
        finiteGraphEccentricity (XiSimpleGraph system ((birth + buffer) + steps)) vertex := by
    have shifted := Filter.Tendsto.eventually (tendsto_add_atTop_nat (birth + buffer)) growth
    filter_upwards [shifted] with steps bounds
    rw [Nat.add_comm (birth + buffer) steps]
    exact fun vertex => (bounds vertex).1
  have actualLower : ∀ᶠ steps in atTop,
      resistanceLower * (system.resistanceSpectralRadius connected distancePositive) ^ steps /
          (XiSimpleGraph system (birth + buffer)).degree (xiForward system birth buffer center) ≤
        xiFractionalEccentricityBallResistance system birth center fraction (buffer + steps) := by
    filter_upwards [shiftedGrowth] with steps growthBound
    have radiusBound : coefficient * (system.distanceSpectralRadius connected) ^ steps ≤
        fraction * finiteGraphEccentricity (XiSimpleGraph system ((birth + buffer) + steps))
          (xiForward system (birth + buffer) steps (xiForward system birth buffer center)) := by
      calc
        coefficient * (system.distanceSpectralRadius connected) ^ steps ≤
            (fraction * lower * (system.distanceSpectralRadius connected) ^ (birth + buffer)) *
              (system.distanceSpectralRadius connected) ^ steps :=
          mul_le_mul_of_nonneg_right bufferConstant
            (pow_nonneg (zero_le_one.trans distanceGreaterThanOne.le) steps)
        _ = fraction * (lower * (system.distanceSpectralRadius connected) ^
            ((birth + buffer) + steps)) := by rw [pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (growthBound _) fractionPositive.le
    letI : Nontrivial (XiVtx system ((birth + buffer) + steps)) :=
      ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
    have proper := finiteGraph_fractional_eccentricity_ball_proper
      (XiSimpleGraph system ((birth + buffer) + steps))
      (xiSimpleGraph_connected system connected _)
      (xiForward system (birth + buffer) steps (xiForward system birth buffer center))
      fraction fractionStrict
    have actual := lowerBound (birth + buffer) steps (xiForward system birth buffer center)
      _ radiusBound (by
        obtain ⟨outside, outsideMembership⟩ := proper
        have outsideNotMember :=
          (@Finset.mem_compl _ _ _ (Classical.decEq _) outside).mp outsideMembership
        exact ⟨outside, Finset.mem_compl.mpr outsideNotMember⟩)
    change _ ≤ xiFractionalEccentricityBallResistance system (birth + buffer)
      (xiForward system birth buffer center) fraction steps at actual
    rw [xiFractionalEccentricityBallResistance_trans] at actual
    exact actual
  have diverges := ((tendsto_pow_atTop_atTop_of_one_lt resistanceGreaterThanOne).const_mul_atTop
    resistanceLowerPositive).atTop_div_const
      (xiSimpleGraph_degree_positive system connected (birth + buffer)
        (xiForward system birth buffer center))
  have shiftedLimit := tendsto_atTop_mono' atTop actualLower diverges
  apply (tendsto_add_atTop_iff_nat buffer).mp
  simpa only [Nat.add_comm buffer] using shiftedLimit

theorem xiFractionalEccentricityBallResistance_not_all_tendsto_of_le_one
    (resistanceAtMostOne : system.resistanceSpectralRadius connected distancePositive ≤ 1) :
    ¬ (∀ birth (center : XiVtx system birth) fraction,
      0 < fraction → fraction < 1 →
      Tendsto (xiFractionalEccentricityBallResistance system birth center fraction) atTop atTop) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, growth⟩ :=
    xiOriginalEccentricity_spectral_growth system connected loopless unique
      plantingNonadjacent distancePositive
  obtain ⟨coefficient, resistanceUpper, coefficientPositive, resistanceUpperPositive, upperBound⟩ :=
    xiSimpleGraph_ball_resistance_spectral_upper system connected loopless unique
      plantingNonadjacent distancePositive
  have distancePositiveReal : 0 < system.distanceSpectralRadius connected :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  have fractionPositive : 0 < min (1 / 2 : ℝ) (coefficient / (2 * upper)) := by positivity
  have fractionStrict : min (1 / 2 : ℝ) (coefficient / (2 * upper)) < 1 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have coefficientBound : min (1 / 2 : ℝ) (coefficient / (2 * upper)) * upper ≤ coefficient := by
    have bound := (le_div_iff₀ (by positivity : 0 < 2 * upper)).mp
      (min_le_right (1 / 2 : ℝ) (coefficient / (2 * upper)))
    nlinarith
  let center : XiVtx system 0 := xiPositiveTerminal system 0
  have eventualBound : ∀ᶠ age in atTop,
      xiFractionalEccentricityBallResistance system 0 center
        (min (1 / 2 : ℝ) (coefficient / (2 * upper))) age ≤
      resistanceUpper / (XiSimpleGraph system 0).degree center := by
    filter_upwards [growth] with age bounds
    letI : Nontrivial (XiVtx system (0 + age)) :=
      ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
    have currentBounds : ∀ vertex : XiVtx system (0 + age),
        finiteGraphEccentricity (XiSimpleGraph system (0 + age)) vertex ≤
          upper * (system.distanceSpectralRadius connected) ^ age := by
      rw [Nat.zero_add]
      exact fun vertex => (bounds vertex).2
    have radiusPositive : 0 < min (1 / 2 : ℝ) (coefficient / (2 * upper)) *
        finiteGraphEccentricity (XiSimpleGraph system (0 + age)) (xiForward system 0 age center) := by
      exact mul_pos fractionPositive (finiteGraphEccentricity_positive _
        (xiSimpleGraph_connected system connected _) _)
    have radiusBound : min (1 / 2 : ℝ) (coefficient / (2 * upper)) *
        finiteGraphEccentricity (XiSimpleGraph system (0 + age)) (xiForward system 0 age center) ≤
        coefficient * (system.distanceSpectralRadius connected) ^ age := by
      calc
        _ ≤ min (1 / 2 : ℝ) (coefficient / (2 * upper)) *
            (upper * (system.distanceSpectralRadius connected) ^ age) := by
          apply mul_le_mul_of_nonneg_left _ fractionPositive.le
          exact currentBounds (xiForward system 0 age center)
        _ = (min (1 / 2 : ℝ) (coefficient / (2 * upper)) * upper) *
            (system.distanceSpectralRadius connected) ^ age := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right coefficientBound (pow_nonneg distancePositiveReal.le age)
    have actual := upperBound 0 age center _ radiusPositive radiusBound
    change xiFractionalEccentricityBallResistance system 0 center _ age ≤ _ at actual
    apply actual.trans
    apply div_le_div_of_nonneg_right _
      (xiSimpleGraph_degree_positive system connected 0 center).le
    exact mul_le_of_le_one_right resistanceUpperPositive.le
      (pow_le_one₀ (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1.le
        resistanceAtMostOne)
  intro allDiverge
  have diverges := allDiverge 0 center _ fractionPositive fractionStrict
  obtain ⟨age, upperBoundAtAge, lowerBoundAtAge⟩ :=
    (eventualBound.and (diverges.eventually_ge_atTop
      (resistanceUpper / (XiSimpleGraph system 0).degree center + 1))).exists
  linarith

theorem xiActualRecurrence_iff_resistanceSpectralRadius_gt_one :
    (∀ birth (center : XiVtx system birth) fraction,
      0 < fraction → fraction < 1 →
      Tendsto (xiFractionalEccentricityBallResistance system birth center fraction) atTop atTop) ↔
    1 < system.resistanceSpectralRadius connected distancePositive := by
  constructor
  · intro recurrence
    by_contra noGrowth
    exact xiFractionalEccentricityBallResistance_not_all_tendsto_of_le_one system connected
      loopless unique plantingNonadjacent distancePositive (le_of_not_gt noGrowth) recurrence
  · intro growth birth center fraction positive strict
    exact xiFractionalEccentricityBallResistance_tendsto_of_one_lt system connected loopless unique
      plantingNonadjacent distancePositive growth birth center fraction positive strict

theorem xiActualRecurrent_iff_resistanceSpectralRadius_gt_one :
    xiActualRecurrent system ↔ 1 < system.resistanceSpectralRadius connected distancePositive := by
  simp only [xiActualRecurrent, xi_liminf_ofReal_eq_top_iff_tendsto_atTop]
  exact xiActualRecurrence_iff_resistanceSpectralRadius_gt_one system connected loopless unique
    plantingNonadjacent distancePositive

end
end EIGS

#print axioms EIGS.xiFractionalEccentricityBallResistance_trans
#print axioms EIGS.xiFractionalEccentricityBallResistance_tendsto_of_one_lt
#print axioms EIGS.xiFractionalEccentricityBallResistance_not_all_tendsto_of_le_one
#print axioms EIGS.xiActualRecurrence_iff_resistanceSpectralRadius_gt_one
#print axioms EIGS.xi_liminf_ofReal_eq_top_iff_tendsto_atTop
#print axioms EIGS.xiActualRecurrent_iff_resistanceSpectralRadius_gt_one
