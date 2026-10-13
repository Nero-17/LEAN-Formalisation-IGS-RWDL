import RequestProject.Section31.EIGSAnchoredWindowDisplacementTail
import RequestProject.Section31.FloorClockModulusCover
import RequestProject.Section31.EIGSNativeGridWindowClock

/-! Actual full-horizon floor-path modulus probabilities. The finite grid
factor, the two-window exponent and the absolute-floor rounding correction are
all retained. The original-rule consumer fills the integer-window tails and
clock correction internally, with one common set of parameter witnesses. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory Preorder
open scoped BigOperators ProbabilityTheory Classical ENNReal
noncomputable section
set_option maxHeartbeats 4000000

theorem floor_clock_modulus_probability_real_le_grid_bound
    {Sample Space : Type} [MeasurableSpace Sample] [PseudoMetricSpace Space]
    (law : Measure Sample) [IsProbabilityMeasure law] (process : Sample → ℕ → Space)
    (rate horizon window radius bound : ℝ) (rateNonnegative : 0 ≤ rate)
    (windowPositive : 0 < window) (boundNonnegative : 0 ≤ bound)
    (integerWindowBounds : ∀ index : ℕ, index ≤ ⌊horizon / window⌋₊ →
      (law {sample | ∃ offset : ℕ,
        offset ≤ ⌊((index : ℝ) + 2) * window * rate⌋₊ -
          ⌊(index : ℝ) * window * rate⌋₊ ∧
        radius < dist (process sample (⌊(index : ℝ) * window * rate⌋₊ + offset))
          (process sample ⌊(index : ℝ) * window * rate⌋₊)}).toReal ≤ bound) :
    (law {sample | ∃ first ∈ Set.Icc (0 : ℝ) horizon,
      ∃ second ∈ Set.Icc (0 : ℝ) horizon, |second - first| ≤ window ∧
        2 * radius < dist (process sample ⌊first * rate⌋₊)
          (process sample ⌊second * rate⌋₊)}).toReal ≤
      ((⌊horizon / window⌋₊ : ℝ) + 1) * bound := by
  have ennrealBound := floor_clock_modulus_probability_le_grid_bound law process
    rate horizon window radius rateNonnegative windowPositive (ENNReal.ofReal bound) (by
      intro index bounded
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top law _) boundNonnegative).mpr
        (integerWindowBounds index bounded))
  have finiteBound : (⌊horizon / window⌋₊ + 1 : ℝ≥0∞) * ENNReal.ofReal bound ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have realBound := ENNReal.toReal_mono finiteBound ennrealBound
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_add (a := (⌊horizon / window⌋₊ : ℝ≥0∞)) (b := 1) (by simp) (by simp),
    ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_ofReal boundNonnegative,
    Nat.cast_add, Nat.cast_one] using realBound

/-- Although the time quantifiers are real, a floor path on a bounded horizon
uses a finite coordinate prefix. Every predicate on that finite state space is
measurable; no continuity of the step path or its embedding is required. -/
theorem finite_floor_clock_modulus_event_measurable {X Space : Type}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [PseudoMetricSpace Space]
    (embedding : X → Space) (rate horizon window radius : ℝ) (rateNonnegative : 0 ≤ rate) :
    MeasurableSet {path : ℕ → X | ∃ first ∈ Set.Icc (0 : ℝ) horizon,
      ∃ second ∈ Set.Icc (0 : ℝ) horizon, |second - first| ≤ window ∧
        2 * radius < dist (embedding (path ⌊first * rate⌋₊)) (embedding (path ⌊second * rate⌋₊))} := by
  let last := ⌊horizon * rate⌋₊
  let event : Set (ℕ → X) := {path | ∃ first ∈ Set.Icc (0 : ℝ) horizon,
    ∃ second ∈ Set.Icc (0 : ℝ) horizon, |second - first| ≤ window ∧
      2 * radius < dist (embedding (path ⌊first * rate⌋₊)) (embedding (path ⌊second * rate⌋₊))}
  have agree (path : ℕ → X) (time : ℝ) (bounded : time ≤ horizon) :
      completedHistory (frestrictLe last path) ⌊time * rate⌋₊ = path ⌊time * rate⌋₊ := by
    have coordinateBound : ⌊time * rate⌋₊ ≤ last :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right bounded rateNonnegative)
    simp only [completedHistory, dif_pos coordinateBound, frestrictLe_apply]
  have eventEquality : event = (frestrictLe last) ⁻¹' {history | completedHistory history ∈ event} := by
    ext path
    constructor
    · rintro ⟨first, firstBounds, second, secondBounds, close, far⟩
      refine ⟨first, firstBounds, second, secondBounds, close, ?_⟩
      simpa only [agree path first firstBounds.2, agree path second secondBounds.2] using far
    · rintro ⟨first, firstBounds, second, secondBounds, close, far⟩
      refine ⟨first, firstBounds, second, secondBounds, close, ?_⟩
      simpa only [agree path first firstBounds.2, agree path second secondBounds.2] using far
  change MeasurableSet event
  rw [eventEquality]
  exact (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe last)

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiFullHorizonModulusEvent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected) (normalization : ℝ)
    (coarse steps count : ℕ) (horizon window : ℝ) : Set (ℕ → XiVtx system (coarse + steps)) :=
  {path | ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
    |second - first| ≤ window ∧
      2 * ((count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)) <
      dist (parameters.vertexEmbedding (coarse + steps)
        (path ⌊first * xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊))
        (parameters.vertexEmbedding (coarse + steps)
          (path ⌊second * xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊))}

theorem xiFullHorizonModulusEvent_measurable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected) (normalization : ℝ)
    (normalizationNonnegative : 0 ≤ normalization) (coarse steps count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (horizon window : ℝ) :
    MeasurableSet (xiFullHorizonModulusEvent system rulesConnected distancePositive parameters normalization
      coarse steps count horizon window) := by
  exact finite_floor_clock_modulus_event_measurable (parameters.vertexEmbedding (coarse + steps))
    (xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
    horizon window ((count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse))
    (xiNativeFiniteJumpRate_nonnegative system (coarse + steps) _ normalization
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1.le normalizationNonnegative)

/-- All windows use the same fraction, survival probability and clock factor.
The full finite grid factor is retained, and no window-tail premise appears in
this original-rule consumer. -/
theorem exists_xiFullHorizonModulusBound_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)] :
    ∃ fraction probability factor : ℝ, 0 < fraction ∧ 0 < probability ∧ 0 < factor ∧
      0 ≤ 1 - probability * (1 - Real.exp (-1)) ∧
      1 - probability * (1 - Real.exp (-1)) < 1 ∧
      ∀ (coarse steps count : ℕ) (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
      (horizon window : ℝ), 0 < window →
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
      ((pathLaw transition (initial : Measure _))
        (xiFullHorizonModulusEvent system rulesConnected distancePositive parameters normalization
          coarse steps count horizon window)).toReal ≤
        ((⌊horizon / window⌋₊ : ℝ) + 1) * factor *
          Real.exp (2 * window / (fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) *
              (1 - probability * (1 - Real.exp (-1))) ^ count := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, anchored⟩ :=
    exists_xiAnchoredWindowDisplacementTail_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  obtain ⟨factor, factorPositive, clockBound⟩ := xiNativeGridWindow_exponential_bound_of_rules system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive normalization fraction normalizationPositive fractionPositive
  refine ⟨fraction, probability, factor, fractionPositive, probabilityPositive, factorPositive,
    decayNonnegative, decayLessThanOne, ?_⟩
  intro coarse steps count initial horizon window windowPositive parameters transition
  let actualLaw := pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))
  let jumpRate := xiNativeFiniteJumpRate system (coarse + steps)
    (system.resistanceSpectralRadius rulesConnected distancePositive) normalization
  let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
    (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
  let bound := factor * Real.exp (2 * window / (fraction *
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) *
    (1 - probability * (1 - Real.exp (-1))) ^ count
  have boundNonnegative : 0 ≤ bound :=
    mul_nonneg (mul_nonneg factorPositive.le (Real.exp_pos _).le) (pow_nonneg decayNonnegative count)
  have rateNonnegative : 0 ≤ jumpRate := xiNativeFiniteJumpRate_nonnegative system (coarse + steps) _ normalization
    (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1.le normalizationPositive.le
  have fullBound := floor_clock_modulus_probability_real_le_grid_bound actualLaw
    (fun path index => parameters.vertexEmbedding (coarse + steps) (path index))
    jumpRate horizon window radius bound rateNonnegative windowPositive boundNonnegative (by
      intro index indexBound
      have integerTail := anchored coarse steps ⌊(index : ℝ) * window * jumpRate⌋₊
        (⌊((index : ℝ) + 2) * window * jumpRate⌋₊ - ⌊(index : ℝ) * window * jumpRate⌋₊) count initial
      have afterAnchor : (index : ℝ) * window ≤ ((index : ℝ) + 2) * window := by nlinarith
      have clock := clockBound coarse steps window (((index : ℝ) + 2) * window) index
        windowPositive afterAnchor le_rfl
      have uniformTail := integerTail.trans
        (mul_le_mul_of_nonneg_right clock (pow_nonneg decayNonnegative count))
      simpa only [xiAnchoredCoarseDisplacementEvent] using uniformTail)
  change (actualLaw (xiFullHorizonModulusEvent system rulesConnected distancePositive parameters normalization
    coarse steps count horizon window)).toReal ≤ _
  calc
    _ ≤ ((⌊horizon / window⌋₊ : ℝ) + 1) * bound := fullBound
    _ = _ := by dsimp only [bound]; ring

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.floor_clock_modulus_probability_real_le_grid_bound
#print axioms EIGS.xiFullHorizonModulusEvent_measurable
#print axioms EIGS.exists_xiFullHorizonModulusBound_of_rules
