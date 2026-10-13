import RequestProject.Section31.EIGSActualL2Core
import RequestProject.Section31.VaryingL2Multiplication

/-! Bounded multiplication for the actual native Xi spaces, with all weak
measure convergence supplied by the original construction. Backward finite
observation products then preserve strong convergence by explicit induction. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

variable {K : ℕ}

theorem xiSpeedL2Core_strong_multiplication (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) :
    letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
    ∀ (multiplier : XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ)
      (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (target : Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)),
      (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).Strong sequence target →
      (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).Strong
        (fun level => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
          (xiCompletionEmbedding system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair)
          (measurable_xiCompletionEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
          multiplier level (sequence level))
        (boundedContinuousLimitMultiplication
          (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
          multiplier target) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  intro multiplier sequence target convergence
  have weakConvergence : Tendsto
      (embeddedProbabilityMeasures (xiNativeSpeedProbabilityMeasure system mass)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair)
        (measurable_xiCompletionEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair))
      atTop (nhds (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
    rw [xiEmbeddedSpeedProbabilityMeasure_eq]
    exact xiSpeedProbabilityMeasure_tendsto system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
  exact embeddedProbabilityL2Core_strong_multiplication
    (xiNativeSpeedProbabilityMeasure system mass)
    (xiCompletionEmbedding system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (measurable_xiCompletionEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    weakConvergence multiplier convergence

end EIGS

namespace IGS.Sec31.FiniteObservations

open Filter Topology

variable {Time Test Hilbert : Type*}
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

/-- The finite backward product of observations and the actual intervening operators. -/
def backwardProduct (evolution : Time → Hilbert →L[ℝ] Hilbert)
    (multiplication : Test → Hilbert →L[ℝ] Hilbert) :
    List (Time × Test) → Hilbert → Hilbert
  | [], terminal => terminal
  | observation :: remaining, terminal =>
      multiplication observation.2 (evolution observation.1
        (backwardProduct evolution multiplication remaining terminal))

variable {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    {LevelHilbert : ℕ → Type*}
    [∀ level, NormedAddCommGroup (LevelHilbert level)]
    [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem backwardProduct_strong
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (levelEvolution : ∀ level, Time → LevelHilbert level →L[ℝ] LevelHilbert level)
    (evolution : Time → Hilbert →L[ℝ] Hilbert)
    (levelMultiplication : ∀ level, Test → LevelHilbert level →L[ℝ] LevelHilbert level)
    (multiplication : Test → Hilbert →L[ℝ] Hilbert)
    (evolutionStrong : ∀ time sequence target, core.Strong sequence target →
      core.Strong (fun level => levelEvolution level time (sequence level)) (evolution time target))
    (multiplicationStrong : ∀ test sequence target, core.Strong sequence target →
      core.Strong (fun level => levelMultiplication level test (sequence level)) (multiplication test target))
    (observations : List (Time × Test))
    {terminalSequence : ∀ level, LevelHilbert level} {terminal : Hilbert}
    (terminalStrong : core.Strong terminalSequence terminal) :
    core.Strong
      (fun level => backwardProduct (levelEvolution level) (levelMultiplication level) observations (terminalSequence level))
      (backwardProduct evolution multiplication observations terminal) := by
  induction observations with
  | nil => exact terminalStrong
  | cons observation remaining induction =>
    exact multiplicationStrong observation.2 _ _ (evolutionStrong observation.1 _ _ induction)

theorem backwardProduct_pairing_limit
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (levelEvolution : ∀ level, Time → LevelHilbert level →L[ℝ] LevelHilbert level)
    (evolution : Time → Hilbert →L[ℝ] Hilbert)
    (levelMultiplication : ∀ level, Test → LevelHilbert level →L[ℝ] LevelHilbert level)
    (multiplication : Test → Hilbert →L[ℝ] Hilbert)
    (evolutionStrong : ∀ time sequence target, core.Strong sequence target →
      core.Strong (fun level => levelEvolution level time (sequence level)) (evolution time target))
    (multiplicationStrong : ∀ test sequence target, core.Strong sequence target →
      core.Strong (fun level => levelMultiplication level test (sequence level)) (multiplication test target))
    (observations : List (Time × Test))
    {terminalSequence initialSequence : ∀ level, LevelHilbert level}
    {terminal initial : Hilbert}
    (terminalStrong : core.Strong terminalSequence terminal)
    (initialStrong : core.Strong initialSequence initial) :
    Tendsto (fun level => inner ℝ (initialSequence level)
      (backwardProduct (levelEvolution level) (levelMultiplication level) observations (terminalSequence level)))
      atTop (nhds (inner ℝ initial (backwardProduct evolution multiplication observations terminal))) :=
  core.strong_inner_tendsto initialStrong
    (backwardProduct_strong core levelEvolution evolution levelMultiplication multiplication
      evolutionStrong multiplicationStrong observations terminalStrong)

end IGS.Sec31.FiniteObservations

#print axioms EIGS.xiSpeedL2Core_strong_multiplication
#print axioms IGS.Sec31.FiniteObservations.backwardProduct_strong
#print axioms IGS.Sec31.FiniteObservations.backwardProduct_pairing_limit
