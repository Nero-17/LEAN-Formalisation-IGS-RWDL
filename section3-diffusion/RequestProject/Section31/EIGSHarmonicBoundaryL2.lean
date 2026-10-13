import RequestProject.Section31.EIGSHarmonicJointUniform
import RequestProject.Section31.EIGSL2EnergyRepresentative
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual finite harmonic boundary coordinates remain nondegenerate in the
native limit L² space. Full support and the actual boundary identities prove
injectivity; finite-dimensional norm equivalence then controls the boundary
coordinates by their actual L² harmonic extension. -/

namespace EIGS

open MeasureTheory

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily connected).metricLengths lengths = distanceRate • lengths)

theorem xiContinuousUnionRestriction_injective :
    Function.Injective (xiContinuousUnionRestriction system connected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair) := by
  intro first second equality
  apply DFunLike.coe_injective
  exact (xiCompletionUnionEmbedding_denseRange system connected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).equalizer
      first.continuous second.continuous equality

theorem exists_xiHarmonic_boundary_L2_control
    (mass : XiMassParameters system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) :
    letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    ∃ extensionMap : (XiVtx system initialLevel → ℝ) →ₗ[ℝ]
        C(XiMetricCompletion system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ values vertex,
        extensionMap values (xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system connected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel values vertex) ∧
      Function.Injective ((xiContinuousL2Map system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass).toLinearMap.comp extensionMap) ∧
      ∃ bound : ℝ, 0 < bound ∧ ∀ values,
        ‖values‖ ≤ bound * ‖xiContinuousL2Map system connected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass (extensionMap values)‖ := by
  classical
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system connected
        distancePositive oneColourDistance resistanceVector resistanceVectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system connected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair profiles
      profilesPlus profilesMinus profilesMinimal contractionFactor profilesOscillation
  choose extension extensionAgreement using fun values : XiVtx system initialLevel → ℝ =>
    exists_xiContinuousHarmonic_of_step_contraction system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair contractionFactor factorPositive factorStrict
      stepContraction initialLevel values
  let extensionMap : (XiVtx system initialLevel → ℝ) →ₗ[ℝ]
      C(XiMetricCompletion system connected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ) := {
    toFun := extension
    map_add' := by
      intro first second
      apply xiContinuousUnionRestriction_injective system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair
      funext vertex
      change extension (first + second) (xiCompletionUnionEmbedding system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        extension first (xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) +
        extension second (xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)
      rw [extensionAgreement, extensionAgreement, extensionAgreement]
      exact congrFun ((xiHarmonicUnionLinearMap system connected resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel).map_add first second) vertex
    map_smul' := by
      intro scalar values
      apply xiContinuousUnionRestriction_injective system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair
      funext vertex
      change extension (scalar • values) (xiCompletionUnionEmbedding system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        scalar * extension values (xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)
      rw [extensionAgreement, extensionAgreement]
      exact congrFun ((xiHarmonicUnionLinearMap system connected resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel).map_smul scalar values) vertex }
  let nativeMap := (xiContinuousL2Map system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass).toLinearMap.comp extensionMap
  have nativeInjective : Function.Injective nativeMap := by
    intro first second equality
    have continuousEquality : extension first = extension second :=
      xiContinuousL2Map_injective system connected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass equality
    apply xiHarmonicUnionLinearMap_injective system connected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel
    funext vertex
    change xiHarmonicUnionExtension system connected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel first vertex =
      xiHarmonicUnionExtension system connected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel second vertex
    rw [← extensionAgreement, ← extensionAgreement, continuousEquality]
  obtain ⟨bound, boundPositive, inverseBound⟩ := nativeMap.injective_iff_antilipschitz.mp nativeInjective
  refine ⟨extensionMap, extensionAgreement, nativeInjective, (bound : ℝ), ?_, ?_⟩
  · exact_mod_cast boundPositive
  · intro values
    exact ZeroHomClass.bound_of_antilipschitz nativeMap inverseBound values

end EIGS

#print axioms EIGS.xiContinuousUnionRestriction_injective
#print axioms EIGS.exists_xiHarmonic_boundary_L2_control
