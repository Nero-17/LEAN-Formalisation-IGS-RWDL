import RequestProject.Section31.EIGSDiameterGromovHausdorff
import RequestProject.Section31.FiniteDiameterMetric

/-! The preliminary Perron rescaling disappears exactly. The final sequence
is the original unit graph divided only by its own diameter. -/

namespace EIGS

set_option maxHeartbeats 150000

open Filter Topology Metric Set GromovHausdorff
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiOriginalDiameterGHPoint (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) : GHSpace :=
  xiDiameterFiniteGHPoint system connected 1 zero_lt_one 1 zero_lt_one level

theorem xiDiameterFiniteGHPoint_eq_original (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (rate : ℝ) (ratePositive : 0 < rate) (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ) :
    xiDiameterFiniteGHPoint system connected rate ratePositive scale scalePositive level =
      xiOriginalDiameterGHPoint system connected level := by
  letI := xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
    1 zero_lt_one level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  have levelScalePositive : 0 < rate⁻¹ ^ level * scale⁻¹ :=
    mul_pos (pow_pos (inv_pos.mpr ratePositive) _) (inv_pos.mpr scalePositive)
  have metricEquality : positiveScaledMetricSpace (XiVtx system level)
      (rate⁻¹ ^ level * scale⁻¹) levelScalePositive =
      xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate ratePositive level := by
    apply MetricSpace.ext
    ext source sink
    change (rate⁻¹ ^ level * scale⁻¹) *
        ((1 : ℝ)⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => (1 : ℝ)⁻¹) source sink) =
      rate⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => scale⁻¹) source sink
    have lengthsEquality : (fun _ : Fin K => scale⁻¹) = scale⁻¹ • (fun _ : Fin K => (1 : ℝ)) := by
      ext colour
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [lengthsEquality, Network.weightedDistance_smul _ _ (inv_nonneg.mpr scalePositive.le)]
    simp only [inv_one, one_pow, one_mul]
    ring
  have originalPositive := xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have basedPositive := xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate ratePositive level
  calc
    _ = finiteDiameterMetricPoint (XiVtx system level)
        (xiLevelMetricSpace system connected (fun _ => scale⁻¹)
          (fun _ => inv_pos.mpr scalePositive) rate ratePositive level) :=
      (finiteDiameterMetricPoint_eq (XiVtx system level) _ basedPositive).symm
    _ = finiteDiameterMetricPoint (XiVtx system level)
        (positiveScaledMetricSpace (XiVtx system level)
          (rate⁻¹ ^ level * scale⁻¹) levelScalePositive) :=
      congrArg (finiteDiameterMetricPoint (XiVtx system level)) metricEquality.symm
    _ = finiteDiameterMetricPoint (XiVtx system level)
        (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level) :=
      finiteDiameterMetricPoint_scale_invariant (XiVtx system level) originalPositive
        (rate⁻¹ ^ level * scale⁻¹) levelScalePositive
    _ = xiOriginalDiameterGHPoint system connected level :=
      finiteDiameterMetricPoint_eq (XiVtx system level) _ originalPositive

theorem xiSimpleGraph_original_diameter_gromovHausdorff_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) (normalized : (∑ colour, lengths colour) = 1)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    Tendsto (xiOriginalDiameterGHPoint system connected) atTop
      (nhds (xiDiameterLimitGHPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)) := by
  obtain ⟨scale, scalePositive, convergence⟩ := xiSimpleGraph_diameter_gromovHausdorff_limit system connected
    loopless unique plantingNonadjacent distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  have sequenceEquality : xiDiameterFiniteGHPoint system connected rate
      (zero_lt_one.trans rateGreaterThanOne) scale scalePositive = xiOriginalDiameterGHPoint system connected := by
    funext level
    exact xiDiameterFiniteGHPoint_eq_original system connected rate (zero_lt_one.trans rateGreaterThanOne)
      scale scalePositive level
  rw [sequenceEquality] at convergence
  exact convergence

end EIGS

#print axioms EIGS.xiDiameterFiniteGHPoint_eq_original
#print axioms EIGS.xiSimpleGraph_original_diameter_gromovHausdorff_limit
