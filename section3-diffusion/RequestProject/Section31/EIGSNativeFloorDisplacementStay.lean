import RequestProject.Section31.EIGSAnchoredWindowDisplacementTail

/-! The already constructed all-start maximal displacement estimate at the
actual floor clock. A fixed number of coarse arrivals gives a uniform small
tail on the original time scale, without any restriction on the resistance
spectral radius other than the positivity obtained from the rules.
Candidate source: no compilation is claimed. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem exists_xiNativeFloorDisplacementStay_of_rules (system : EIGSData K)
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
    ∃ fraction : ℝ, 0 < fraction ∧ ∃ count : ℕ,
      ∀ (coarse steps : ℕ) (window : ℝ), 0 ≤ window →
      window ≤ fraction *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse →
      ∀ initial : ProbabilityMeasure (XiVtx system (coarse + steps)),
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
      let horizon := Nat.floor (window * xiNativeFiniteJumpRate system (coarse + steps)
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
      ((pathLaw transition (initial : Measure _))
        (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps 0 horizon count)).toReal ≤
          (1 / 4 : ℝ) := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive,
      decayNonnegative, decayBelowOne, tails⟩ :=
    exists_xiAnchoredWindowDisplacementTail_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  have vanishing : Tendsto
      (fun count : ℕ => Real.exp 1 * (1 - probability * (1 - Real.exp (-1))) ^ count)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one decayNonnegative decayBelowOne).const_mul (Real.exp 1)
  obtain ⟨count, countBound⟩ :=
    (vanishing.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  refine ⟨fraction, fractionPositive, count, ?_⟩
  intro coarse steps window windowNonnegative windowBound initial parameters transition horizon
  have spatialPositive : 0 <
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by
    have massPositive := (eigs_mass_spectral_growth system rulesConnected distancePositive).1
    have resistancePositive :=
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
    positivity
  have scalePositive := xiCoarseNativeLaplaceScale_positive system rulesConnected distancePositive
    normalization fraction normalizationPositive fractionPositive coarse steps
  have jumpPositive : 0 < xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization := by
    have productPositive : 0 < xiNativeFiniteJumpRate system (coarse + steps)
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * fraction :=
      (mul_pos_iff_of_pos_right spatialPositive).mp scalePositive
    exact (mul_pos_iff_of_pos_right fractionPositive).mp productPositive
  have ratioBound : (horizon : ℝ) /
      xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps ≤ 1 := by
    calc
      _ ≤ window / (fraction *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse) := by
        simpa only [horizon, xiCoarseNativeLaplaceScale, mul_comm window] using
          floor_native_clock_ratio_le
            (xiNativeFiniteJumpRate system (coarse + steps)
              (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
            fraction _ window jumpPositive fractionPositive spatialPositive windowNonnegative
      _ ≤ 1 := (div_le_one (mul_pos fractionPositive spatialPositive)).mpr windowBound
  exact (tails coarse steps 0 horizon count initial).trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ratioBound)
      (pow_nonneg decayNonnegative count)).trans countBound.le)

end
end EIGS

#print axioms EIGS.exists_xiNativeFloorDisplacementStay_of_rules
