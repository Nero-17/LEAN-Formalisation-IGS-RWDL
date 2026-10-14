import RequestProject.Section31.EIGSContinuousResistanceFormOfRules
import RequestProject.Section31.EIGSOriginalClosedEnergyIdentification
import RequestProject.Section31.EIGSConservativeHuntClosedIdentification

/-! The resistance form is the original closed form of the already
constructed conservative continuous-path Hunt family. The final theorem
selects the existing Hunt witness first, then constructs the resistance form
for precisely that witness's positive energy eigenvector. Domain equality
and literal closed-form agreement supply the identification; no second
process or independent energy normalization is selected. Candidate, uncompiled. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
noncomputable section
variable {K : ℕ}

def XiResistanceFormClosedIdentification
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) : Prop :=
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative = originalDomain ∧
  ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
    ∀ function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
        ⟨(xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive function).val,
          QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative _⟩ =
      xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function

theorem xiResistanceFormClosedIdentification_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    XiResistanceFormClosedIdentification system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  constructor
  · exact xiOriginal_closedDomain_eq system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate
      rateGreaterThanOne resistanceVector vectorPositive eigenpair
  · intro closable function
    rw [QuadraticEnergySpace.closedForm_extends]
    exact xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair function

theorem exists_xiResistanceForm_same_closed_Hunt_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      Nonempty (XiContinuousResistanceFormRealization system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)) ∧
      XiResistanceFormClosedIdentification system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedConservativeHuntContinuousPathProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive := by
  intro parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
      normalization, normalizationPositive, normalizedConvergence, huntProperties⟩ :=
    exists_xiIdentifiedConservativeHuntContinuousPath_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have canonicalEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext eigenpair)
  have rateGreaterThanOne : 1 < resistanceRate := by
    rw [canonicalEquality]
    exact canonicalRateGreaterThanOne
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_, ?_, huntProperties⟩
  · exact exists_xiContinuousResistanceFormRealization_of_rules system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair (xiVertexEmbedding system 0 true) rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance mass rateGreaterThanOne
  · exact xiResistanceFormClosedIdentification_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive rateGreaterThanOne resistanceVector vectorPositive eigenpair

end
end EIGS

#print axioms EIGS.xiResistanceFormClosedIdentification_of_rules
#print axioms EIGS.exists_xiResistanceForm_same_closed_Hunt_of_rules
