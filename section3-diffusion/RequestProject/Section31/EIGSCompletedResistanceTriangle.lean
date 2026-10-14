import RequestProject.Section31.EIGSFiniteEnergyCompactExtension
import RequestProject.Section31.EIGSSkeletonResistanceTriangle

/-! Actual resistance on every point of the original metric completion.
Compactness of the constructed energy extension makes its Riesz rows norm
continuous. The squared row-difference norm restricts to the actual skeleton
resistance, and density transfers the triangle inequality for R itself.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair

variable (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor →L[ℝ]
  C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))

def xiCompletedResistanceRow (point : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :
    xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor :=
  continuousOperatorKernelRow (extension.comp
    (xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor).subtypeL) point

def xiCompletedResistance (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) : ℝ :=
  ‖xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first -
    xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension second‖ ^ 2

variable (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
  distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex)

include agreement in
theorem xiCompletedResistanceRow_sub_on_skeleton (first second : XiVertexUnion system) :
    xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension
      (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair first) -
    xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension
      (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair second) =
    xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first second := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  apply ext_inner_right ℝ
  intro values
  rw [inner_sub_left, xiSkeletonResistanceRiesz_represents]
  unfold xiCompletedResistanceRow
  rw [← continuousOperatorKernelRow_represents, ← continuousOperatorKernelRow_represents]
  change extension values.val _ - extension values.val _ = _
  rw [agreement, agreement]

include agreement in
theorem xiCompletedResistance_on_skeleton (first second : XiVertexUnion system) :
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension
      (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair first)
      (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair second) =
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first second := by
  unfold xiCompletedResistance
  rw [xiCompletedResistanceRow_sub_on_skeleton system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    anchor extension agreement]
  rfl

variable (extensionCompact : IsCompactOperator extension)

include extensionCompact in
theorem xiCompletedResistanceRow_continuous :
    Continuous (xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  exact continuousOperatorKernelRow_continuous _
    (extensionCompact.comp_clm (xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor).subtypeL)

include extensionCompact in
theorem xiCompletedResistance_continuous :
    Continuous (fun points :
      XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ×
      XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =>
      xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension points.1 points.2) := by
  have rowContinuous := xiCompletedResistanceRow_continuous system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    anchor extension extensionCompact
  exact ((rowContinuous.comp continuous_fst).sub (rowContinuous.comp continuous_snd)).norm.pow 2

include agreement extensionCompact in
theorem xiCompletedResistance_triangle
    (first middle last : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first last ≤
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first middle +
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension middle last := by
  let resistance := xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension
  have rowContinuous := xiCompletedResistanceRow_continuous system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    anchor extension extensionCompact
  have firstContinuous : ∀ point, Continuous (fun varying => resistance varying point) :=
    fun _ => (rowContinuous.sub continuous_const).norm.pow 2
  have secondContinuous : ∀ point, Continuous (resistance point) :=
    fun _ => (continuous_const.sub rowContinuous).norm.pow 2
  have dense := xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  refine dense.induction_on first
    (isClosed_le (firstContinuous last) ((firstContinuous middle).add continuous_const)) ?_
  intro firstVertex
  refine dense.induction_on middle
    (isClosed_le continuous_const ((secondContinuous _).add (firstContinuous last))) ?_
  intro middleVertex
  refine dense.induction_on last
    (isClosed_le (secondContinuous _) (continuous_const.add (secondContinuous _))) ?_
  intro lastVertex
  rw [xiCompletedResistance_on_skeleton system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      anchor extension agreement,
    xiCompletedResistance_on_skeleton system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      anchor extension agreement,
    xiCompletedResistance_on_skeleton system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      anchor extension agreement]
  exact xiSkeletonResistance_triangle system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair anchor firstVertex middleVertex lastVertex

end
end EIGS

#print axioms EIGS.xiCompletedResistance_on_skeleton
#print axioms EIGS.xiCompletedResistance_continuous
#print axioms EIGS.xiCompletedResistance_triangle
