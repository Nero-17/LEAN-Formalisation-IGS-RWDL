import RequestProject.Section31.EIGSMetricCompletion
import RequestProject.Section2ConcreteSpectralRadius

/-! A canonical choice of the metric data from the original rule assumptions.
The distance rate is the actual minimum usual complex spectral radius. -/

namespace EIGS

variable {K : ℕ}

structure XiPathMetricData (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected) where
  lengths : Fin K → ℝ
  lengthsPositive : ∀ colour, 0 < lengths colour
  ratePositive : 0 < system.distanceSpectralRadius ruleConnected
  normalized : (∑ colour, lengths colour) = 1
  eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths =
    system.distanceSpectralRadius ruleConnected • lengths

noncomputable def xiPathMetricDataOfRules (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    XiPathMetricData system ruleConnected := by
  let existence := system.metricLengths_spectral_eigenpair ruleConnected rulesLoopless rulesUnique distancePositive
  exact {
    lengths := Classical.choose existence
    lengthsPositive := (Classical.choose_spec existence).1
    ratePositive := (Classical.choose_spec existence).2.1
    normalized := (Classical.choose_spec existence).2.2.1
    eigenpair := (Classical.choose_spec existence).2.2.2 }

namespace XiPathMetricData

variable {system : EIGSData K}
    {ruleConnected : ∀ colour, (ruleSG system colour).Connected}

noncomputable def LimitSpace (parameters : XiPathMetricData system ruleConnected) : Type :=
  XiMetricCompletion system ruleConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius ruleConnected) parameters.ratePositive parameters.eigenpair

noncomputable instance (parameters : XiPathMetricData system ruleConnected) :
    MetricSpace parameters.LimitSpace := by
  unfold LimitSpace
  infer_instance

instance (parameters : XiPathMetricData system ruleConnected) : CompleteSpace parameters.LimitSpace := by
  unfold LimitSpace
  infer_instance

noncomputable def vertexEmbedding (parameters : XiPathMetricData system ruleConnected) (level : ℕ) :
    XiVtx system level → parameters.LimitSpace :=
  xiCompletionEmbedding system ruleConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius ruleConnected) parameters.ratePositive parameters.eigenpair level

theorem vertexEmbedding_isometry (parameters : XiPathMetricData system ruleConnected) (level : ℕ) :
    letI := xiLevelMetricSpace system ruleConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius ruleConnected) parameters.ratePositive level
    Isometry (parameters.vertexEmbedding level) :=
  xiCompletionEmbedding_isometry system ruleConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius ruleConnected) parameters.ratePositive parameters.eigenpair level

end XiPathMetricData

end EIGS

#print axioms EIGS.xiPathMetricDataOfRules
#print axioms EIGS.XiPathMetricData.vertexEmbedding_isometry
