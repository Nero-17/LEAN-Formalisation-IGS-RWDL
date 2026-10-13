import RequestProject.Outlook.FourColourClusterIsomorphism

/-! Distributional identification through the actual deterministic graph
realization. Incidence shapes retain both named terminals and directed edge
incidence. Source-cluster shapes remove inactive vertices and retain the full
unlabelled graph, rather than only its size or boundary statistics. -/
namespace Outlook.FourColourActualGraphLaw
open Cluster MeasureTheory ProbabilityTheory FourColourConditionalHierarchy FourColourCodingTree
open FourColourBranchingLaw FourColourGraphRealization FourColourClusterIsomorphism

def incidenceSetoid : Setoid TTN where
  r firstNetwork secondNetwork := Nonempty (TTN.IncidenceIso firstNetwork secondNetwork)
  iseqv := {
    refl := fun network => ⟨TTN.IncidenceIso.refl network⟩
    symm := fun ⟨isomorphism⟩ => ⟨isomorphism.symm⟩
    trans := fun ⟨firstIso⟩ ⟨secondIso⟩ => ⟨firstIso.trans secondIso⟩ }

def IncidenceShape := Quotient incidenceSetoid
def incidenceShape (network : TTN) : IncidenceShape := Quotient.mk incidenceSetoid network

instance : MeasurableSpace IncidenceShape := ⊤
instance : DiscreteMeasurableSpace IncidenceShape := ⟨fun _ => trivial⟩

def sourceClusterSetoid : Setoid TTN where
  r firstNetwork secondNetwork := Nonempty (TTN.sourceClusterGraph firstNetwork ≃g TTN.sourceClusterGraph secondNetwork)
  iseqv := {
    refl := fun _ => ⟨SimpleGraph.Iso.refl⟩
    symm := fun ⟨isomorphism⟩ => ⟨isomorphism.symm⟩
    trans := fun ⟨firstIso⟩ ⟨secondIso⟩ => ⟨firstIso.trans secondIso⟩ }

def SourceClusterShape := Quotient sourceClusterSetoid
def sourceClusterShape (network : TTN) : SourceClusterShape := Quotient.mk sourceClusterSetoid network

instance : MeasurableSpace SourceClusterShape := ⊤
instance : DiscreteMeasurableSpace SourceClusterShape := ⟨fun _ => trivial⟩

/-- Every finite-generation law of the actual pruned network, including its
named endpoints and directed incidence, is the independent rule-tree law
passed through the adopted deterministic realization. -/
theorem actual_retainedNetworkLaw (depth : ℕ) (parent : Fin 4) :
    (parentMeasure depth parent).map (fun configuration =>
      incidenceShape (TTN.retainedNetwork (net depth configuration) parent false)) =
      (ruleTreeLaw depth parent).map (fun tree => incidenceShape (realize depth parent tree)) := by
  have mapping : (fun configuration =>
      incidenceShape (TTN.retainedNetwork (net depth configuration) parent false)) =ᵐ[parentMeasure depth parent]
      (fun configuration => incidenceShape (realize depth parent (encode depth parent configuration))) := by
    exact ae_cond_of_forall_mem MeasurableSet.of_discrete (fun configuration condition =>
      Quotient.sound ⟨(actualRealizationIso depth parent configuration condition).symm⟩)
  rw [Measure.map_congr mapping]
  change (parentMeasure depth parent).map
    ((fun tree => incidenceShape (realize depth parent tree)) ∘ encode depth parent) = _
  rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  exact congrArg (fun law => law.map (fun tree => incidenceShape (realize depth parent tree)))
    (actual_encodedLaw_eq_ruleTreeLaw depth parent)

/-- The genuine connected cluster law of the original connected percolation
configuration is the full graph law of the adopted four-colour realization.
No inactive ambient vertices occur in either graph shape. -/
theorem actual_red_sourceClusterLaw (depth : ℕ) :
    (parentMeasure depth 0).map (fun configuration => sourceClusterShape (net depth configuration)) =
      (ruleTreeLaw depth 0).map (fun tree => sourceClusterShape (realize depth 0 tree)) := by
  have mapping : (fun configuration => sourceClusterShape (net depth configuration)) =ᵐ[parentMeasure depth 0]
      (fun configuration => sourceClusterShape (realize depth 0 (encode depth 0 configuration))) := by
    exact ae_cond_of_forall_mem MeasurableSet.of_discrete (fun configuration condition =>
      Quotient.sound ⟨(actualRedClusterIso depth configuration condition).symm⟩)
  rw [Measure.map_congr mapping]
  change (parentMeasure depth 0).map
    ((fun tree => sourceClusterShape (realize depth 0 tree)) ∘ encode depth 0) = _
  rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  exact congrArg (fun law => law.map (fun tree => sourceClusterShape (realize depth 0 tree)))
    (actual_encodedLaw_eq_ruleTreeLaw depth 0)

end Outlook.FourColourActualGraphLaw

#print axioms Outlook.FourColourActualGraphLaw.actual_retainedNetworkLaw
#print axioms Outlook.FourColourActualGraphLaw.actual_red_sourceClusterLaw
