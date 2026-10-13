import RequestProject.Outlook.FourColourLiteralMetricLaw
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! A genuine measurable GH-class path-limit functional and the limiting
literal substitution law. Divergent paths receive the fixed default singleton
GH class. The actual pathwise compact completion and the existing complete
joint GH-class law determine the same limiting probability law. No vertex
measure or GHP statement is introduced. -/
noncomputable section
namespace Outlook.FourColourLiteralLimitLaw
open Cluster Reduced MeasureTheory Filter Topology
open FourColourRandomGH FourColourLiteralMetricLaw
open FourColourCodingTree FourColourInfiniteProcess

/-- The measurable locus of sequences having a genuine GH-space limit. -/
def convergentGHPaths : Set (ℕ → GromovHausdorff.GHSpace) :=
  {path | ∃ limit, Tendsto path atTop (𝓝 limit)}

theorem measurableSet_convergentGHPaths : MeasurableSet convergentGHPaths :=
  MeasureTheory.measurableSet_exists_tendsto
    (fun depth => (measurable_pi_apply depth :
      Measurable (fun path : ℕ → GromovHausdorff.GHSpace => path depth)))

/-- The pinned default GHSpace point is represented by a singleton compact set. -/
def defaultGHClass : GromovHausdorff.GHSpace := default

/-- On convergent paths take the genuine limit; elsewhere take one fixed class. -/
def ghPathLimit (path : ℕ → GromovHausdorff.GHSpace) : GromovHausdorff.GHSpace := by
  classical
  exact if path ∈ convergentGHPaths then limUnder atTop path else defaultGHClass

theorem measurable_ghPathLimit : Measurable ghPathLimit := by
  classical
  have limitMeasurable : Measurable
      (fun path : ℕ → GromovHausdorff.GHSpace => limUnder atTop path) :=
    (StronglyMeasurable.limUnder (l := atTop)
      (fun depth => (measurable_pi_apply depth :
        Measurable (fun path : ℕ → GromovHausdorff.GHSpace => path depth)).stronglyMeasurable)).measurable
  exact Measurable.ite measurableSet_convergentGHPaths limitMeasurable measurable_const

theorem ghPathLimit_eq_of_tendsto (path : ℕ → GromovHausdorff.GHSpace)
    (limit : GromovHausdorff.GHSpace) (convergence : Tendsto path atTop (𝓝 limit)) :
    ghPathLimit path = limit := by
  have member : path ∈ convergentGHPaths := ⟨limit, convergence⟩
  rw [ghPathLimit, if_pos member]
  exact convergence.limUnder_eq

theorem ghPathLimit_eq_default (path : ℕ → GromovHausdorff.GHSpace)
    (divergent : ¬ ∃ limit, Tendsto path atTop (𝓝 limit)) :
    ghPathLimit path = defaultGHClass := by
  have notMember : path ∉ convergentGHPaths := divergent
  rw [ghPathLimit, if_neg notMember]

theorem tendsto_ghPathLimit (path : ℕ → GromovHausdorff.GHSpace)
    (convergent : path ∈ convergentGHPaths) :
    Tendsto path atTop (𝓝 (ghPathLimit path)) := by
  obtain ⟨limit, convergence⟩ := convergent
  rw [ghPathLimit_eq_of_tendsto path limit convergence]
  exact convergence

/-- The path functional recovers the actual completion class on every sample. -/
theorem actual_ghPathLimit (cluster : NestedCluster) :
    ghPathLimit (actualGHPath cluster) = actualCompactGH cluster :=
  ghPathLimit_eq_of_tendsto _ _ (actualFiniteGH_tendsto cluster)

/-- This random class is defined on all literal rule-tree paths, with the fixed
default outside the measurable convergence locus. -/
def literalCompactGH (path : (depth : ℕ) → RuleTree depth) : GromovHausdorff.GHSpace :=
  ghPathLimit (literalGHPath path)

theorem measurable_literalCompactGH : Measurable literalCompactGH :=
  measurable_ghPathLimit.comp measurable_literalGHPath

/-- The full actual GH-path law is supported on the genuine convergence locus. -/
theorem actual_gh_path_ae_convergent :
    ∀ᵐ path ∂nestedClusterMeasure.map actualGHPath, path ∈ convergentGHPaths := by
  apply (ae_map_iff measurable_actualGHPath.aemeasurable measurableSet_convergentGHPaths).mpr
  exact Filter.Eventually.of_forall (fun cluster =>
    ⟨actualCompactGH cluster, actualFiniteGH_tendsto cluster⟩)

/-- Convergence on the rule-tree side follows from the complete joint path
law, with no pointwise convergence or geometry assumption on literal paths. -/
theorem literal_gh_path_ae_convergent :
    ∀ᵐ path ∂ruleTreePathMeasure 0, literalGHPath path ∈ convergentGHPaths := by
  have supported := actual_gh_path_ae_convergent
  rw [nested_actual_literal_full_gh_law] at supported
  exact ae_of_ae_map measurable_literalGHPath.aemeasurable supported

theorem literal_gh_ae_limit :
    ∀ᵐ path ∂ruleTreePathMeasure 0,
      Tendsto (literalGHPath path) atTop (𝓝 (literalCompactGH path)) := by
  filter_upwards [literal_gh_path_ae_convergent] with path convergent
  exact tendsto_ghPathLimit (literalGHPath path) convergent

/-- The literal limiting class is the actual compact completion class under
the existing coupled encoding, on the original common full-measure event. -/
theorem actual_encoded_literal_limit :
    ∀ᵐ cluster ∂nestedClusterMeasure,
      literalCompactGH (nestedEncodedSequence cluster) = actualCompactGH cluster := by
  filter_upwards [actual_literal_gh_path] with cluster equality
  change actualGHPath cluster = literalGHPath (nestedEncodedSequence cluster) at equality
  change ghPathLimit (literalGHPath (nestedEncodedSequence cluster)) = actualCompactGH cluster
  rw [← equality]
  exact actual_ghPathLimit cluster

def literalCompactSourceLaw : Measure GromovHausdorff.GHSpace :=
  (ruleTreePathMeasure 0).map literalCompactGH

instance literalCompactSourceLaw_probability : IsProbabilityMeasure literalCompactSourceLaw :=
  Measure.isProbabilityMeasure_map measurable_literalCompactGH.aemeasurable

/-- The true limiting probability laws agree. This is the measurable image
of the already-proved complete joint finite-level GH-class law. -/
theorem actual_literal_compact_source_law :
    compactSourceLaw = literalCompactSourceLaw := by
  have equality := congrArg
    (fun measure : Measure (ℕ → GromovHausdorff.GHSpace) => measure.map ghPathLimit)
    nested_actual_literal_full_gh_law
  dsimp only at equality
  rw [Measure.map_map measurable_ghPathLimit measurable_actualGHPath,
    Measure.map_map measurable_ghPathLimit measurable_literalGHPath] at equality
  have actualMapping : ghPathLimit ∘ actualGHPath = actualCompactGH := funext actual_ghPathLimit
  rw [actualMapping] at equality
  exact equality

end Outlook.FourColourLiteralLimitLaw

#print axioms Outlook.FourColourLiteralLimitLaw.measurableSet_convergentGHPaths
#print axioms Outlook.FourColourLiteralLimitLaw.measurable_ghPathLimit
#print axioms Outlook.FourColourLiteralLimitLaw.ghPathLimit_eq_of_tendsto
#print axioms Outlook.FourColourLiteralLimitLaw.actual_ghPathLimit
#print axioms Outlook.FourColourLiteralLimitLaw.measurable_literalCompactGH
#print axioms Outlook.FourColourLiteralLimitLaw.literal_gh_ae_limit
#print axioms Outlook.FourColourLiteralLimitLaw.actual_encoded_literal_limit
#print axioms Outlook.FourColourLiteralLimitLaw.actual_literal_compact_source_law
