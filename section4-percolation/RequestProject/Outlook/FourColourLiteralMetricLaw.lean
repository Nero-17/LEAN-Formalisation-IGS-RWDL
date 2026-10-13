import RequestProject.Outlook.FourColourRandomGH
import RequestProject.Outlook.FourColourInfiniteGraphLaw

/-! Genuine normalized source metrics on literal adopted substitution graphs.
Graph isomorphisms are promoted to metric isometries by preserving actual
shortest walks. The finite and full joint GH-class laws retain the original
critical terminal-connected conditioning. No metric-measure assertion is made. -/
noncomputable section
namespace Outlook.FourColourLiteralMetricLaw
open Cluster Reduced MeasureTheory ProbabilityTheory
open FourColourActualMesh FourColourRandomGH
open FourColourConditionalHierarchy FourColourCodingTree FourColourBranchingLaw
open FourColourLiteralRealization FourColourInfiniteProcess

theorem source_ambient_reachable (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex}) :
    network.underlyingGraph.Reachable first.1 last.1 :=
  (TTN.edgePath_iff_reachable _ _ _).mp
    (TTN.edgePath_trans (TTN.edgePath_symm first.2) last.2)

/-- Every actual ambient walk starting in the source component stays there. -/
theorem source_walk_support (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex})
    (walk : network.underlyingGraph.Walk first.1 last.1)
    (vertex : network.V) (member : vertex ∈ walk.support) :
    network.EdgePath network.a vertex := by
  classical
  apply (TTN.edgePath_iff_reachable _ _ _).mpr
  exact ((TTN.edgePath_iff_reachable _ _ _).mp first.2).trans
    (walk.takeUntil vertex member).reachable

/-- Inducing a real source-component walk does not change either endpoint. -/
def sourceInducedWalk (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex})
    (walk : network.underlyingGraph.Walk first.1 last.1) :
    (TTN.sourceClusterGraph network).Walk first last :=
  walk.induce {vertex | network.EdgePath network.a vertex}
    (source_walk_support network first last walk)

theorem sourceInducedWalk_length (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex})
    (walk : network.underlyingGraph.Walk first.1 last.1) :
    (sourceInducedWalk network first last walk).length = walk.length := by
  have equality := congrArg
    (fun path : network.underlyingGraph.Walk first.1 last.1 => path.length)
    (walk.map_induce (source_walk_support network first last walk))
  simpa only [SimpleGraph.Walk.length_map] using equality

theorem source_induced_reachable (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex}) :
    (TTN.sourceClusterGraph network).Reachable first last := by
  obtain ⟨walk⟩ := source_ambient_reachable network first last
  exact ⟨sourceInducedWalk network first last walk⟩

/-- The actual induced source graph and its ambient network have identical
shortest-walk distances on the source component. Both pairs are reachable. -/
theorem source_induced_dist_eq_ambient (network : TTN)
    (first last : {vertex : network.V // network.EdgePath network.a vertex}) :
    (TTN.sourceClusterGraph network).dist first last =
      network.underlyingGraph.dist first.1 last.1 := by
  apply Nat.le_antisymm
  · obtain ⟨walk, lengthEqual⟩ :=
      (source_ambient_reachable network first last).exists_walk_length_eq_dist
    calc
      _ ≤ (sourceInducedWalk network first last walk).length :=
        SimpleGraph.dist_le _
      _ = walk.length := sourceInducedWalk_length network first last walk
      _ = _ := lengthEqual
  · obtain ⟨walk, lengthEqual⟩ :=
      (source_induced_reachable network first last).exists_walk_length_eq_dist
    have bound := SimpleGraph.dist_le
      (walk.map (SimpleGraph.Embedding.induce
        {vertex | network.EdgePath network.a vertex}).toHom)
    simpa only [SimpleGraph.Walk.length_map, lengthEqual] using bound

/-- A genuine graph isomorphism preserves reachable shortest-walk distances. -/
theorem graphIso_dist_eq {firstType secondType : Type*}
    {firstGraph : SimpleGraph firstType} {secondGraph : SimpleGraph secondType}
    (isomorphism : firstGraph ≃g secondGraph) (first last : firstType)
    (reachable : firstGraph.Reachable first last) :
    secondGraph.dist (isomorphism first) (isomorphism last) = firstGraph.dist first last := by
  apply Nat.le_antisymm
  · obtain ⟨walk, lengthEqual⟩ := reachable.exists_walk_length_eq_dist
    have bound := SimpleGraph.dist_le (walk.map isomorphism.toHom)
    simpa only [SimpleGraph.Walk.length_map, lengthEqual] using bound
  · obtain ⟨walk, lengthEqual⟩ :=
      (reachable.map isomorphism.toHom).exists_walk_length_eq_dist
    have bound : firstGraph.dist (isomorphism.symm (isomorphism first))
        (isomorphism.symm (isomorphism last)) ≤ walk.length := by
      simpa only [SimpleGraph.Walk.length_map] using
        SimpleGraph.dist_le (walk.map isomorphism.symm.toHom)
    simpa only [lengthEqual, RelIso.symm_apply_apply] using bound

theorem sourceClusterIso_ambient_dist {firstNetwork secondNetwork : TTN}
    (isomorphism : TTN.sourceClusterGraph firstNetwork ≃g TTN.sourceClusterGraph secondNetwork)
    (first last : {vertex : firstNetwork.V // firstNetwork.EdgePath firstNetwork.a vertex}) :
    secondNetwork.underlyingGraph.dist (isomorphism first).1 (isomorphism last).1 =
      firstNetwork.underlyingGraph.dist first.1 last.1 := by
  calc
    _ = (TTN.sourceClusterGraph secondNetwork).dist (isomorphism first) (isomorphism last) :=
      (source_induced_dist_eq_ambient secondNetwork _ _).symm
    _ = (TTN.sourceClusterGraph firstNetwork).dist first last :=
      graphIso_dist_eq isomorphism first last (source_induced_reachable firstNetwork first last)
    _ = _ := source_induced_dist_eq_ambient firstNetwork first last

/-- A separate carrier for arbitrary actual network source components. ULift
keeps its metric instance distinct from the existing Conf-indexed source metric. -/
def NetworkSourceSpace (_depth : ℕ) (network : TTN) : Type :=
  ULift {vertex : network.V // network.EdgePath network.a vertex}

instance networkSourceFinite (depth : ℕ) (network : TTN) :
    Finite (NetworkSourceSpace depth network) := by
  change Finite (ULift {vertex : network.V // network.EdgePath network.a vertex})
  infer_instance

instance networkSourceNonempty (depth : ℕ) (network : TTN) :
    Nonempty (NetworkSourceSpace depth network) :=
  ⟨⟨⟨network.a, TTN.edgePath_self _ _⟩⟩⟩

instance networkSourceMetricSpace (depth : ℕ) (network : TTN) :
    MetricSpace (NetworkSourceSpace depth network) where
  dist first last := distanceScale depth * (network.underlyingGraph.dist first.down.1 last.down.1 : ℝ)
  dist_self := by
    intro vertex
    rw [SimpleGraph.dist_self]
    simp
  dist_comm := by
    intro first last
    rw [SimpleGraph.dist_comm]
  dist_triangle := by
    intro first middle last
    have bound := (source_ambient_reachable network first.down middle.down).dist_triangle_left last.down.1
    have realBound : (network.underlyingGraph.dist first.down.1 last.down.1 : ℝ) ≤
        (network.underlyingGraph.dist first.down.1 middle.down.1 : ℝ) +
        (network.underlyingGraph.dist middle.down.1 last.down.1 : ℝ) := by
      exact_mod_cast bound
    calc
      _ ≤ distanceScale depth *
          ((network.underlyingGraph.dist first.down.1 middle.down.1 : ℝ) +
           (network.underlyingGraph.dist middle.down.1 last.down.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left realBound (le_of_lt (distanceScale_pos depth))
      _ = _ := mul_add _ _ _
  eq_of_dist_eq_zero := by
    intro first last equality
    have realZero : (network.underlyingGraph.dist first.down.1 last.down.1 : ℝ) = 0 :=
      (mul_eq_zero.mp equality).resolve_left (ne_of_gt (distanceScale_pos depth))
    have naturalZero : network.underlyingGraph.dist first.down.1 last.down.1 = 0 := by
      exact_mod_cast realZero
    apply Equiv.ulift.injective
    apply Subtype.ext
    exact (source_ambient_reachable network first.down last.down).dist_eq_zero_iff.mp naturalZero

instance networkSourceCompact (depth : ℕ) (network : TTN) :
    CompactSpace (NetworkSourceSpace depth network) := by infer_instance

/-- The source graph isomorphism itself, with its proved exact normalized
distance preservation; no isometry is a premise. -/
def sourceClusterMetricIso (depth : ℕ) {firstNetwork secondNetwork : TTN}
    (isomorphism : TTN.sourceClusterGraph firstNetwork ≃g TTN.sourceClusterGraph secondNetwork) :
    NetworkSourceSpace depth firstNetwork ≃ᵢ NetworkSourceSpace depth secondNetwork where
  toEquiv := Equiv.ulift.trans (isomorphism.toEquiv.trans Equiv.ulift.symm)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro first last
    change distanceScale depth *
        (secondNetwork.underlyingGraph.dist (isomorphism first.down).1 (isomorphism last.down).1 : ℝ) =
      distanceScale depth * (firstNetwork.underlyingGraph.dist first.down.1 last.down.1 : ℝ)
    rw [sourceClusterIso_ambient_dist isomorphism]

/-- Identification with the previously constructed actual Conf-indexed metric. -/
def actualSourceMetricIso (depth : ℕ) (configuration : Conf depth) :
    SourceSpace depth configuration ≃ᵢ NetworkSourceSpace depth (net depth configuration) where
  toEquiv := Equiv.ulift.symm
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro first last
    rfl

def networkSourceGH (depth : ℕ) (network : TTN) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace (NetworkSourceSpace depth network)

theorem sourceClusterIso_gh_eq (depth : ℕ) {firstNetwork secondNetwork : TTN}
    (isomorphism : TTN.sourceClusterGraph firstNetwork ≃g TTN.sourceClusterGraph secondNetwork) :
    networkSourceGH depth firstNetwork = networkSourceGH depth secondNetwork :=
  GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
    ⟨sourceClusterMetricIso depth isomorphism⟩

theorem actualSourceGH_eq_network (depth : ℕ) (configuration : Conf depth) :
    finiteSourceGH depth configuration = networkSourceGH depth (net depth configuration) :=
  GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
    ⟨actualSourceMetricIso depth configuration⟩

def literalSourceGH (depth : ℕ) (tree : RuleTree depth) : GromovHausdorff.GHSpace :=
  networkSourceGH depth (literalRealize depth 0 tree)

theorem measurable_literalSourceGH (depth : ℕ) : Measurable (literalSourceGH depth) :=
  Measurable.of_discrete

/-- The actual red-source isomorphism now gives equality of genuine normalized
metric isometry classes, retaining its exact connection condition. -/
theorem actual_literal_source_gh_eq (depth : ℕ) (configuration : Conf depth)
    (connected : configuration ∈ parentEvent depth 0) :
    finiteSourceGH depth configuration = literalSourceGH depth (encode depth 0 configuration) := by
  calc
    _ = networkSourceGH depth (net depth configuration) := actualSourceGH_eq_network depth configuration
    _ = networkSourceGH depth (literalRealize depth 0 (encode depth 0 configuration)) :=
      (sourceClusterIso_gh_eq depth (literalRedClusterIso depth configuration connected)).symm
    _ = _ := rfl

theorem actual_literal_source_gh_law (depth : ℕ) :
    (parentMeasure depth 0).map (finiteSourceGH depth) =
      (ruleTreeLaw depth 0).map (literalSourceGH depth) := by
  have mapping : finiteSourceGH depth =ᵐ[parentMeasure depth 0]
      literalSourceGH depth ∘ encode depth 0 := by
    exact ae_cond_of_forall_mem MeasurableSet.of_discrete
      (fun configuration condition => actual_literal_source_gh_eq depth configuration condition)
  rw [Measure.map_congr mapping,
    ← Measure.map_map (measurable_literalSourceGH depth) Measurable.of_discrete]
  exact congrArg (fun law => law.map (literalSourceGH depth))
    (actual_encodedLaw_eq_ruleTreeLaw depth 0)

/-- The original coupled critical process has the finite literal normalized
source metric law, rather than merely its unlabelled graph law. -/
theorem nested_actual_literal_finite_gh_law (depth : ℕ) :
    nestedClusterMeasure.map (actualFiniteGH depth) =
      (ruleTreeLaw depth 0).map (literalSourceGH depth) := by
  rw [actual_finite_gh_law]
  change (parentMeasure depth 0).map (finiteSourceGH depth) = _
  exact actual_literal_source_gh_law depth

def literalGHPath (path : (depth : ℕ) → RuleTree depth) (depth : ℕ) : GromovHausdorff.GHSpace :=
  literalSourceGH depth (path depth)

theorem measurable_literalGHPath : Measurable literalGHPath :=
  measurable_pi_lambda _ (fun depth =>
    (measurable_literalSourceGH depth).comp (measurable_pi_apply depth))

theorem actual_literal_gh_path :
    actualGHPath =ᵐ[nestedClusterMeasure] literalGHPath ∘ nestedEncodedSequence := by
  filter_upwards [nestedConfiguration_connected] with cluster connected
  funext depth
  have admissible : nestedConfiguration depth cluster ∈ parentEvent depth 0 := by
    change conn depth (nestedConfiguration depth cluster) = true
    exact connected depth
  exact actual_literal_source_gh_eq depth (nestedConfiguration depth cluster) admissible

/-- Equality of the complete joint metric-class sequence laws. It uses the
actual coherent encoding process, and does not posit independent generations. -/
theorem nested_actual_literal_full_gh_law :
    nestedClusterMeasure.map actualGHPath =
      (ruleTreePathMeasure 0).map literalGHPath := by
  rw [Measure.map_congr actual_literal_gh_path,
    ← Measure.map_map measurable_literalGHPath measurable_nestedEncodedSequence,
    nested_encoded_full_process_law]

theorem nested_actual_literal_joint_gh_law (indices : Finset ℕ) :
    nestedClusterMeasure.map (fun cluster => indices.restrict (actualGHPath cluster)) =
      (ruleTreePathMeasure 0).map (fun path => indices.restrict (literalGHPath path)) := by
  have measurable_restriction : Measurable
      (indices.restrict : (ℕ → GromovHausdorff.GHSpace) → (indices → GromovHausdorff.GHSpace)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply index.val)
  have equality := congrArg (fun measure => measure.map indices.restrict)
    nested_actual_literal_full_gh_law
  dsimp only at equality
  rw [Measure.map_map measurable_restriction measurable_actualGHPath,
    Measure.map_map measurable_restriction measurable_literalGHPath] at equality
  exact equality

end Outlook.FourColourLiteralMetricLaw

#print axioms Outlook.FourColourLiteralMetricLaw.sourceInducedWalk_length
#print axioms Outlook.FourColourLiteralMetricLaw.source_induced_dist_eq_ambient
#print axioms Outlook.FourColourLiteralMetricLaw.graphIso_dist_eq
#print axioms Outlook.FourColourLiteralMetricLaw.sourceClusterMetricIso
#print axioms Outlook.FourColourLiteralMetricLaw.actual_literal_source_gh_eq
#print axioms Outlook.FourColourLiteralMetricLaw.nested_actual_literal_finite_gh_law
#print axioms Outlook.FourColourLiteralMetricLaw.nested_actual_literal_full_gh_law
#print axioms Outlook.FourColourLiteralMetricLaw.nested_actual_literal_joint_gh_law
