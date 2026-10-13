import RequestProject.Cluster.InfiniteConsequences
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Equality with the independently constructed full reduced network law -/

namespace Cluster

open MeasureTheory ProbabilityTheory Reduced Finset Preorder

noncomputable section

private theorem measure_eq_of_initial_restrictions
    (first_measure second_measure : Measure (ℕ → ℝ)) [IsFiniteMeasure second_measure]
    (prefix_laws : ∀ n, first_measure.map (frestrictLe n) =
      second_measure.map (frestrictLe n)) : first_measure = second_measure := by
  let family : (indices : Finset ℕ) → Measure (indices → ℝ) :=
    fun indices => second_measure.map indices.restrict
  have projective_family : IsProjectiveMeasureFamily (α := fun _ : ℕ => ℝ) family := by
    exact isProjectiveMeasureFamily_map_restrict
      (P := second_measure) (X := fun n trajectory => trajectory n)
      (fun n => (measurable_pi_apply n).aemeasurable)
  haveI : ∀ indices, IsFiniteMeasure (family indices) := fun indices => by
    dsimp [family]
    infer_instance
  have first_projective : IsProjectiveLimit (α := fun _ : ℕ => ℝ) first_measure family := by
    apply (isProjectiveLimit_nat_iff projective_family first_measure).mpr
    intro n
    exact prefix_laws n
  have second_projective : IsProjectiveLimit (α := fun _ : ℕ => ℝ) second_measure family :=
    fun _ => rfl
  exact first_projective.unique second_projective

private theorem nestedTree_window : ∀ (n : ℕ) (tree : NestedTree),
    rwin n (nestedTree n tree) =
      fun index : Fin (n + 1) => Rres index.val (nestedTree index.val tree) := by
  intro n
  induction n with
  | zero =>
      intro tree
      funext index
      have index_zero : index = 0 := Fin.eq_zero index
      subst index
      rfl
  | succ n induction_hypothesis =>
      intro tree
      funext index
      refine Fin.lastCases ?_ (fun earlier_index => ?_) index
      · simp only [rwin_last, Fin.val_last]
      · rw [rwin_succ, Fin.snoc_castSucc, nestedTree_bonded, induction_hypothesis]
        rfl

private def initialWindow (n : ℕ) (finite_tree : RConf n) : (Iic n → ℝ) :=
  fun index => rwin n finite_tree
    ⟨index.val, Nat.lt_succ_of_le (mem_Iic.mp index.property)⟩

private theorem initial_window_identity (n : ℕ) (tree : NestedTree) :
    frestrictLe n (fun depth => Rres depth (nestedTree depth tree)) =
      initialWindow n (nestedTree n tree) := by
  funext index
  exact (congrFun (nestedTree_window n tree)
    ⟨index.val, Nat.lt_succ_of_le (mem_Iic.mp index.property)⟩).symm

private theorem initial_window_law (probability : Measure NestedTree)
    (n : ℕ) (level_law : probability.map (nestedTree n) =
      rMeasure (pdiamond pc) (pseries pc) n) :
    probability.map (fun tree =>
      frestrictLe n (fun depth => Rres depth (nestedTree depth tree))) =
        (rMeasure (pdiamond pc) (pseries pc) n).map (initialWindow n) := by
  have function_identity : (fun tree =>
      frestrictLe n (fun depth => Rres depth (nestedTree depth tree))) =
        initialWindow n ∘ nestedTree n :=
    funext (initial_window_identity n)
  rw [function_identity, ← Measure.map_map Measurable.of_discrete (measurable_nestedTree n),
    level_law]

/-- The reduction image and independently constructed tree have the same full resistance law. -/
theorem nested_reduced_full_process_law :
    (nestedClusterMeasure.map nestedClusterTree).map
      (fun tree depth => Rres depth (nestedTree depth tree)) =
    (nestedTreeMeasure (pdiamond pc) (pseries pc) pdiamond_pc_nonneg
      pseries_pc_nonneg pseries_add_pdiamond_pc).map
        (fun tree depth => Rres depth (nestedTree depth tree)) := by
  haveI := nestedTreeMeasure_probability pdiamond_pc_nonneg pseries_pc_nonneg
    pseries_add_pdiamond_pc
  have measurable_sequence : Measurable
      (fun tree depth => Rres depth (nestedTree depth tree)) :=
    measurable_pi_lambda _ (fun depth =>
      (Measurable.of_discrete : Measurable (Rres depth)).comp (measurable_nestedTree depth))
  apply measure_eq_of_initial_restrictions
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) measurable_sequence,
    Measure.map_map (measurable_frestrictLe n) measurable_sequence]
  change (nestedClusterMeasure.map nestedClusterTree).map
      (fun tree => frestrictLe n (fun depth => Rres depth (nestedTree depth tree))) =
    (nestedTreeMeasure (pdiamond pc) (pseries pc) pdiamond_pc_nonneg
      pseries_pc_nonneg pseries_add_pdiamond_pc).map
        (fun tree => frestrictLe n (fun depth => Rres depth (nestedTree depth tree)))
  have image_level_law : (nestedClusterMeasure.map nestedClusterTree).map (nestedTree n) =
      rMeasure (pdiamond pc) (pseries pc) n := by
    rw [Measure.map_map (measurable_nestedTree n) measurable_nestedClusterTree]
    exact nestedClusterTree_law n
  rw [initial_window_law _ n image_level_law,
    initial_window_law _ n
      (nestedTree_law pdiamond_pc_nonneg pseries_pc_nonneg pseries_add_pdiamond_pc n)]

/-- Proposition 4.2 for the two separately constructed infinite actual network processes. -/
theorem nested_cluster_full_network_law :
    nestedClusterMeasure.map
      (fun cluster depth => (net depth (nestedConfiguration depth cluster)).effRes.toReal) =
    (nestedTreeMeasure (pdiamond pc) (pseries pc) pdiamond_pc_nonneg
      pseries_pc_nonneg pseries_add_pdiamond_pc).map
        (fun tree depth => (treeNetwork depth (nestedTree depth tree)).effRes.toReal) := by
  apply nested_cluster_network_process.trans
  simpa only [treeNetwork_toReal_effRes] using nested_reduced_full_process_law

end
end Cluster
