import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Countable inverse systems of probability measures

The transition from level `n` to level `n + 1` is the regular conditional law
of the finer configuration given its coarse image. Ionescu–Tulcea constructs
the infinite path measure. The consistency assumption is only the one-step
pushforward identity; compatibility of the infinite path is proved below.
-/

namespace ProbabilityTheory.InverseSystem

open MeasureTheory ProbabilityTheory Kernel Finset Preorder

noncomputable section

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  (law : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (law n)]
  (bond : (n : ℕ) → X (n + 1) → X n)
  (measurable_bond : ∀ n, Measurable (bond n))

/-- Conditional refinement law of a configuration. -/
def refinement (n : ℕ) : Kernel (X n) (X (n + 1)) :=
  condDistrib id (bond n) (law (n + 1))

instance refinement_markov (n : ℕ) : IsMarkovKernel (refinement law bond n) := by
  unfold refinement
  infer_instance

/-- Refinement depends on the last configuration in the finite history. -/
def historyRefinement (n : ℕ) : Kernel ((i : Iic n) → X i) (X (n + 1)) :=
  (refinement law bond n).comap (fun history => history ⟨n, mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance historyRefinement_markov (n : ℕ) :
    IsMarkovKernel (historyRefinement law bond n) := by
  unfold historyRefinement
  infer_instance

/-- Infinite path measure obtained by conditional refinement. -/
def pathMeasure : Measure ((n : ℕ) → X n) :=
  Kernel.trajMeasure (law 0) (historyRefinement law bond)

instance pathMeasure_probability : IsProbabilityMeasure (pathMeasure law bond) := by
  unfold pathMeasure
  infer_instance

lemma comap_comp_measure {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (transition : Kernel β γ) (measure : Measure α)
    (projection : α → β) (measurable_projection : Measurable projection) :
    transition.comap projection measurable_projection ∘ₘ measure =
      transition ∘ₘ (measure.map projection) := by
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

lemma pathMeasure_map_zero :
    (pathMeasure law bond).map (fun path => path 0) = law 0 := by
  have restriction_law :
      (pathMeasure law bond).map (frestrictLe 0) =
        (law 0).map (MeasurableEquiv.piUnique ((fun i : Iic 0 => X i))).symm := by
    rw [pathMeasure, Kernel.trajMeasure,
      Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self, Measure.id_comp]
  have evaluation_factor : (fun path : (n : ℕ) → X n => path 0) =
      (fun history : (i : Iic 0) → X i => history ⟨0, mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0 := rfl
  rw [evaluation_factor, ← Measure.map_map (measurable_pi_apply _)
    (measurable_frestrictLe 0), restriction_law,
    Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.measurable _)]
  convert (Measure.map_id : (law 0).map id = law 0) using 1

lemma pathMeasure_next (n : ℕ) :
    (pathMeasure law bond).map (fun path => path (n + 1)) =
      refinement law bond n ∘ₘ ((pathMeasure law bond).map (fun path => path n)) := by
  have history_joint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := law 0) (κ := historyRefinement law bond) (a := n)
  have next_law := congrArg Measure.snd history_joint
  rw [Measure.snd_compProd, Measure.snd_map_prodMk] at next_law
  · change historyRefinement law bond n ∘ₘ
        ((pathMeasure law bond).map (frestrictLe n)) = _ at next_law
    rw [historyRefinement, comap_comp_measure, Measure.map_map (measurable_pi_apply _)
      (measurable_frestrictLe n)] at next_law
    exact next_law.symm
  · exact measurable_frestrictLe n

variable (consistent : ∀ n, (law (n + 1)).map (bond n) = law n)

include measurable_bond consistent

/-- Every coordinate has the prescribed law, with no temporal independence assumption. -/
theorem pathMeasure_map_eval (n : ℕ) :
    (pathMeasure law bond).map (fun path => path n) = law n := by
  induction n with
  | zero => exact pathMeasure_map_zero law bond
  | succ n induction_hypothesis =>
      rw [pathMeasure_next, induction_hypothesis, ← consistent n, refinement,
        condDistrib_comp_map (measurable_bond n).aemeasurable aemeasurable_id,
        Measure.map_id]

variable [∀ n, MeasurableEq (X n)]

/-- Conditional refinement is supported on the fibre of the coarse map. -/
theorem refinement_supported (n : ℕ) :
    ∀ᵐ coarse_configuration ∂law n,
      ∀ᵐ fine_configuration ∂refinement law bond n coarse_configuration,
        bond n fine_configuration = coarse_configuration := by
  have pair_support : ∀ᵐ pair ∂(law n ⊗ₘ refinement law bond n),
      bond n pair.2 = pair.1 := by
    rw [← consistent n, refinement, compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff ((measurable_bond n).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun ((measurable_bond n).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  exact Measure.ae_ae_of_ae_compProd pair_support

/-- Consecutive configurations of the infinite process are coarse images of one another. -/
theorem pathMeasure_bonded (n : ℕ) :
    ∀ᵐ path ∂pathMeasure law bond, bond n (path (n + 1)) = path n := by
  have last_law :
      ((pathMeasure law bond).map (frestrictLe n)).map
          (fun history => history ⟨n, mem_Iic.mpr le_rfl⟩) = law n := by
    rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe n)]
    exact pathMeasure_map_eval law bond measurable_bond consistent n
  have conditional_support := refinement_supported law bond measurable_bond consistent n
  rw [← last_law] at conditional_support
  have history_support := ae_of_ae_map (measurable_pi_apply _).aemeasurable conditional_support
  have history_joint_support :
      ∀ᵐ pair ∂((pathMeasure law bond).map (frestrictLe n) ⊗ₘ
        historyRefinement law bond n),
        bond n pair.2 = pair.1 ⟨n, mem_Iic.mpr le_rfl⟩ := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_bond n).comp measurable_snd)
        ((measurable_pi_apply (⟨n, mem_Iic.mpr le_rfl⟩ : Iic n)).comp measurable_fst))
    exact history_support
  have history_joint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := law 0) (κ := historyRefinement law bond) (a := n)
  change (pathMeasure law bond).map (frestrictLe n) ⊗ₘ historyRefinement law bond n =
    (pathMeasure law bond).map (fun path => (frestrictLe n path, path (n + 1))) at history_joint
  rw [history_joint] at history_joint_support
  exact ae_of_ae_map
    ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))).aemeasurable
    history_joint_support

/-- Countably many bonding constraints hold simultaneously on a set of full measure. -/
theorem pathMeasure_all_bonded :
    ∀ᵐ path ∂pathMeasure law bond, ∀ n, bond n (path (n + 1)) = path n := by
  exact (ae_all_iff).mpr (pathMeasure_bonded law bond measurable_bond consistent)

omit measurable_bond consistent in
/-- The inverse-limit sample space consists only of compatible paths. -/
def compatiblePaths : Set ((n : ℕ) → X n) :=
  {path | ∀ n, bond n (path (n + 1)) = path n}

omit consistent in
lemma measurableSet_compatiblePaths : MeasurableSet (compatiblePaths bond) := by
  simp only [compatiblePaths, Set.setOf_forall]
  exact MeasurableSet.iInter fun n => measurableSet_eq_fun
    ((measurable_bond n).comp (measurable_pi_apply (n + 1))) (measurable_pi_apply n)

omit measurable_bond consistent in
/-- The probability law on the actual inverse limit, rather than on all sequences. -/
def compatibleMeasure : Measure (compatiblePaths bond) :=
  (pathMeasure law bond).comap Subtype.val

/-- Including the inverse limit in the full path space recovers the constructed law. -/
theorem compatibleMeasure_map_val :
    (compatibleMeasure law bond).map Subtype.val = pathMeasure law bond := by
  rw [compatibleMeasure, map_comap_subtype_coe
    (measurableSet_compatiblePaths bond measurable_bond)]
  exact Measure.restrict_eq_self_of_ae_mem
    (pathMeasure_all_bonded law bond measurable_bond consistent)

theorem compatibleMeasure_probability : IsProbabilityMeasure (compatibleMeasure law bond) := by
  constructor
  have total_mass := congrArg (fun measure => measure Set.univ)
    (compatibleMeasure_map_val law bond measurable_bond consistent)
  dsimp only at total_mass
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ] at total_mass
  exact total_mass.trans (measure_univ : (pathMeasure law bond) Set.univ = 1)

/-- The inverse-limit coordinates have the prescribed probability laws. -/
theorem compatibleMeasure_map_eval (n : ℕ) :
    (compatibleMeasure law bond).map (fun path => path.val n) = law n := by
  change (compatibleMeasure law bond).map
    ((fun path : (n : ℕ) → X n => path n) ∘ Subtype.val) = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_subtype_coe,
    compatibleMeasure_map_val law bond measurable_bond consistent]
  exact pathMeasure_map_eval law bond measurable_bond consistent n

end
end ProbabilityTheory.InverseSystem
