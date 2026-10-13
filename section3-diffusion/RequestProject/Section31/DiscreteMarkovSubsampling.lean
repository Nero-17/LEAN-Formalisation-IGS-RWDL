import RequestProject.Section31.DiscreteMarkovTrajectory

/-! Joint-law input for discrete Markov subsampling. The future endpoint after
an arbitrary block is represented by an actual kernel power, jointly with the
entire preceding finite history. Full infinite subsampling consistency still
requires the sampled-prefix induction and projective-limit uniqueness step;
it is not inferred here from single-coordinate marginal agreement. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

def sampleEvery (stride : ℕ) (path : ℕ → X) : ℕ → X := fun index => path (stride * index)

theorem sampleEvery_measurable (stride : ℕ) : Measurable (sampleEvery (X := X) stride) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

theorem sampledPathLaw_isProbability (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (stride : ℕ) :
    IsProbabilityMeasure ((pathLaw kernel initial).map (sampleEvery stride)) :=
  Measure.isProbabilityMeasure_map (sampleEvery_measurable stride).aemeasurable

instance kernelPower_isMarkov (kernel : Kernel X X) [IsMarkovKernel kernel] (index : ℕ) :
    IsMarkovKernel (kernel ^ index) := by
  induction index with
  | zero => change IsMarkovKernel (Kernel.id : Kernel X X); infer_instance
  | succ index inductionHypothesis =>
    letI : IsMarkovKernel (kernel ^ index) := inductionHypothesis
    rw [Nat.add_comm index 1, Kernel.pow_add, pow_one]
    infer_instance

theorem traj_coordinate_at_start (kernel : Kernel X X) [IsMarkovKernel kernel] (start : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map (fun path => path start) =
      Kernel.deterministic
        (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  have factor : (fun path : ℕ → X => path start) =
      (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe start := rfl
  rw [factor, Kernel.map_comp_right _ (measurable_frestrictLe start) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map (measurable_pi_apply _)]

theorem traj_coordinate_after_succ (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start offset : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
        (fun path => path (start + (offset + 1))) =
      kernel ∘ₖ (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
        (fun path => path (start + offset)) := by
  have factor : (fun path : ℕ → X => path (start + offset)) =
      (fun history : Finset.Iic (start + offset) → X =>
        history ⟨start + offset, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe (start + offset) := rfl
  rw [← Nat.add_assoc]
  calc
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
        (fun path => path (start + offset + 1)) =
        (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) (start + offset) ∘ₖ
          Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) start (start + offset)).map
          (fun path => path (start + offset + 1)) := by
      rw [Kernel.traj_comp_partialTraj (Nat.le_add_right start offset)]
    _ = historyStep kernel (start + offset) ∘ₖ
        Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) start (start + offset) := by
      rw [Kernel.map_comp, Kernel.map_traj_succ_self]
    _ = kernel ∘ₖ (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) start
        (start + offset)).map (fun history : Finset.Iic (start + offset) → X =>
          history ⟨start + offset, Finset.mem_Iic.mpr le_rfl⟩) := by
      exact (Kernel.comp_map
        (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) start (start + offset)) kernel
        (f := fun history : Finset.Iic (start + offset) → X =>
          history ⟨start + offset, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)).symm
    _ = kernel ∘ₖ (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
        (fun path => path (start + offset)) := by
      rw [factor, Kernel.map_comp_right _ (measurable_frestrictLe (start + offset))
        (measurable_pi_apply _), Kernel.traj_map_frestrictLe]

theorem traj_block_endpoint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start offset : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
        (fun path => path (start + offset)) =
      (kernel ^ offset).comap
        (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  induction offset with
  | zero =>
    rw [Nat.add_zero, traj_coordinate_at_start, pow_zero]
    apply Kernel.ext
    intro history
    rfl
  | succ offset inductionHypothesis =>
    rw [traj_coordinate_after_succ, inductionHypothesis, pow_succ']
    apply Kernel.ext
    intro history
    rfl

theorem traj_history_endpoint_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start offset : ℕ) (initialHistory : Finset.Iic 0 → X) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
        (fun path => (frestrictLe start path, path (start + offset))) =
      Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start initialHistory ⊗ₘ
        (kernel ^ offset).comap
          (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) := by
  have joint := Kernel.partialTraj_compProd_traj (κ := historyStep kernel)
    (X := fun _ : ℕ => X) (Nat.zero_le start) initialHistory
  calc
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
        (fun path => (frestrictLe start path, path (start + offset))) =
        ((Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
          (fun path => (frestrictLe start path, path))).map
          (Prod.map id (fun path : ℕ → X => path (start + offset))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start initialHistory ⊗ₘ
        Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
          (Prod.map id (fun path : ℕ → X => path (start + offset))) := by rw [← joint]
    _ = Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start initialHistory ⊗ₘ
        (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
          (fun path => path (start + offset)) := by
      rw [Measure.compProd_map (measurable_pi_apply _)]
    _ = _ := by rw [traj_block_endpoint]

theorem pathLaw_dirac_eq_traj (kernel : Kernel X X) [IsMarkovKernel kernel] (point : X) :
    pathLaw kernel (Measure.dirac point) =
      Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 (fun _ => point) := by
  unfold pathLaw
  rw [Measure.map_dirac (by fun_prop), Measure.dirac_bind
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).measurable]

theorem traj_history_endpoint_joint_kernel (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start offset : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map
        (fun path => (frestrictLe start path, path (start + offset))) =
      (Kernel.id ×ₖ (kernel ^ offset).comap
        (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)) ∘ₖ
        Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start := by
  apply Kernel.ext
  intro initialHistory
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comp_apply, ← Measure.compProd_eq_comp_prod]
  exact traj_history_endpoint_joint kernel start offset initialHistory

theorem pathLaw_history_endpoint_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [SFinite initial] (start offset : ℕ) :
    (pathLaw kernel initial).map (fun path => (frestrictLe start path, path (start + offset))) =
      (pathLaw kernel initial).map (frestrictLe start) ⊗ₘ
        (kernel ^ offset).comap
          (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) := by
  unfold pathLaw
  rw [Measure.map_comp _ _ (by fun_prop), traj_history_endpoint_joint_kernel,
    ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_frestrictLe start), Kernel.traj_map_frestrictLe]

theorem pathLaw_dirac_history_endpoint_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (point : X) (start offset : ℕ) :
    (pathLaw kernel (Measure.dirac point)).map
        (fun path => (frestrictLe start path, path (start + offset))) =
      Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start (fun _ => point) ⊗ₘ
        (kernel ^ offset).comap
          (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) := by
  rw [pathLaw_dirac_eq_traj]
  exact traj_history_endpoint_joint kernel start offset (fun _ => point)

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.traj_block_endpoint
#print axioms IGS.Sec31.DiscreteMarkov.traj_history_endpoint_joint
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_history_endpoint_joint
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_dirac_history_endpoint_joint
