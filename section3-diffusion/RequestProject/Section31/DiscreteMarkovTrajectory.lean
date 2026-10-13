import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance

/-! Infinite discrete trajectories constructed by the actual Ionescu--Tulcea
kernel. A homogeneous transition kernel is applied to the last coordinate of
each finite history. The coordinate marginals are proved to be its iterates.
This is a discrete path measure, without a continuous-time or path-regularity
assertion. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

noncomputable def historyStep (kernel : Kernel X X) (index : ℕ) :
    Kernel (Finset.Iic index → X) X :=
  kernel.comap (fun history => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance historyStep_isMarkov (kernel : Kernel X X) [IsMarkovKernel kernel] (index : ℕ) :
    IsMarkovKernel (historyStep kernel index) := by
  unfold historyStep
  infer_instance

noncomputable def pathLaw (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) : Measure (ℕ → X) :=
  Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 ∘ₘ
    initial.map (fun point => fun _ : Finset.Iic 0 => point)

instance pathLaw_isProbability (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (pathLaw kernel initial) := by
  haveI : IsProbabilityMeasure (initial.map (fun point => fun _ : Finset.Iic 0 => point)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold pathLaw
  infer_instance

theorem traj_coordinate_zero (kernel : Kernel X X) [IsMarkovKernel kernel] :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map (fun path => path 0) =
      Kernel.deterministic (fun history : Finset.Iic 0 → X => history ⟨0, by simp⟩)
        (measurable_pi_apply _) := by
  have factor : (fun path : ℕ → X => path 0) =
      (fun history : Finset.Iic 0 → X => history ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
  rw [factor, Kernel.map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map (measurable_pi_apply _)]

theorem traj_coordinate_succ (kernel : Kernel X X) [IsMarkovKernel kernel] (index : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map (fun path => path (index + 1)) =
      kernel ∘ₖ (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map (fun path => path index) := by
  have factor : (fun path : ℕ → X => path index) =
      (fun history : Finset.Iic index → X => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe index := rfl
  calc
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map (fun path => path (index + 1)) =
        (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) index ∘ₖ
          Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 index).map (fun path => path (index + 1)) := by
      rw [Kernel.traj_comp_partialTraj (Nat.zero_le index)]
    _ = historyStep kernel index ∘ₖ Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 index := by
      rw [Kernel.map_comp, Kernel.map_traj_succ_self]
    _ = kernel ∘ₖ (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 index).map
        (fun history : Finset.Iic index → X => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) := by
      exact (Kernel.comp_map
        (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 index) kernel
        (f := fun history : Finset.Iic index → X => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)).symm
    _ = kernel ∘ₖ (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map (fun path => path index) := by
      rw [factor, Kernel.map_comp_right _ (measurable_frestrictLe index) (measurable_pi_apply _),
        Kernel.traj_map_frestrictLe]

theorem pathLaw_coordinate_zero (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) :
    (pathLaw kernel initial).map (fun path => path 0) = initial := by
  unfold pathLaw
  rw [Measure.map_comp _ _ (measurable_pi_apply 0), traj_coordinate_zero,
    Measure.deterministic_comp_eq_map (measurable_pi_apply _),
    Measure.map_map (measurable_pi_apply _) (by fun_prop)]
  exact Measure.map_id

theorem pathLaw_coordinate_succ (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) (index : ℕ) :
    (pathLaw kernel initial).map (fun path => path (index + 1)) =
      kernel ∘ₘ (pathLaw kernel initial).map (fun path => path index) := by
  unfold pathLaw
  rw [Measure.map_comp _ _ (measurable_pi_apply _), traj_coordinate_succ,
    ← Measure.comp_assoc, Measure.map_comp _ _ (measurable_pi_apply _)]

theorem pathLaw_coordinate_iterates (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) (index : ℕ) :
    (pathLaw kernel initial).map (fun path => path index) = (kernel ^ index) ∘ₘ initial := by
  induction index with
  | zero =>
    rw [pathLaw_coordinate_zero, pow_zero]
    exact Measure.id_comp.symm
  | succ index inductionHypothesis =>
    rw [pathLaw_coordinate_succ, inductionHypothesis, pow_succ']
    exact Measure.comp_assoc

theorem pathLaw_coordinate_stationary (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) (invariant : kernel.Invariant initial) (index : ℕ) :
    (pathLaw kernel initial).map (fun path => path index) = initial := by
  induction index with
  | zero => exact pathLaw_coordinate_zero kernel initial
  | succ index inductionHypothesis =>
    rw [pathLaw_coordinate_succ, inductionHypothesis]
    exact invariant.def

theorem pathLaw_coordinate_dirac (kernel : Kernel X X) [IsMarkovKernel kernel]
    (point : X) (index : ℕ) :
    (pathLaw kernel (Measure.dirac point)).map (fun path => path index) = (kernel ^ index) point := by
  rw [pathLaw_coordinate_iterates]
  exact Measure.dirac_bind (kernel ^ index).measurable point

theorem kernel_pow_fixed_step {Time : Type*} [AddMonoid Time]
    (family : Time → Kernel X X) (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (step : Time) (index : ℕ) :
    family step ^ index = family (index • step) := by
  induction index with
  | zero => rw [pow_zero, zero_nsmul, zeroLaw]; rfl
  | succ index inductionHypothesis =>
    rw [pow_succ', inductionHypothesis]
    change family step ∘ₖ family (index • step) = family ((index + 1) • step)
    simpa only [succ_nsmul] using addLaw (index • step) step

theorem pathLaw_fixed_step_marginal {Time : Type*} [AddMonoid Time]
    (family : Time → Kernel X X) [∀ time, IsMarkovKernel (family time)]
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (step : Time) (initial : Measure X) (index : ℕ) :
    (pathLaw (family step) initial).map (fun path => path index) =
      family (index • step) ∘ₘ initial := by
  rw [pathLaw_coordinate_iterates, kernel_pow_fixed_step family zeroLaw addLaw step index]

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_isProbability
#print axioms IGS.Sec31.DiscreteMarkov.traj_coordinate_succ
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_coordinate_iterates
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_coordinate_stationary
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_coordinate_dirac
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_fixed_step_marginal
