import RequestProject.Section31.CoarseHittingShift

/-! Exact deterministic time shifts of the actual homogeneous IFT path law.
The future-block kernel is identified from the actual IFT recurrence, then
its finite prefixes and the complete shifted path law are identified.
The restarted initial measure is the actual coordinate marginal. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ProbabilityTheory Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

def initialPointPathKernel (kernel : Kernel X X) [IsMarkovKernel kernel] : Kernel X (ℕ → X) :=
  (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).comap
    (fun point => fun _ : Finset.Iic 0 => point) (by fun_prop)

instance initialPointPathKernel_isMarkov (kernel : Kernel X X) [IsMarkovKernel kernel] :
    IsMarkovKernel (initialPointPathKernel kernel) := by
  unfold initialPointPathKernel
  infer_instance

theorem initialPointPathKernel_apply (kernel : Kernel X X) [IsMarkovKernel kernel] (point : X) :
    initialPointPathKernel kernel point = pathLaw kernel (Measure.dirac point) := by
  rw [initialPointPathKernel, Kernel.comap_apply, pathLaw_dirac_eq_traj]

theorem pathLaw_eq_initialPointPathKernel_comp (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) :
    pathLaw kernel initial = initialPointPathKernel kernel ∘ₘ initial := by
  unfold pathLaw initialPointPathKernel
  rw [← Measure.deterministic_comp_eq_map (show Measurable (fun point : X => fun _ : Finset.Iic 0 => point) by fun_prop),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]

theorem futureBlockKernel_eq_initialPoint_prefix_comap (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) :
    futureBlockKernel kernel start count =
      ((initialPointPathKernel kernel).map (frestrictLe count)).comap
        (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  apply Kernel.ext
  intro history
  rw [Kernel.comap_apply, Kernel.map_apply _ (measurable_frestrictLe count), initialPointPathKernel_apply]
  exact futureBlockKernel_eq_dirac_prefix kernel start count history

theorem pathLaw_futurePrefix (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (start count : ℕ) :
    (pathLaw kernel initial).map (futurePrefix start count) =
      (pathLaw kernel ((kernel ^ start : Kernel X X) ∘ₘ initial)).map (frestrictLe count) := by
  have joint := pathLaw_history_future_block_joint kernel initial start count
  have projected := congrArg (fun measure : Measure ((Finset.Iic start → X) × (Finset.Iic count → X)) =>
    measure.map Prod.snd) joint
  dsimp only at projected
  rw [Measure.map_map
    (f := fun path : ℕ → X => (frestrictLe start path, futurePrefix start count path))
    (g := Prod.snd) measurable_snd
    ((measurable_frestrictLe start).prodMk (futurePrefix_measurable start count))] at projected
  change (pathLaw kernel initial).map (futurePrefix start count) =
    ((pathLaw kernel initial).map (frestrictLe start) ⊗ₘ futureBlockKernel kernel start count).snd at projected
  rw [Measure.snd_compProd] at projected
  have kernelIdentity : futureBlockKernel kernel start count =
      ((initialPointPathKernel kernel).map (frestrictLe count)) ∘ₖ
        Kernel.deterministic
          (fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) := by
    rw [futureBlockKernel_eq_initialPoint_prefix_comap]
    exact (Kernel.comp_deterministic_eq_comap
      ((initialPointPathKernel kernel).map (frestrictLe count)) (measurable_pi_apply _)).symm
  calc
    _ = futureBlockKernel kernel start count ∘ₘ (pathLaw kernel initial).map (frestrictLe start) := projected
    _ = ((initialPointPathKernel kernel).map (frestrictLe count)) ∘ₘ
        (pathLaw kernel initial).map (fun path => path start) := by
      rw [kernelIdentity, ← Measure.comp_assoc,
        Measure.deterministic_comp_eq_map (measurable_pi_apply _),
        Measure.map_map
          (f := frestrictLe (π := fun _ : ℕ => X) start)
          (g := fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) (measurable_frestrictLe start)]
      <;> rfl
    _ = ((initialPointPathKernel kernel).map (frestrictLe count)) ∘ₘ ((kernel ^ start : Kernel X X) ∘ₘ initial) := by
      rw [pathLaw_coordinate_iterates]
    _ = _ := by
      rw [pathLaw_eq_initialPointPathKernel_comp,
        Measure.map_comp _ _ (measurable_frestrictLe count)]

theorem shiftPath_measurable (start : ℕ) : Measurable (shiftPath (X := X) start) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

theorem pathLaw_shiftPath (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (start : ℕ) :
    (pathLaw kernel initial).map (shiftPath start) = pathLaw kernel ((kernel ^ start : Kernel X X) ∘ₘ initial) := by
  let restarted : Measure (ℕ → X) := pathLaw kernel ((kernel ^ start : Kernel X X) ∘ₘ initial)
  let shifted := (pathLaw kernel initial).map (shiftPath start)
  let family : (coordinates : Finset ℕ) → Measure (coordinates → X) :=
    fun coordinates => restarted.map coordinates.restrict
  haveI : ∀ coordinates, IsFiniteMeasure (family coordinates) := by
    intro coordinates
    dsimp only [family, restarted]
    infer_instance
  have restartedLimit : IsProjectiveLimit restarted family := fun _ => rfl
  have shiftedPrefixes : ∀ count, shifted.map (frestrictLe count) = restarted.map (frestrictLe count) := by
    intro count
    dsimp only [shifted, restarted]
    rw [Measure.map_map (measurable_frestrictLe count) (shiftPath_measurable start)]
    exact pathLaw_futurePrefix kernel initial start count
  have shiftedLimit : IsProjectiveLimit shifted family := by
    intro coordinates
    have projected := congrArg
      (fun measure : Measure (Finset.Iic (coordinates.sup id) → X) =>
        measure.map (Finset.restrict₂ (π := fun _ : ℕ => X) coordinates.subset_Iic_sup_id))
      (shiftedPrefixes (coordinates.sup id))
    have mapProjection (measure : Measure (ℕ → X)) :
        (measure.map (frestrictLe (π := fun _ : ℕ => X) (coordinates.sup id))).map
          (Finset.restrict₂ (π := fun _ : ℕ => X) coordinates.subset_Iic_sup_id) =
          measure.map (coordinates.restrict (π := fun _ : ℕ => X)) := by
      rw [Measure.map_map
        (f := frestrictLe (π := fun _ : ℕ => X) (coordinates.sup id))
        (g := Finset.restrict₂ (π := fun _ : ℕ => X) coordinates.subset_Iic_sup_id)
        (Finset.measurable_restrict₂ (X := fun _ : ℕ => X) coordinates.subset_Iic_sup_id)
        (measurable_frestrictLe (coordinates.sup id))]
      rfl
    exact (mapProjection shifted).symm.trans (projected.trans (mapProjection restarted))
  exact shiftedLimit.unique restartedLimit

theorem pathLaw_shiftPath_event (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (start : ℕ)
    (event : Set (ℕ → X)) (eventMeasurable : MeasurableSet event) :
    (pathLaw kernel initial) ((shiftPath start) ⁻¹' event) =
      pathLaw kernel ((kernel ^ start : Kernel X X) ∘ₘ initial) event := by
  have equality := congrArg (fun measure : Measure (ℕ → X) => measure event)
    (pathLaw_shiftPath kernel initial start)
  dsimp only at equality
  rw [Measure.map_apply (shiftPath_measurable start) eventMeasurable] at equality
  exact equality

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.initialPointPathKernel_apply
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_eq_initialPointPathKernel_comp
#print axioms IGS.Sec31.DiscreteMarkov.futureBlockKernel_eq_initialPoint_prefix_comap
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_futurePrefix
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_shiftPath
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_shiftPath_event
