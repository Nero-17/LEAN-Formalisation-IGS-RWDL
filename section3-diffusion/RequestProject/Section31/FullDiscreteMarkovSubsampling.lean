import RequestProject.Section31.DiscreteMarkovSubsampling

/-! Full joint-law consistency of discrete Markov subsampling. The proof
constructs the sampled finite-prefix recursion from the actual block-joint
law, proves every finite-prefix distribution equal, then uses uniqueness of
the actual projective-limit measure. No fulljoint consistency is assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X]

theorem compProd_map_left_comap {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (measure : Measure A) [SFinite measure] (kernel : Kernel B C) [IsSFiniteKernel kernel]
    (function : A → B) (measurable : Measurable function) :
    (measure ⊗ₘ kernel.comap function measurable).map (Prod.map function id) =
      measure.map function ⊗ₘ kernel := by
  have identityPullback : (Kernel.id : Kernel B B).comap function measurable =
      Kernel.deterministic function measurable := by
    apply Kernel.ext
    intro point
    rfl
  have productMap : (Kernel.id ×ₖ kernel.comap function measurable).map (Prod.map function id) =
      (Kernel.id ×ₖ kernel).comap function measurable := by
    rw [← Kernel.map_prod_eq _ _ measurable, Kernel.id_map measurable,
      Kernel.comap_prod, identityPullback]
  rw [Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable.prodMap measurable_id), productMap,
    ← Kernel.comp_deterministic_eq_comap _ measurable, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map measurable, ← Measure.compProd_eq_comp_prod]

def selectedPrefix (stride count : ℕ) (path : ℕ → X) : Finset.Iic count → X :=
  fun index => path (stride * index.val)

theorem selectedPrefix_measurable (stride count : ℕ) :
    Measurable (selectedPrefix (X := X) stride count) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

def finiteSample (stride count : ℕ) (history : Finset.Iic (stride * count) → X) :
    Finset.Iic count → X :=
  fun index => history ⟨stride * index.val,
    Finset.mem_Iic.mpr (Nat.mul_le_mul_left stride (Finset.mem_Iic.mp index.property))⟩

theorem finiteSample_measurable (stride count : ℕ) :
    Measurable (finiteSample (X := X) stride count) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

def appendHistory (count : ℕ) (history : (Finset.Iic count → X) × X) : Finset.Iic (count + 1) → X :=
  fun index => if bound : index.val ≤ count then
    history.1 ⟨index.val, Finset.mem_Iic.mpr bound⟩ else history.2

theorem appendHistory_measurable (count : ℕ) : Measurable (appendHistory (X := X) count) := by
  apply measurable_pi_lambda
  intro index
  by_cases bound : index.val ≤ count
  · have evaluation : Measurable (fun history : Finset.Iic count → X =>
        history ⟨index.val, Finset.mem_Iic.mpr bound⟩) := measurable_pi_apply _
    simpa only [appendHistory, dif_pos bound] using evaluation.comp measurable_fst
  · simpa only [appendHistory, dif_neg bound] using
      (measurable_snd : Measurable (fun history : (Finset.Iic count → X) × X => history.2))

theorem appendHistory_prefix (count : ℕ) (path : ℕ → X) :
    appendHistory count (frestrictLe count path, path (count + 1)) = frestrictLe (count + 1) path := by
  funext index
  by_cases bound : index.val ≤ count
  · simp only [appendHistory, dif_pos bound, frestrictLe_apply]
  · have last : index.val = count + 1 :=
      Nat.le_antisymm (Finset.mem_Iic.mp index.property) (Nat.succ_le_of_lt (Nat.lt_of_not_ge bound))
    simp only [appendHistory, dif_neg bound, frestrictLe_apply]
    rw [last]

theorem sampled_prefix_next_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [SFinite initial] (stride count : ℕ) :
    (pathLaw kernel initial).map
        (fun path => (selectedPrefix stride count path, path (stride * (count + 1)))) =
      (pathLaw kernel initial).map (selectedPrefix stride count) ⊗ₘ historyStep (kernel ^ stride) count := by
  haveI : SFinite (pathLaw kernel initial) := by
    unfold pathLaw
    infer_instance
  have factor : (fun path : ℕ → X =>
      (selectedPrefix stride count path, path (stride * (count + 1)))) =
      (Prod.map (finiteSample stride count) id) ∘
        (fun path => (frestrictLe (stride * count) path, path (stride * count + stride))) := by
    funext path
    rw [Nat.mul_succ]
    rfl
  have conditional : (kernel ^ stride).comap
      (fun history : Finset.Iic (stride * count) → X =>
        history ⟨stride * count, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _) =
      (historyStep (kernel ^ stride) count).comap (finiteSample stride count)
        (finiteSample_measurable stride count) := by
    apply Kernel.ext
    intro history
    rfl
  rw [factor, ← Measure.map_map ((finiteSample_measurable stride count).prodMap measurable_id)
      ((measurable_frestrictLe (stride * count)).prodMk (measurable_pi_apply _)), pathLaw_history_endpoint_joint,
    conditional, compProd_map_left_comap, Measure.map_map (finiteSample_measurable stride count)
      (measurable_frestrictLe (stride * count))]
  rfl

theorem pathLaw_sampled_prefix (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (stride count : ℕ) :
    (pathLaw kernel initial).map (selectedPrefix stride count) =
      (pathLaw (kernel ^ stride) initial).map (frestrictLe count) := by
  induction count with
  | zero =>
    have sampledZero : selectedPrefix (X := X) stride 0 =
        (fun point => fun _ : Finset.Iic 0 => point) ∘ (fun path : ℕ → X => path 0) := by
      funext path index
      have indexZero : index.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp index.property)
      simp only [selectedPrefix, Function.comp_apply, indexZero, Nat.mul_zero]
    have prefixZero : frestrictLe (π := fun _ : ℕ => X) 0 =
        (fun point => fun _ : Finset.Iic 0 => point) ∘ (fun path : ℕ → X => path 0) := by
      funext path index
      have indexZero : index.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp index.property)
      simp only [Function.comp_apply, frestrictLe_apply, indexZero]
    calc
      (pathLaw kernel initial).map (selectedPrefix stride 0) =
          ((pathLaw kernel initial).map (fun path => path 0)).map
            (fun point => fun _ : Finset.Iic 0 => point) := by
        rw [Measure.map_map (f := fun path : ℕ → X => path 0)
          (g := fun point : X => fun _ : Finset.Iic 0 => point)
          (by fun_prop) (measurable_pi_apply 0), sampledZero]
      _ = initial.map (fun point => fun _ : Finset.Iic 0 => point) := by rw [pathLaw_coordinate_zero]
      _ = ((pathLaw (kernel ^ stride) initial).map (fun path => path 0)).map
            (fun point => fun _ : Finset.Iic 0 => point) := by rw [pathLaw_coordinate_zero]
      _ = (pathLaw (kernel ^ stride) initial).map (frestrictLe 0) := by
        rw [Measure.map_map (f := fun path : ℕ → X => path 0)
          (g := fun point : X => fun _ : Finset.Iic 0 => point)
          (by fun_prop) (measurable_pi_apply 0), prefixZero]
  | succ count inductionHypothesis =>
    have sampledAppend : appendHistory (X := X) count ∘
        (fun path : ℕ → X => (selectedPrefix stride count path, path (stride * (count + 1)))) =
        selectedPrefix stride (count + 1) :=
      funext (fun path => appendHistory_prefix count (sampleEvery stride path))
    have coarseAppend : appendHistory (X := X) count ∘
        (fun path : ℕ → X => (frestrictLe count path, path (count + 1))) =
        frestrictLe (count + 1) := funext (appendHistory_prefix count)
    have coarseJoint : (pathLaw (kernel ^ stride) initial).map
        (fun path => (frestrictLe count path, path (count + 1))) =
        (pathLaw (kernel ^ stride) initial).map (frestrictLe count) ⊗ₘ
          historyStep (kernel ^ stride) count := by
      simpa only [pow_one, historyStep] using
        pathLaw_history_endpoint_joint (kernel ^ stride) initial count 1
    calc
      (pathLaw kernel initial).map (selectedPrefix stride (count + 1)) =
          ((pathLaw kernel initial).map
            (fun path => (selectedPrefix stride count path, path (stride * (count + 1))))).map
            (appendHistory count) := by
        rw [Measure.map_map (appendHistory_measurable count)
          ((selectedPrefix_measurable stride count).prodMk (measurable_pi_apply _)), sampledAppend]
      _ = ((pathLaw kernel initial).map (selectedPrefix stride count) ⊗ₘ
          historyStep (kernel ^ stride) count).map (appendHistory count) := by
        rw [sampled_prefix_next_joint]
      _ = ((pathLaw (kernel ^ stride) initial).map (frestrictLe count) ⊗ₘ
          historyStep (kernel ^ stride) count).map (appendHistory count) := by rw [inductionHypothesis]
      _ = ((pathLaw (kernel ^ stride) initial).map
          (fun path => (frestrictLe count path, path (count + 1)))).map (appendHistory count) := by
        rw [coarseJoint]
      _ = (pathLaw (kernel ^ stride) initial).map (frestrictLe (count + 1)) := by
        rw [Measure.map_map (appendHistory_measurable count)
          ((measurable_frestrictLe count).prodMk (measurable_pi_apply _)), coarseAppend]

theorem pathLaw_sampleEvery (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [IsProbabilityMeasure initial] (stride : ℕ) :
    (pathLaw kernel initial).map (sampleEvery stride) = pathLaw (kernel ^ stride) initial := by
  let coarse := pathLaw (kernel ^ stride) initial
  let sampled := (pathLaw kernel initial).map (sampleEvery stride)
  let family : (coordinates : Finset ℕ) → Measure (coordinates → X) :=
    fun coordinates => coarse.map coordinates.restrict
  haveI : ∀ coordinates, IsFiniteMeasure (family coordinates) := by
    intro coordinates
    dsimp only [family, coarse]
    infer_instance
  have coarseLimit : IsProjectiveLimit coarse family := fun _ => rfl
  have sampledPrefixes : ∀ count, sampled.map (frestrictLe count) = coarse.map (frestrictLe count) := by
    intro count
    dsimp only [sampled, coarse]
    rw [Measure.map_map (measurable_frestrictLe count) (sampleEvery_measurable stride)]
    exact pathLaw_sampled_prefix kernel initial stride count
  have sampledLimit : IsProjectiveLimit sampled family := by
    intro coordinates
    have projected := congrArg
      (fun measure : Measure (Finset.Iic (coordinates.sup id) → X) =>
        measure.map (Finset.restrict₂ (π := fun _ : ℕ => X) coordinates.subset_Iic_sup_id))
      (sampledPrefixes (coordinates.sup id))
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
    exact (mapProjection sampled).symm.trans (projected.trans (mapProjection coarse))
  exact sampledLimit.unique coarseLimit

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.compProd_map_left_comap
#print axioms IGS.Sec31.DiscreteMarkov.sampled_prefix_next_joint
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_sampled_prefix
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_sampleEvery
