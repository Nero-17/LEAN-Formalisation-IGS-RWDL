import RequestProject.Section31.InvariantKernelStableFullSet
import RequestProject.Section31.CountableMarkovKernelIdentity

/-! Absorbing modification of an actual countable-time invariant Markov family.
The measurable full set and its stability are constructed from the proved AE
laws. The modified family has exact zero-time and composition laws at every
point, agrees AE with the original family and preserves the original measure.
No conclusion about all real times or Hunt paths is asserted. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

noncomputable def absorbingKernel (good : Set X) (goodMeasurable : MeasurableSet good)
    (kernel : Kernel X X) : Kernel X X := by
  classical
  exact Kernel.piecewise goodMeasurable kernel Kernel.id

theorem absorbingKernel_apply (good : Set X) (goodMeasurable : MeasurableSet good)
    (kernel : Kernel X X) (point : X) [Decidable (point ∈ good)] :
    absorbingKernel good goodMeasurable kernel point =
      if point ∈ good then kernel point else Measure.dirac point := by
  classical
  by_cases membership : point ∈ good
  · simp only [absorbingKernel, Kernel.piecewise_apply, if_pos membership]
  · simp only [absorbingKernel, Kernel.piecewise_apply, if_neg membership, Kernel.id_apply]

instance absorbingKernel_isMarkov (good : Set X) (goodMeasurable : MeasurableSet good)
    (kernel : Kernel X X) [IsMarkovKernel kernel] :
    IsMarkovKernel (absorbingKernel good goodMeasurable kernel) := by
  classical
  unfold absorbingKernel
  infer_instance

theorem absorbingKernel_ae_eq (measure : Measure X) (good : Set X)
    (goodMeasurable : MeasurableSet good) (goodNull : measure goodᶜ = 0)
    (kernel : Kernel X X) :
    (fun point => absorbingKernel good goodMeasurable kernel point) =ᵐ[measure] kernel := by
  classical
  filter_upwards [ae_iff.mpr goodNull] with point membership
  simp only [absorbingKernel_apply, if_pos membership]

theorem absorbingKernel_comp_of_stable (good : Set X) (goodMeasurable : MeasurableSet good)
    (first second combined : Kernel X X)
    (stable : ∀ point ∈ good, first point goodᶜ = 0)
    (composition : ∀ point ∈ good, (second ∘ₖ first) point = combined point) :
    absorbingKernel good goodMeasurable second ∘ₖ absorbingKernel good goodMeasurable first =
      absorbingKernel good goodMeasurable combined := by
  classical
  apply Kernel.ext
  intro point
  by_cases membership : point ∈ good
  · have agree : (fun location => absorbingKernel good goodMeasurable second location)
        =ᵐ[first point] second := by
      filter_upwards [ae_iff.mpr (stable point membership)] with location locationGood
      simp only [absorbingKernel_apply, if_pos locationGood]
    calc
      (absorbingKernel good goodMeasurable second ∘ₖ
          absorbingKernel good goodMeasurable first) point =
          (first point).bind (absorbingKernel good goodMeasurable second) := by
        rw [Kernel.comp_apply, absorbingKernel_apply, if_pos membership]
      _ = (first point).bind second := Measure.bind_congr_right agree
      _ = (second ∘ₖ first) point := rfl
      _ = combined point := composition point membership
      _ = absorbingKernel good goodMeasurable combined point := by
        simp only [absorbingKernel_apply, if_pos membership]
  · rw [Kernel.comp_apply, absorbingKernel_apply, if_neg membership,
      Measure.dirac_bind (absorbingKernel good goodMeasurable second).measurable]
    simp only [absorbingKernel_apply, if_neg membership]

theorem exists_countable_time_markov_modification
    {Time : Type*} [AddMonoid Time] [Countable Time]
    (measure : Measure X) (kernels : Time → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (kernels time))
    (invariant : ∀ time, (kernels time).Invariant measure)
    (zeroLaw : ∀ᵐ point ∂measure, kernels 0 point = Kernel.id point)
    (addLaw : ∀ firstTime secondTime, ∀ᵐ point ∂measure,
      (kernels secondTime ∘ₖ kernels firstTime) point = kernels (firstTime + secondTime) point) :
    ∃ modified : Time → Kernel X X,
      (∀ time, IsMarkovKernel (modified time)) ∧
      (∀ time, (modified time).Invariant measure) ∧
      (∀ time, (fun point => modified time point) =ᵐ[measure] kernels time) ∧
      modified 0 = Kernel.id ∧
      (∀ firstTime secondTime,
        modified secondTime ∘ₖ modified firstTime = modified (firstTime + secondTime)) := by
  classical
  let predicate : Option (Time × Time) → X → Prop
    | none => fun point => kernels 0 point = Kernel.id point
    | some times => fun point =>
        (kernels times.2 ∘ₖ kernels times.1) point = kernels (times.1 + times.2) point
  have laws : ∀ index, ∀ᵐ point ∂measure, predicate index point := by
    intro index
    cases index with
    | none => exact zeroLaw
    | some times => exact addLaw times.1 times.2
  obtain ⟨initialGood, initialMeasurable, initialNull, initialLaws⟩ :=
    IGS.Sec31.exists_measurable_full_set_of_countable_ae measure predicate laws
  obtain ⟨good, goodMeasurable, goodSubset, goodNull, stable⟩ :=
    exists_invariant_stable_full_set measure kernels invariant initialGood initialMeasurable initialNull
  let modified : Time → Kernel X X := fun time => absorbingKernel good goodMeasurable (kernels time)
  have modifiedMarkov : ∀ time, IsMarkovKernel (modified time) := by
    intro time
    letI : IsMarkovKernel (kernels time) := markov time
    dsimp only [modified]
    infer_instance
  have sameAE : ∀ time, (fun point => modified time point) =ᵐ[measure] kernels time :=
    fun time => absorbingKernel_ae_eq measure good goodMeasurable goodNull (kernels time)
  have zeroIdentity : modified 0 = Kernel.id := by
    apply Kernel.ext
    intro point
    by_cases membership : point ∈ good
    · have originalZero : kernels 0 point = Kernel.id point :=
        initialLaws point (goodSubset membership) none
      simpa only [modified, absorbingKernel_apply, if_pos membership, Kernel.id_apply] using originalZero
    · simp only [modified, absorbingKernel_apply, if_neg membership, Kernel.id_apply]
  refine ⟨modified, modifiedMarkov, ?_, sameAE, zeroIdentity, ?_⟩
  · intro time
    change modified time ∘ₘ measure = measure
    exact (Measure.comp_congr (sameAE time)).trans (invariant time).def
  · intro firstTime secondTime
    exact absorbingKernel_comp_of_stable good goodMeasurable (kernels firstTime) (kernels secondTime)
      (kernels (firstTime + secondTime))
      (fun point membership => stable point membership firstTime)
      (fun point membership => initialLaws point (goodSubset membership) (some (firstTime, secondTime)))

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.absorbingKernel_ae_eq
#print axioms IGS.Sec31.CountableMarkov.absorbingKernel_comp_of_stable
#print axioms IGS.Sec31.CountableMarkov.exists_countable_time_markov_modification
