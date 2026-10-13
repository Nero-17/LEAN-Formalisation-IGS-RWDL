import RequestProject.Section31.EIGSRationalMarkovPathLawOfRules
import RequestProject.Section31.CoherentPrefixPathLaw
import Mathlib.Logic.Denumerable

/-! Actual probability laws indexed by all nonnegative dyadic times. Finite
enumerated prefixes are sampled from a sufficiently fine actual skeleton.
Their compatibility is proved from full skeleton subsampling, then actual
conditional-kernel Ionescu--Tulcea extension constructs the total law. The
enumeration is arbitrary and is never assumed to respect chronological order.
This does not assert real-time path regularity or a Hunt process. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNRat BigOperators
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

def prefixGridLevel (levels : ℕ → ℕ) (count : ℕ) : ℕ :=
  ∑ index ∈ Finset.range (count + 1), levels index

theorem prefixGridLevel_succ (levels : ℕ → ℕ) (count : ℕ) :
    prefixGridLevel levels (count + 1) = prefixGridLevel levels count + levels (count + 1) := by
  exact Finset.sum_range_succ levels (count + 1)

theorem level_le_prefixGridLevel (levels : ℕ → ℕ) (count : ℕ) (index : Finset.Iic count) :
    levels index.val ≤ prefixGridLevel levels count := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Iic.mp index.property)))

def prefixGridIndex (levels indices : ℕ → ℕ) (count : ℕ) (index : Finset.Iic count) : ℕ :=
  indices index.val * 2 ^ (prefixGridLevel levels count - levels index.val)

theorem prefixGridIndex_succ (levels indices : ℕ → ℕ) (count : ℕ) (index : Finset.Iic count) :
    prefixGridIndex levels indices (count + 1)
        ⟨index.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp index.property).trans (Nat.le_succ count))⟩ =
      2 ^ levels (count + 1) * prefixGridIndex levels indices count index := by
  have bound := level_le_prefixGridLevel levels count index
  have subtract : prefixGridLevel levels (count + 1) - levels index.val =
      (prefixGridLevel levels count - levels index.val) + levels (count + 1) := by
    rw [prefixGridLevel_succ]
    omega
  simp only [prefixGridIndex, subtract, pow_add]
  ring

def dyadicPrefix (levels indices : ℕ → ℕ) (count : ℕ) (path : ℕ → X) : Finset.Iic count → X :=
  fun index => path (prefixGridIndex levels indices count index)

theorem prefixGridIndex_time (levels indices : ℕ → ℕ) (count : ℕ) (index : Finset.Iic count) :
    prefixGridIndex levels indices count index • dyadicStep (prefixGridLevel levels count) =
      indices index.val • dyadicStep (levels index.val) := by
  have split : levels index.val + (prefixGridLevel levels count - levels index.val) =
      prefixGridLevel levels count := Nat.add_sub_of_le (level_le_prefixGridLevel levels count index)
  calc
    prefixGridIndex levels indices count index • dyadicStep (prefixGridLevel levels count) =
        indices index.val • ((2 ^ (prefixGridLevel levels count - levels index.val) : ℕ) •
          dyadicStep (levels index.val + (prefixGridLevel levels count - levels index.val))) := by
      rw [split, ← mul_nsmul]
      rw [prefixGridIndex, Nat.mul_comm]
    _ = indices index.val • dyadicStep (levels index.val) := by rw [dyadic_refinement_step]

theorem dyadicPrefix_measurable (levels indices : ℕ → ℕ) (count : ℕ) :
    Measurable (dyadicPrefix (X := X) levels indices count) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

theorem dyadicPrefix_restrict_succ (levels indices : ℕ → ℕ) (count : ℕ) :
    (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) ∘ dyadicPrefix levels indices (count + 1) =
      dyadicPrefix levels indices count ∘ sampleEvery (2 ^ levels (count + 1)) := by
  funext path index
  change path (prefixGridIndex levels indices (count + 1) _) =
    path (2 ^ levels (count + 1) * prefixGridIndex levels indices count index)
  rw [prefixGridIndex_succ]

variable (family : ℚ≥0 → Kernel X X) (markov : ∀ time, IsMarkovKernel (family time))
  (initial : Measure X) [IsProbabilityMeasure initial] (levels indices : ℕ → ℕ)

noncomputable def dyadicPrefixLaws (count : ℕ) : Measure (Finset.Iic count → X) :=
  (rationalSkeletonLaw family markov (dyadicStep (prefixGridLevel levels count)) initial).map
    (dyadicPrefix levels indices count)

instance dyadicPrefixLaws_isProbability (count : ℕ) :
    IsProbabilityMeasure (dyadicPrefixLaws family markov initial levels indices count) := by
  haveI : IsMarkovKernel (family (dyadicStep (prefixGridLevel levels count))) := markov _
  haveI : IsProbabilityMeasure
      (rationalSkeletonLaw family markov (dyadicStep (prefixGridLevel levels count)) initial) := by
    change IsProbabilityMeasure (pathLaw (family _) initial)
    infer_instance
  exact Measure.isProbabilityMeasure_map (dyadicPrefix_measurable levels indices count).aemeasurable

theorem dyadicPrefixLaws_coherent
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) (count : ℕ) :
    (dyadicPrefixLaws family markov initial levels indices (count + 1)).map
        (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) =
      dyadicPrefixLaws family markov initial levels indices count := by
  unfold dyadicPrefixLaws
  rw [Measure.map_map (measurable_frestrictLe₂ (X := fun _ : ℕ => X) (Nat.le_succ count))
    (dyadicPrefix_measurable levels indices (count + 1)), dyadicPrefix_restrict_succ,
    ← Measure.map_map (dyadicPrefix_measurable levels indices count)
      (sampleEvery_measurable (2 ^ levels (count + 1))), prefixGridLevel_succ,
    rationalSkeletonLaw_dyadic family markov zeroLaw addLaw]

noncomputable def enumeratedDyadicPathLaw : Measure (ℕ → X) :=
  coherentPrefixPathLaw (dyadicPrefixLaws family markov initial levels indices)

instance enumeratedDyadicPathLaw_isProbability :
    IsProbabilityMeasure (enumeratedDyadicPathLaw family markov initial levels indices) := by
  unfold enumeratedDyadicPathLaw
  infer_instance

theorem enumeratedDyadicPathLaw_prefix
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) (count : ℕ) :
    (enumeratedDyadicPathLaw family markov initial levels indices).map (frestrictLe count) =
      dyadicPrefixLaws family markov initial levels indices count :=
  coherentPrefixPathLaw_prefix _
    (dyadicPrefixLaws_coherent family markov initial levels indices zeroLaw addLaw) count

def DyadicTime := {time : ℚ≥0 // ∃ level index : ℕ, time = index • dyadicStep level}

instance dyadicTime_countable : Countable DyadicTime := by
  letI : Countable ℚ≥0 := NNRat.coe_injective.countable
  exact Subtype.val_injective.countable

instance dyadicTime_infinite : Infinite DyadicTime := by
  let injection : ℕ → DyadicTime := fun index =>
    ⟨(index : ℚ≥0), 0, index, by simp [dyadicStep]⟩
  apply Infinite.of_injective injection
  intro first second equal
  have equalValues : (first : ℚ≥0) = (second : ℚ≥0) := congrArg Subtype.val equal
  exact_mod_cast equalValues

noncomputable def dyadicEnumeration : ℕ ≃ DyadicTime := Classical.choice inferInstance

noncomputable def dyadicTimeLevel (time : DyadicTime) : ℕ := Classical.choose time.property

noncomputable def dyadicTimeIndex (time : DyadicTime) : ℕ :=
  Classical.choose (Classical.choose_spec time.property)

theorem dyadicTime_representation (time : DyadicTime) :
    time.val = dyadicTimeIndex time • dyadicStep (dyadicTimeLevel time) :=
  Classical.choose_spec (Classical.choose_spec time.property)

noncomputable def reindexDyadicPath (path : ℕ → X) (time : DyadicTime) : X :=
  path (dyadicEnumeration.symm time)

theorem reindexDyadicPath_measurable : Measurable (reindexDyadicPath (X := X)) := by
  apply measurable_pi_lambda
  intro time
  exact measurable_pi_apply _

noncomputable def dyadicPathLaw : Measure (DyadicTime → X) :=
  (enumeratedDyadicPathLaw family markov initial
    (fun index => dyadicTimeLevel (dyadicEnumeration index))
    (fun index => dyadicTimeIndex (dyadicEnumeration index))).map
      reindexDyadicPath

instance dyadicPathLaw_isProbability : IsProbabilityMeasure (dyadicPathLaw family markov initial) := by
  unfold dyadicPathLaw
  exact Measure.isProbabilityMeasure_map reindexDyadicPath_measurable.aemeasurable

theorem dyadicPathLaw_enumerated_prefix
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) (count : ℕ) :
    (dyadicPathLaw family markov initial).map
        (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val)) =
      dyadicPrefixLaws family markov initial
        (fun index => dyadicTimeLevel (dyadicEnumeration index))
        (fun index => dyadicTimeIndex (dyadicEnumeration index)) count := by
  unfold dyadicPathLaw
  have measurable : Measurable
      (fun path : DyadicTime → X => fun index : Finset.Iic count =>
        path (dyadicEnumeration index.val)) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_pi_apply _
  rw [Measure.map_map measurable reindexDyadicPath_measurable]
  have inverse :
      (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val)) ∘
        reindexDyadicPath =
      frestrictLe (π := fun _ : ℕ => X) count := by
    funext path index
    simp only [Function.comp_apply, reindexDyadicPath, Equiv.symm_apply_apply, frestrictLe_apply]
  rw [inverse]
  exact enumeratedDyadicPathLaw_prefix family markov initial _ _ zeroLaw addLaw count

theorem exists_dyadic_probability_pathLaw
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime)) :
    ∃ law : Measure (DyadicTime → X), IsProbabilityMeasure law ∧
      ∀ count, law.map (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val)) =
        dyadicPrefixLaws family markov initial
          (fun index => dyadicTimeLevel (dyadicEnumeration index))
          (fun index => dyadicTimeIndex (dyadicEnumeration index)) count :=
  ⟨dyadicPathLaw family markov initial, inferInstance,
    dyadicPathLaw_enumerated_prefix family markov initial zeroLaw addLaw⟩

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.dyadicPrefixLaws_coherent
#print axioms IGS.Sec31.DiscreteMarkov.enumeratedDyadicPathLaw_prefix
#print axioms IGS.Sec31.DiscreteMarkov.dyadicPathLaw_enumerated_prefix
#print axioms IGS.Sec31.DiscreteMarkov.exists_dyadic_probability_pathLaw
