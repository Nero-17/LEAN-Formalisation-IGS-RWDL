import RequestProject.Section31.FullDiscreteMarkovSubsampling
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-! Construct an actual countable-coordinate probability law from coherent
finite prefix laws. Conditional kernels are constructed by disintegration;
Ionescu--Tulcea supplies the infinite law, whose entire prefix distributions
are then proved by induction. Native dyadic compatibility is a later consumer
and is not claimed here. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

def splitPrefix (count : ℕ) (history : Finset.Iic (count + 1) → X) :
    (Finset.Iic count → X) × X :=
  (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count) history,
    history ⟨count + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem splitPrefix_measurable (count : ℕ) : Measurable (splitPrefix (X := X) count) := by
  exact (measurable_frestrictLe₂ (X := fun _ : ℕ => X) (Nat.le_succ count)).prodMk (measurable_pi_apply _)

theorem appendHistory_splitPrefix (count : ℕ) (history : Finset.Iic (count + 1) → X) :
    appendHistory count (splitPrefix count history) = history := by
  funext index
  by_cases bound : index.val ≤ count
  · simp only [appendHistory, splitPrefix, dif_pos bound, frestrictLe₂_apply]
  · have last : index.val = count + 1 :=
      Nat.le_antisymm (Finset.mem_Iic.mp index.property)
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge bound))
    simp only [appendHistory, splitPrefix, dif_neg bound]
    congr 1
    exact Subtype.ext last.symm

variable (prefixLaws : (count : ℕ) → Measure (Finset.Iic count → X))
  [∀ count, IsProbabilityMeasure (prefixLaws count)]

noncomputable def prefixJoint (count : ℕ) : Measure ((Finset.Iic count → X) × X) :=
  (prefixLaws (count + 1)).map (splitPrefix count)

instance prefixJoint_isProbability (count : ℕ) :
    IsProbabilityMeasure (prefixJoint prefixLaws count) :=
  Measure.isProbabilityMeasure_map (splitPrefix_measurable count).aemeasurable

noncomputable def prefixConditional (count : ℕ) : Kernel (Finset.Iic count → X) X :=
  (prefixJoint prefixLaws count).condKernel

instance prefixConditional_isMarkov (count : ℕ) :
    IsMarkovKernel (prefixConditional prefixLaws count) := by
  unfold prefixConditional
  infer_instance

noncomputable def coherentPrefixPathLaw : Measure (ℕ → X) :=
  Kernel.trajMeasure (X := fun _ : ℕ => X)
    ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)))
    (prefixConditional prefixLaws)

instance coherentPrefixPathLaw_isProbability :
    IsProbabilityMeasure (coherentPrefixPathLaw prefixLaws) := by
  haveI : IsProbabilityMeasure
      ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X))) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.piUnique _).measurable.aemeasurable
  unfold coherentPrefixPathLaw
  infer_instance

theorem prefixJoint_fst
    (coherent : ∀ count, (prefixLaws (count + 1)).map (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) = prefixLaws count)
    (count : ℕ) : (prefixJoint prefixLaws count).fst = prefixLaws count := by
  unfold prefixJoint splitPrefix
  rw [Measure.fst_map_prodMk (measurable_pi_apply _)]
  exact coherent count

theorem prefixConditional_disintegrates
    (coherent : ∀ count, (prefixLaws (count + 1)).map (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) = prefixLaws count)
    (count : ℕ) : prefixLaws count ⊗ₘ prefixConditional prefixLaws count = prefixJoint prefixLaws count := by
  have disintegration := Measure.disintegrate (prefixJoint prefixLaws count)
    (prefixJoint prefixLaws count).condKernel
  simpa only [prefixJoint_fst prefixLaws coherent, prefixConditional] using disintegration

theorem coherentPrefixPathLaw_prefix
    (coherent : ∀ count, (prefixLaws (count + 1)).map (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) = prefixLaws count)
    (count : ℕ) : (coherentPrefixPathLaw prefixLaws).map (frestrictLe count) = prefixLaws count := by
  induction count with
  | zero =>
    unfold coherentPrefixPathLaw Kernel.trajMeasure
    rw [MeasurableEquiv.map_symm_map, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ count induction =>
    haveI : IsProbabilityMeasure
        ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X))) :=
      Measure.isProbabilityMeasure_map (MeasurableEquiv.piUnique _).measurable.aemeasurable
    have recurrence := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => X)
      (μ₀ := (prefixLaws 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)))
      (κ := prefixConditional prefixLaws) (a := count)
    change (coherentPrefixPathLaw prefixLaws).map (frestrictLe count) ⊗ₘ
      prefixConditional prefixLaws count =
        (coherentPrefixPathLaw prefixLaws).map
          (fun path => (frestrictLe count path, path (count + 1))) at recurrence
    rw [induction, prefixConditional_disintegrates prefixLaws coherent] at recurrence
    calc
      (coherentPrefixPathLaw prefixLaws).map (frestrictLe (count + 1)) =
          ((coherentPrefixPathLaw prefixLaws).map
            (fun path => (frestrictLe count path, path (count + 1)))).map
              (appendHistory count) := by
        rw [Measure.map_map (appendHistory_measurable count)
          ((measurable_frestrictLe count).prodMk (measurable_pi_apply _))]
        congr 1
        funext path
        exact (appendHistory_prefix count path).symm
      _ = (prefixJoint prefixLaws count).map (appendHistory count) := by rw [← recurrence]
      _ = prefixLaws (count + 1) := by
        unfold prefixJoint
        rw [Measure.map_map (appendHistory_measurable count) (splitPrefix_measurable count)]
        have inverse : appendHistory count ∘ splitPrefix (X := X) count = id := by
          funext history
          exact appendHistory_splitPrefix count history
        rw [inverse, Measure.map_id]

theorem exists_probability_pathLaw_of_coherent_prefixes
    (coherent : ∀ count, (prefixLaws (count + 1)).map (frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ count)) = prefixLaws count) :
    ∃ law : Measure (ℕ → X), IsProbabilityMeasure law ∧
      ∀ count, law.map (frestrictLe count) = prefixLaws count :=
  ⟨coherentPrefixPathLaw prefixLaws, inferInstance, coherentPrefixPathLaw_prefix prefixLaws coherent⟩

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.prefixConditional_disintegrates
#print axioms IGS.Sec31.DiscreteMarkov.coherentPrefixPathLaw_prefix
#print axioms IGS.Sec31.DiscreteMarkov.exists_probability_pathLaw_of_coherent_prefixes
