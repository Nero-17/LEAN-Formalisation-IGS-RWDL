import RequestProject.Section31.CoherentPrefixPathLaw

/-! Coherent prefix probabilities on different standard Borel coordinate
spaces have one genuine countable-coordinate probability law. The proof
constructs conditional kernels and uses dependent Ionescu--Tulcea. -/

namespace IGS.Sec31.DependentPrefix

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory
noncomputable section
set_option maxHeartbeats 4000000

variable {Space : ℕ → Type*} [∀ index, MeasurableSpace (Space index)]
  [∀ index, StandardBorelSpace (Space index)] [∀ index, Nonempty (Space index)]

def splitPrefix (count : ℕ) (history : (index : Finset.Iic (count + 1)) → Space index.val) :
    ((index : Finset.Iic count) → Space index.val) × Space (count + 1) :=
  (frestrictLe₂ (π := Space) (Nat.le_succ count) history,
    history ⟨count + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem splitPrefix_measurable (count : ℕ) : Measurable (splitPrefix (Space := Space) count) :=
  (measurable_frestrictLe₂ (X := Space) (Nat.le_succ count)).prodMk (measurable_pi_apply _)

def appendPrefix (count : ℕ)
    (history : ((index : Finset.Iic count) → Space index.val) × Space (count + 1))
    (index : Finset.Iic (count + 1)) : Space index.val :=
  if bound : index.val ≤ count then history.1 ⟨index.val, Finset.mem_Iic.mpr bound⟩
  else cast (congrArg Space (show count + 1 = index.val by
    have := Finset.mem_Iic.mp index.property
    omega)) history.2

theorem appendPrefix_measurable (count : ℕ) : Measurable (appendPrefix (Space := Space) count) := by
  apply measurable_pi_lambda
  intro index
  rcases index with ⟨index, membership⟩
  by_cases bound : index ≤ count
  · simpa only [appendPrefix, dif_pos bound] using (measurable_pi_apply
      (⟨index, Finset.mem_Iic.mpr bound⟩ : Finset.Iic count)).comp measurable_fst
  · have last : index = count + 1 := by have := Finset.mem_Iic.mp membership; omega
    subst index
    simpa only [appendPrefix, dif_neg (show ¬ count + 1 ≤ count by omega), cast_eq] using
      (measurable_snd : Measurable
        (Prod.snd : ((index : Finset.Iic count) → Space index.val) × Space (count + 1) → Space (count + 1)))

theorem appendPrefix_splitPrefix (count : ℕ)
    (history : (index : Finset.Iic (count + 1)) → Space index.val) :
    appendPrefix count (splitPrefix count history) = history := by
  funext index
  rcases index with ⟨index, membership⟩
  by_cases bound : index ≤ count
  · simp only [appendPrefix, splitPrefix, dif_pos bound, frestrictLe₂_apply]
  · have last : index = count + 1 := by have := Finset.mem_Iic.mp membership; omega
    subst index
    simp only [appendPrefix, splitPrefix, dif_neg (show ¬ count + 1 ≤ count by omega), cast_eq]

theorem appendPrefix_prefix (count : ℕ) (path : (index : ℕ) → Space index) :
    appendPrefix count (frestrictLe count path, path (count + 1)) = frestrictLe (count + 1) path :=
  appendPrefix_splitPrefix count (frestrictLe (count + 1) path)

variable (prefixLaws : (count : ℕ) → Measure ((index : Finset.Iic count) → Space index.val))
  [∀ count, IsProbabilityMeasure (prefixLaws count)]

def prefixJoint (count : ℕ) :
    Measure (((index : Finset.Iic count) → Space index.val) × Space (count + 1)) :=
  (prefixLaws (count + 1)).map (splitPrefix count)

instance prefixJoint_isProbability (count : ℕ) : IsProbabilityMeasure (prefixJoint prefixLaws count) :=
  Measure.isProbabilityMeasure_map (splitPrefix_measurable count).aemeasurable

def prefixConditional (count : ℕ) : Kernel ((index : Finset.Iic count) → Space index.val) (Space (count + 1)) :=
  (prefixJoint prefixLaws count).condKernel

instance prefixConditional_isMarkov (count : ℕ) : IsMarkovKernel (prefixConditional prefixLaws count) := by
  unfold prefixConditional
  infer_instance

def coherentPathLaw : Measure ((index : ℕ) → Space index) :=
  Kernel.trajMeasure (X := Space)
    ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun index : Finset.Iic 0 => Space index.val)))
    (prefixConditional prefixLaws)

instance coherentPathLaw_isProbability : IsProbabilityMeasure (coherentPathLaw prefixLaws) := by
  haveI : IsProbabilityMeasure
      ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun index : Finset.Iic 0 => Space index.val))) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.piUnique _).measurable.aemeasurable
  unfold coherentPathLaw
  infer_instance

theorem coherentPathLaw_prefix
    (coherent : ∀ count, (prefixLaws (count + 1)).map
      (frestrictLe₂ (π := Space) (Nat.le_succ count)) = prefixLaws count)
    (count : ℕ) : (coherentPathLaw prefixLaws).map (frestrictLe count) = prefixLaws count := by
  have jointFirst (count : ℕ) : (prefixJoint prefixLaws count).fst = prefixLaws count := by
    unfold prefixJoint splitPrefix
    rw [Measure.fst_map_prodMk (measurable_pi_apply _)]
    exact coherent count
  have disintegrates (count : ℕ) : prefixLaws count ⊗ₘ prefixConditional prefixLaws count =
      prefixJoint prefixLaws count := by
    have disintegration := Measure.disintegrate (prefixJoint prefixLaws count)
      (prefixJoint prefixLaws count).condKernel
    simpa only [jointFirst, prefixConditional] using disintegration
  induction count with
  | zero =>
      unfold coherentPathLaw Kernel.trajMeasure
      rw [MeasurableEquiv.map_symm_map, Measure.map_comp _ _ (measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ count induction =>
      haveI : IsProbabilityMeasure
          ((prefixLaws 0).map (MeasurableEquiv.piUnique (fun index : Finset.Iic 0 => Space index.val))) :=
        Measure.isProbabilityMeasure_map (MeasurableEquiv.piUnique _).measurable.aemeasurable
      have recurrence := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := Space)
        (μ₀ := (prefixLaws 0).map (MeasurableEquiv.piUnique (fun index : Finset.Iic 0 => Space index.val)))
        (κ := prefixConditional prefixLaws) (a := count)
      change (coherentPathLaw prefixLaws).map (frestrictLe count) ⊗ₘ prefixConditional prefixLaws count =
        (coherentPathLaw prefixLaws).map (fun path => (frestrictLe count path, path (count + 1))) at recurrence
      rw [induction, disintegrates] at recurrence
      calc
        (coherentPathLaw prefixLaws).map (frestrictLe (count + 1)) =
            ((coherentPathLaw prefixLaws).map
              (fun path => (frestrictLe count path, path (count + 1)))).map (appendPrefix count) := by
          rw [Measure.map_map (appendPrefix_measurable count)
            ((measurable_frestrictLe count).prodMk (measurable_pi_apply _))]
          congr 1
          funext path
          exact (appendPrefix_prefix count path).symm
        _ = (prefixJoint prefixLaws count).map (appendPrefix count) := by rw [← recurrence]
        _ = prefixLaws (count + 1) := by
          unfold prefixJoint
          rw [Measure.map_map (appendPrefix_measurable count) (splitPrefix_measurable count)]
          have inverse : appendPrefix (Space := Space) count ∘ splitPrefix count = id := by
            funext history
            exact appendPrefix_splitPrefix count history
          rw [inverse, Measure.map_id]

end
end IGS.Sec31.DependentPrefix

#print axioms IGS.Sec31.DependentPrefix.appendPrefix_splitPrefix
#print axioms IGS.Sec31.DependentPrefix.coherentPathLaw_prefix
