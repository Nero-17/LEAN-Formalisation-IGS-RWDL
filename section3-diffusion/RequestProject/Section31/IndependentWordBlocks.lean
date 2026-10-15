import RequestProject.Section31.IndependentRenewalPhases

/-! Genuine independent finite words cut from an infinite product sample.
The joint law is proved by an injective coordinate selection and the
product-measure curry identity. No block independence is an input. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
set_option maxHeartbeats 3000000

def independentWordBlock {Alphabet : Type*} (width offset trial : ℕ)
    (sample : ℕ → Alphabet) : Fin width → Alphabet :=
  fun position => sample (offset + trial * width + position)

@[fun_prop] theorem independentWordBlock_measurable {Alphabet : Type*}
    [MeasurableSpace Alphabet] (width offset trial : ℕ) :
    Measurable (independentWordBlock (Alphabet := Alphabet) width offset trial) :=
  measurable_pi_iff.mpr fun position =>
    measurable_pi_apply (offset + trial * width + position.val)

theorem independent_word_block_coordinates_injective (trials width offset : ℕ) :
    Function.Injective (fun pair : Fin trials × Fin width =>
      offset + pair.1.val * width + pair.2.val) := by
  intro first second equality
  have reduced : first.1.val * width + first.2.val =
      second.1.val * width + second.2.val :=
    Nat.add_left_cancel (by simpa only [Nat.add_assoc] using equality)
  have positions := congrArg (fun value => value % width) reduced
  dsimp only at positions
  rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt first.2.isLt, Nat.add_mod, Nat.mul_mod_left,
    zero_add, Nat.mod_mod, Nat.mod_eq_of_lt second.2.isLt] at positions
  have multiples : first.1.val * width = second.1.val * width := by omega
  have widthPositive : 0 < width := by omega
  have trialsEqual : first.1.val = second.1.val := by
    exact Nat.eq_of_mul_eq_mul_right widthPositive multiples
  exact Prod.ext (Fin.ext trialsEqual) (Fin.ext positions)

theorem independent_word_blocks_joint_law
    {Alphabet : Type*} [MeasurableSpace Alphabet]
    (letterLaw : Measure Alphabet) [IsProbabilityMeasure letterLaw]
    (trials width offset : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => letterLaw)).map
      (fun (sample : ℕ → Alphabet) (trial : Fin trials) =>
        independentWordBlock width offset trial sample) =
      Measure.pi (fun _ : Fin trials => Measure.pi (fun _ : Fin width => letterLaw)) := by
  have originalCoordinates : iIndepFun
      (fun index : ℕ => fun sample : ℕ → Alphabet => sample index)
      (Measure.infinitePi (fun _ : ℕ => letterLaw)) :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (value : Alphabet) => value)
      (fun _ => measurable_id)
  have coordinates : iIndepFun
      (fun pair : Fin trials × Fin width =>
        fun sample : ℕ → Alphabet => sample (offset + pair.1.val * width + pair.2.val))
      (Measure.infinitePi (fun _ : ℕ => letterLaw)) :=
    iIndepFun.precomp (independent_word_block_coordinates_injective trials width offset)
      originalCoordinates
  have flattened := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ => measurable_pi_apply _)).mp coordinates
  simp only [Measure.infinitePi_map_eval] at flattened
  have curried := congrArg
    (fun law : Measure ((Fin trials × Fin width) → Alphabet) =>
      law.map (MeasurableEquiv.curry (Fin trials) (Fin width) Alphabet)) flattened
  dsimp only at curried
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at curried
  have curryLaw := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin trials) (_ : Fin width) => letterLaw)
  rw [curryLaw] at curried
  simpa only [Measure.infinitePi_eq_pi, Function.comp_def,
    MeasurableEquiv.curry_apply, independentWordBlock] using curried

theorem independent_word_block_law
    {Alphabet : Type*} [MeasurableSpace Alphabet]
    (letterLaw : Measure Alphabet) [IsProbabilityMeasure letterLaw]
    (trials width offset : ℕ) (trial : Fin trials) :
    (Measure.infinitePi (fun _ : ℕ => letterLaw)).map
      (independentWordBlock width offset trial.val) =
      Measure.pi (fun _ : Fin width => letterLaw) := by
  have joint := independent_word_blocks_joint_law letterLaw trials width offset
  have evaluated := congrArg
    (fun law : Measure (Fin trials → Fin width → Alphabet) =>
      law.map (fun words => words trial)) joint
  dsimp only at evaluated
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at evaluated
  simpa only [Function.comp_def, (measurePreserving_eval
    (fun _ : Fin trials => Measure.pi (fun _ : Fin width => letterLaw)) trial).map_eq] using evaluated

theorem independent_word_blocks_independent
    {Alphabet : Type*} [MeasurableSpace Alphabet]
    (letterLaw : Measure Alphabet) [IsProbabilityMeasure letterLaw]
    (trials width offset : ℕ) :
    iIndepFun (fun trial : Fin trials => independentWordBlock width offset trial.val)
      (Measure.infinitePi (fun _ : ℕ => letterLaw)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun trial =>
    (measurable_pi_iff.mpr fun position =>
      measurable_pi_apply (offset + trial.val * width + position.val)).aemeasurable)).mpr
  rw [independent_word_blocks_joint_law]
  simp only [independent_word_block_law]

theorem ae_eventually_independent_word_block_success
    {Alphabet : Type*} [MeasurableSpace Alphabet]
    (letterLaw : Measure Alphabet) [IsProbabilityMeasure letterLaw]
    (good : ∀ width, Set (Fin width → Alphabet))
    (goodMeasurable : ∀ width, MeasurableSet (good width))
    (successMass : ∀ width, ENNReal.ofReal ((2 : ℝ) ^ width)⁻¹ ≤
      Measure.pi (fun _ : Fin width => letterLaw) (good width)) :
    ∀ᵐ sample ∂Measure.infinitePi (fun _ : ℕ => letterLaw),
      ∀ᶠ width in atTop, ∃ trial : Fin (renewalPhaseTrialCount width),
        independentWordBlock width 0 trial.val sample ∈ good width := by
  apply ae_eventually_independent_renewal_phase_success
    (Measure.infinitePi (fun _ : ℕ => letterLaw))
    (fun width trial => independentWordBlock width 0 trial.val)
    (fun width => independent_word_blocks_independent letterLaw _ width 0)
    good goodMeasurable
    (fun _ _ => by unfold independentWordBlock; fun_prop)
  intro width trial
  rw [← Measure.map_apply (by unfold independentWordBlock; fun_prop) (goodMeasurable width),
    independent_word_block_law letterLaw (renewalPhaseTrialCount width) width 0 trial]
  exact successMass width

end
end EIGS

#print axioms EIGS.independent_word_block_coordinates_injective
#print axioms EIGS.independent_word_blocks_joint_law
#print axioms EIGS.independent_word_block_law
#print axioms EIGS.independent_word_blocks_independent
#print axioms EIGS.ae_eventually_independent_word_block_success
