import RequestProject.Section31.EIGSDHLRetentionWords
import RequestProject.Section31.IndependentWordBlocks
import Mathlib.Probability.Distributions.Uniform

/-! The good retention words have probability exactly 2^-width under actual
independent uniform child letters. There are 2^width such words among the
4^width edge words, by the proved injective branch coding. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section

def dhlLetterLaw : Measure (Fin 2 × Fin 2) := (PMF.uniformOfFintype (Fin 2 × Fin 2)).toMeasure

instance dhlLetterLaw_probability : IsProbabilityMeasure dhlLetterLaw := by
  unfold dhlLetterLaw
  infer_instance

def dhlGoodRetentionWords (width : ℕ) (head : Bool) : Set (Fin width → Fin 2 × Fin 2) :=
  Set.range (dhlRetentionWord width head)

theorem dhlGoodRetentionWords_measurable (width : ℕ) (head : Bool) :
    MeasurableSet (dhlGoodRetentionWords width head) := (Set.toFinite _).measurableSet

theorem dhlGoodRetentionWords_card (width : ℕ) (head : Bool) :
    Fintype.card (dhlGoodRetentionWords width head) = 2 ^ width := by
  calc
    Fintype.card (dhlGoodRetentionWords width head) = Nat.card (dhlGoodRetentionWords width head) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (Fin width → Fin 2) :=
      Nat.card_congr (Equiv.ofInjective (dhlRetentionWord width head)
        (dhlRetentionWord_injective width head)).symm
    _ = 2 ^ width := by rw [Nat.card_eq_fintype_card]; simp

theorem dhlUniformWordLaw (width : ℕ) :
    Measure.pi (fun _ : Fin width => dhlLetterLaw) =
      (PMF.uniformOfFintype (Fin width → Fin 2 × Fin 2)).toMeasure := by
  apply Measure.ext_of_singleton
  intro word
  simp [Measure.pi_singleton, dhlLetterLaw, PMF.toMeasure_apply_singleton,
    Fintype.card_pi, ← ENNReal.inv_pow]

theorem dhlGoodRetentionWords_mass (width : ℕ) (head : Bool) :
    Measure.pi (fun _ : Fin width => dhlLetterLaw) (dhlGoodRetentionWords width head) =
      ENNReal.ofReal ((2 : ℝ) ^ width)⁻¹ := by
  rw [dhlUniformWordLaw, PMF.toMeasure_uniformOfFintype_apply _
    (dhlGoodRetentionWords_measurable width head), dhlGoodRetentionWords_card]
  simp only [Fintype.card_pi, Fintype.card_prod, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_ofNat]
  have four : (2 : ℝ≥0∞) * 2 = 4 := by norm_num
  rw [four, ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) width),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [div_eq_mul_inv, ENNReal.inv_pow, ENNReal.inv_pow, ← mul_pow]
  congr 1
  rw [← four, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr (by norm_num)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

theorem dhlLetters_ae_eventually_retention_phase :
    ∀ᵐ sample ∂Measure.infinitePi (fun _ : ℕ => dhlLetterLaw),
      ∀ᶠ width in atTop, ∃ trial : Fin (renewalPhaseTrialCount width),
        independentWordBlock width 0 trial.val sample ∈ dhlGoodRetentionWords width false := by
  apply ae_eventually_independent_word_block_success dhlLetterLaw
    (fun width => dhlGoodRetentionWords width false)
    (fun width => dhlGoodRetentionWords_measurable width false)
  intro width
  rw [dhlGoodRetentionWords_mass]

end
end EIGS

#print axioms EIGS.dhlGoodRetentionWords_card
#print axioms EIGS.dhlUniformWordLaw
#print axioms EIGS.dhlGoodRetentionWords_mass
#print axioms EIGS.dhlLetters_ae_eventually_retention_phase
