import RequestProject.Section2
import Mathlib.Topology.Order.Compact

/-!
An elementary nonlinear Perron existence argument for Thomson maps.
The compact feasible set is defined by all linear flow energies, so no
unproved boundary-continuity or fixed-point theorem is used.
The strong positivity condition must still be verified for the concrete rules.
-/

namespace EIGS.RenormMap

open scoped BigOperators
open Set

variable {K : ℕ} (Ψ : EIGS.RenormMap K)

private def perronFeasible : Set (ℝ × (Fin K → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ (∑ i, p.2 i) = 1 ∧
    ∀ i θ, p.1 * p.2 i ≤ (Ψ.coord i).energy θ p.2}

private lemma perronFeasible_iff (p : ℝ × (Fin K → ℝ)) :
    p ∈ Ψ.perronFeasible ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ (∑ i, p.2 i) = 1 ∧ p.1 • p.2 ≤ Ψ.apply p.2 := by
  constructor
  · rintro ⟨hr, hx, hs, hflow⟩
    exact ⟨hr, hx, hs, fun i => le_ciInf (hflow i)⟩
  · rintro ⟨hr, hx, hs, hsub⟩
    refine ⟨hr, hx, hs, fun i θ => (hsub i).trans ?_⟩
    exact ciInf_le ((Ψ.coord i).bddBelow_energy hx) θ

private lemma perronFeasible_isClosed : IsClosed Ψ.perronFeasible := by
  have henergy (i : Fin K) (θ : (Ψ.coord i).F) :
      Continuous (fun p : ℝ × (Fin K → ℝ) => (Ψ.coord i).energy θ p.2) := by
    unfold EIGS.ThomsonData.energy
    fun_prop
  change IsClosed {p : ℝ × (Fin K → ℝ) | 0 ≤ p.1 ∧
    (∀ i, 0 ≤ p.2 i) ∧ (∑ i, p.2 i) = 1 ∧
    ∀ i θ, p.1 * p.2 i ≤ (Ψ.coord i).energy θ p.2}
  simp only [setOf_and, setOf_forall]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_iInter fun i => isClosed_iInter fun θ =>
          isClosed_le (by fun_prop) (henergy i θ))))

private lemma perronFeasible_bound {p : ℝ × (Fin K → ℝ)}
    (hp : p ∈ Ψ.perronFeasible) :
    p.1 ≤ ∑ i, Ψ.apply (fun _ => 1) i := by
  obtain ⟨hr, hx, hs, hsub⟩ := (Ψ.perronFeasible_iff p).mp hp
  have hxone : p.2 ≤ (fun _ => 1) := by
    intro i
    calc
      p.2 i ≤ ∑ j, p.2 j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      _ = 1 := hs
  have hmono := Ψ.apply_mono hx hxone
  calc
    p.1 = ∑ i, p.1 * p.2 i := by rw [← Finset.mul_sum, hs, mul_one]
    _ ≤ ∑ i, Ψ.apply p.2 i := Finset.sum_le_sum (fun i _ => hsub i)
    _ ≤ ∑ i, Ψ.apply (fun _ => 1) i := Finset.sum_le_sum (fun i _ => hmono i)

private lemma perronFeasible_isCompact : IsCompact Ψ.perronFeasible := by
  apply IsCompact.of_isClosed_subset
    (s := Icc (0 : ℝ × (Fin K → ℝ))
      ((∑ i, Ψ.apply (fun _ => 1) i), fun _ => 1)) isCompact_Icc
    Ψ.perronFeasible_isClosed
  intro p hp
  obtain ⟨hr, hx, hs, hsub⟩ := (Ψ.perronFeasible_iff p).mp hp
  exact ⟨⟨hr, hx⟩, Ψ.perronFeasible_bound hp, fun i => by
    calc
      p.2 i ≤ ∑ j, p.2 j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      _ = 1 := hs⟩

private lemma perronFeasible_normalize {ρ : ℝ} {vector : Fin K → ℝ}
    (hρ : 0 ≤ ρ) (hvector : 0 ≤ vector) (hsum : 0 < ∑ i, vector i)
    (hsub : ρ • vector ≤ Ψ.apply vector) :
    (ρ, (∑ i, vector i)⁻¹ • vector) ∈ Ψ.perronFeasible := by
  apply (Ψ.perronFeasible_iff _).mpr
  refine ⟨hρ, fun i => mul_nonneg (inv_nonneg.mpr hsum.le) (hvector i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hsum.ne'
  · rw [Ψ.apply_smul vector (inv_nonneg.mpr hsum.le)]
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hsub i) (inv_nonneg.mpr hsum.le)

/-- Nonlinear Perron existence for a strongly positive Thomson map.
Strong positivity is a structural condition to be proved from the rule graphs,
not an eigenpair or convergence hypothesis. -/
theorem positive_eigenpair_of_strongly_positive (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i) :
    ∃ (vector : Fin K → ℝ) (ρ : ℝ),
      (∀ i, 0 < vector i) ∧ 0 < ρ ∧ (∑ i, vector i) = 1 ∧
      Ψ.apply vector = ρ • vector := by
  classical
  let initialIndex : Fin K := ⟨0, hK⟩
  let initial : Fin K → ℝ := Pi.single initialIndex 1
  have initial_nonneg : 0 ≤ initial := by
    intro i
    simp only [initial, Pi.single_apply]
    split_ifs <;> norm_num
  have initial_ne : initial ≠ 0 := by
    intro h
    have hi := congrFun h initialIndex
    simpa [initial] using hi
  have initial_sum : (∑ i, initial i) = 1 := by simp [initial]
  have initial_positive := hstrong initial initial_nonneg initial_ne
  have initial_feasible : (Ψ.apply initial initialIndex, initial) ∈ Ψ.perronFeasible := by
    apply (Ψ.perronFeasible_iff _).mpr
    refine ⟨(initial_positive initialIndex).le, initial_nonneg, initial_sum, ?_⟩
    intro i
    by_cases hi : i = initialIndex
    · subst i
      simp [initial]
    · simpa [initial, Pi.single_apply, hi, Ne.symm hi] using (initial_positive i).le
  obtain ⟨⟨ρ, vector⟩, hfeasible, hmax⟩ := Ψ.perronFeasible_isCompact.exists_isMaxOn
    ⟨_, initial_feasible⟩ continuous_fst.continuousOn
  obtain ⟨hρ, hvector, hsum, hsub⟩ := (Ψ.perronFeasible_iff _).mp hfeasible
  have hρpos : 0 < ρ := lt_of_lt_of_le (initial_positive initialIndex)
    (hmax initial_feasible)
  have hvector_ne : vector ≠ 0 := by
    intro h
    simp [h] at hsum
  have himage := hstrong vector hvector hvector_ne
  have heigen : Ψ.apply vector = ρ • vector := by
    by_contra hne
    have residual_nonneg : 0 ≤ Ψ.apply vector - ρ • vector := sub_nonneg.mpr hsub
    have residual_ne : Ψ.apply vector - ρ • vector ≠ 0 := sub_ne_zero.mpr hne
    have residual_image_positive := hstrong (Ψ.apply vector - ρ • vector)
      residual_nonneg residual_ne
    have huniv : (Finset.univ : Finset (Fin K)).Nonempty := ⟨initialIndex, Finset.mem_univ _⟩
    let improvement : ℝ := Finset.univ.inf' huniv
      (fun i => Ψ.apply (Ψ.apply vector - ρ • vector) i / Ψ.apply vector i)
    have improvement_pos : 0 < improvement := by
      apply (Finset.lt_inf'_iff _).mpr
      intro i hi
      exact div_pos (residual_image_positive i) (himage i)
    have improvement_bound (i : Fin K) :
        improvement * Ψ.apply vector i ≤ Ψ.apply (Ψ.apply vector - ρ • vector) i := by
      apply (le_div_iff₀ (himage i)).mp
      exact Finset.inf'_le _ (Finset.mem_univ i)
    have himage_nonneg : 0 ≤ Ψ.apply vector := fun i => (himage i).le
    have hsuper := Ψ.apply_superadditive
      (smul_nonneg hρ hvector) residual_nonneg
    rw [add_sub_cancel, Ψ.apply_smul vector hρ] at hsuper
    have hbetter : (ρ + improvement) • Ψ.apply vector ≤ Ψ.apply (Ψ.apply vector) := by
      intro i
      have hb := improvement_bound i
      have hs := hsuper i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs ⊢
      nlinarith
    have himage_sum : 0 < ∑ i, Ψ.apply vector i :=
      Finset.sum_pos (fun i _ => himage i) huniv
    have hnormalized := Ψ.perronFeasible_normalize (add_nonneg hρ improvement_pos.le)
      himage_nonneg himage_sum hbetter
    have hcontradiction : ρ + improvement ≤ ρ := hmax hnormalized
    linarith
  refine ⟨vector, ρ, ?_, hρpos, hsum, heigen⟩
  intro i
  have hmul : 0 < ρ * vector i := by
    simpa only [heigen, Pi.smul_apply, smul_eq_mul] using himage i
  exact pos_of_mul_pos_right hmul hρ

end EIGS.RenormMap
