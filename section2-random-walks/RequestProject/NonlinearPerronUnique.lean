import RequestProject.NonlinearPerron

/-! Uniqueness of a normalized positive eigenvector from strong positivity. -/

namespace EIGS.RenormMap

open scoped BigOperators

variable {K : ℕ} (Ψ : EIGS.RenormMap K)

theorem positive_eigenvector_unique_of_strongly_positive (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i)
    {first second : Fin K → ℝ} {ρ : ℝ}
    (hfirst : ∀ i, 0 < first i) (hsecond : ∀ i, 0 < second i)
    (hfirst_sum : (∑ i, first i) = 1) (hsecond_sum : (∑ i, second i) = 1)
    (hfirst_eigen : Ψ.apply first = ρ • first)
    (hsecond_eigen : Ψ.apply second = ρ • second) : first = second := by
  classical
  have huniv : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  let ratio : ℝ := Finset.univ.inf' huniv (fun i => first i / second i)
  have ratio_pos : 0 < ratio := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i hi
    exact div_pos (hfirst i) (hsecond i)
  have ratio_bound : ratio • second ≤ first := by
    intro i
    exact (le_div_iff₀ (hsecond i)).mp (Finset.inf'_le _ (Finset.mem_univ i))
  obtain ⟨index, hindex, hratio⟩ := Finset.exists_mem_eq_inf' huniv
    (fun i => first i / second i)
  have contact : first index - ratio * second index = 0 := by
    have heq : ratio = first index / second index := hratio
    rw [heq, div_mul_cancel₀ _ (hsecond index).ne', sub_self]
  have hscalar : first = ratio • second := by
    by_contra hne
    have residual_nonneg : 0 ≤ first - ratio • second := sub_nonneg.mpr ratio_bound
    have residual_ne : first - ratio • second ≠ 0 := sub_ne_zero.mpr hne
    have hpositive := hstrong (first - ratio • second) residual_nonneg residual_ne index
    have hsuper := Ψ.apply_superadditive
      (smul_nonneg ratio_pos.le (fun i => (hsecond i).le)) residual_nonneg
    rw [add_sub_cancel, Ψ.apply_smul second ratio_pos.le,
      hfirst_eigen, hsecond_eigen] at hsuper
    have hbound := hsuper index
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbound
    have hcontact := congrArg (fun value : ℝ => ρ * value) contact
    nlinarith
  have ratio_one : ratio = 1 := by
    have h := congrArg (fun vector : Fin K → ℝ => ∑ i, vector i) hscalar
    simpa only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      hfirst_sum, hsecond_sum, mul_one] using h.symm
  simpa only [ratio_one, one_smul] using hscalar

theorem existsUnique_positive_normalized_eigenpair (hK : 0 < K)
    (hstrong : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ i, 0 < Ψ.apply vector i) :
    ∃! pair : (Fin K → ℝ) × ℝ,
      (∀ i, 0 < pair.1 i) ∧ 0 < pair.2 ∧ (∑ i, pair.1 i) = 1 ∧
      Ψ.apply pair.1 = pair.2 • pair.1 := by
  obtain ⟨vector, ρ, hvector, hρ, hsum, heigen⟩ :=
    Ψ.positive_eigenpair_of_strongly_positive hK hstrong
  refine ⟨(vector, ρ), ⟨hvector, hρ, hsum, heigen⟩, ?_⟩
  rintro ⟨other, σ⟩ ⟨hother, hσ, hother_sum, hother_eigen⟩
  have hσρ : σ = ρ := Ψ.eigenvalue_unique hK hother hvector hσ hρ
    hother_eigen heigen
  subst σ
  have hsame := Ψ.positive_eigenvector_unique_of_strongly_positive hK hstrong
    hother hvector hother_sum hsum hother_eigen heigen
  exact Prod.ext hsame rfl

end EIGS.RenormMap
