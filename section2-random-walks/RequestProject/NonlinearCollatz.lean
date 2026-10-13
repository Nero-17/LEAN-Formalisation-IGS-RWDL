import RequestProject.NonlinearPerronUnique

/-! Elementary Collatz comparison, proved at a contact coordinate. -/

namespace EIGS.RenormMap

variable {K : ℕ} (renormalization : EIGS.RenormMap K)

theorem subvalue_le_supervalue (colours_positive : 0 < K)
    (subvector supervector : Fin K → ℝ) (subvalue supervalue : ℝ)
    (subvector_positive : ∀ colour, 0 < subvector colour)
    (supervector_positive : ∀ colour, 0 < supervector colour)
    (subsolution : subvalue • subvector ≤ renormalization.apply subvector)
    (supersolution : renormalization.apply supervector ≤ supervalue • supervector) :
    subvalue ≤ supervalue := by
  classical
  haveI : Nonempty (Fin K) := ⟨⟨0, colours_positive⟩⟩
  obtain ⟨contact, _, maximal⟩ := Finset.univ.exists_max_image
    (fun colour : Fin K => subvector colour / supervector colour) Finset.univ_nonempty
  let scale : ℝ := subvector contact / supervector contact
  have scale_positive : 0 < scale :=
    div_pos (subvector_positive contact) (supervector_positive contact)
  have vector_bound : subvector ≤ scale • supervector := by
    intro colour
    exact (div_le_iff₀ (supervector_positive colour)).mp
      (maximal colour (Finset.mem_univ colour))
  have contact_eq : scale * supervector contact = subvector contact :=
    div_mul_cancel₀ _ (supervector_positive contact).ne'
  have images_bound := renormalization.apply_mono
    (fun colour => (subvector_positive colour).le) vector_bound
  rw [renormalization.apply_smul supervector scale_positive.le] at images_bound
  have contact_bound : subvalue * subvector contact ≤
      scale * (supervalue * supervector contact) :=
    (subsolution contact).trans ((images_bound contact).trans
      (mul_le_mul_of_nonneg_left (supersolution contact) scale_positive.le))
  have final_bound : subvalue * subvector contact ≤ supervalue * subvector contact := by
    calc
      subvalue * subvector contact ≤ scale * (supervalue * supervector contact) := contact_bound
      _ = supervalue * subvector contact := by rw [mul_left_comm, contact_eq]
  exact (mul_le_mul_iff_left₀ (subvector_positive contact)).mp final_bound

theorem eigenvalue_le_of_positive_supervector (colours_positive : 0 < K)
    (vector supervector : Fin K → ℝ) (rate bound : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour)
    (supervector_positive : ∀ colour, 0 < supervector colour)
    (eigenpair : renormalization.apply vector = rate • vector)
    (supersolution : renormalization.apply supervector ≤ bound • supervector) : rate ≤ bound :=
  renormalization.subvalue_le_supervalue colours_positive vector supervector rate bound
    vector_positive supervector_positive eigenpair.ge supersolution

end EIGS.RenormMap
