import RequestProject.Outlook.GreenRuleAudit

/-! User-adopted critical boundary matrix, with the three green-rule entries
derived from the original figure. This is a critical-point matrix only.
The old `EN` remains the displayed-source formula for reproducible error audits.
No old spectral-radius theorem is transferred to this new matrix here. -/

namespace Outlook

noncomputable def correctedCriticalEN : Matrix (Fin 8) (Fin 8) ℝ :=
  fun row column =>
    if row = 4 ∧ column = 0 then 2 * Reduced.pc ^ 2
    else if row = 4 ∧ column = 4 then 2 * Reduced.pc
    else if row = 5 ∧ column = 5 then 2 * Reduced.pc ^ 2
    else EN Reduced.pc row column

theorem correctedCriticalEN_green_entries :
    correctedCriticalEN 4 0 = 2 * Reduced.pc ^ 2 ∧
    correctedCriticalEN 4 4 = 2 * Reduced.pc ∧
    correctedCriticalEN 5 5 = 2 * Reduced.pc ^ 2 := by
  simp [correctedCriticalEN]

theorem correctedCriticalEN_green_entries_match_figure :
    correctedCriticalEN 4 0 = GreenRuleAudit.expected Reduced.pc
      (fun outcome => GreenRuleAudit.boundaryCount outcome 0 0) ∧
    correctedCriticalEN 4 4 = GreenRuleAudit.expected Reduced.pc
      (fun outcome => GreenRuleAudit.boundaryCount outcome 0 2) ∧
    correctedCriticalEN 5 5 = GreenRuleAudit.expected Reduced.pc
      (fun outcome => GreenRuleAudit.incomingCount outcome 2 2) := by
  obtain ⟨_, red, green, incoming⟩ := GreenRuleAudit.critical_figure_counts
  exact ⟨by simpa [correctedCriticalEN] using red.symm,
    by simpa [correctedCriticalEN] using green.symm,
    by simpa [correctedCriticalEN] using incoming.symm⟩

theorem correctedCriticalEN_eq_displayed_elsewhere (row column : Fin 8)
    (not_positive_red : ¬ (row = 4 ∧ column = 0))
    (not_positive_green : ¬ (row = 4 ∧ column = 4))
    (not_negative_green : ¬ (row = 5 ∧ column = 5)) :
    correctedCriticalEN row column = EN Reduced.pc row column := by
  simp [correctedCriticalEN, not_positive_red, not_positive_green, not_negative_green]

end Outlook

#print axioms Outlook.correctedCriticalEN_green_entries
#print axioms Outlook.correctedCriticalEN_green_entries_match_figure
#print axioms Outlook.correctedCriticalEN_eq_displayed_elsewhere
