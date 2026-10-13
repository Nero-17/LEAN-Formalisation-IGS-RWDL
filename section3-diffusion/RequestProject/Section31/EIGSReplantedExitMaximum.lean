import RequestProject.Section31.EIGSReplantedSkeletonDuration

namespace EIGS
open scoped Classical
noncomputable section
variable {K : ℕ}

/-- The actual largest two-terminal exit expectation over all initial
colours and all vertices at this level. -/
def xiReplantedTerminalExitMaximum (system : EIGSData K) (level : ℕ) : ℝ := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  exact Finset.univ.sup' Finset.univ_nonempty (fun colour : Fin K =>
    Finset.univ.sup' ⟨xiPositiveTerminal {system with initCol := colour} level, Finset.mem_univ _⟩
      (fun vertex : XiVtx {system with initCol := colour} level =>
      expExit (XiSimpleGraph {system with initCol := colour} level)
        ({xiPositiveTerminal {system with initCol := colour} level,
          xiNegativeTerminal {system with initCol := colour} level} : Finset _)ᶜ vertex))

theorem xiReplantedTerminalExit_le_maximum (system : EIGSData K) (level : ℕ)
    (colour : Fin K) (vertex : XiVtx {system with initCol := colour} level) :
    expExit (XiSimpleGraph {system with initCol := colour} level)
        ({xiPositiveTerminal {system with initCol := colour} level,
          xiNegativeTerminal {system with initCol := colour} level} : Finset _)ᶜ vertex ≤
      xiReplantedTerminalExitMaximum system level := by
  unfold xiReplantedTerminalExitMaximum
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ colour))
  exact Finset.le_sup' _ (Finset.mem_univ vertex)

theorem xiReplantedTerminalExitMaximum_le (system : EIGSData K) (level : ℕ) {upper : ℝ}
    (bound : ∀ colour (vertex : XiVtx {system with initCol := colour} level),
      expExit (XiSimpleGraph {system with initCol := colour} level)
        ({xiPositiveTerminal {system with initCol := colour} level,
          xiNegativeTerminal {system with initCol := colour} level} : Finset _)ᶜ vertex ≤ upper) :
    xiReplantedTerminalExitMaximum system level ≤ upper := by
  apply Finset.sup'_le
  intro colour _
  apply Finset.sup'_le
  intro vertex _
  exact bound colour vertex

theorem xiReplantedTerminalExitMaximum_nonnegative (system : EIGSData K) (level : ℕ) :
    0 ≤ xiReplantedTerminalExitMaximum system level :=
  (expExit_nonneg (xiPositiveTerminal system level)).trans
    (xiReplantedTerminalExit_le_maximum system level system.initCol
      (xiPositiveTerminal system level))

theorem xiReplantedTerminalExitMaximum_zero (system : EIGSData K) :
    xiReplantedTerminalExitMaximum system 0 = 0 := by
  apply le_antisymm _ (xiReplantedTerminalExitMaximum_nonnegative system 0)
  apply xiReplantedTerminalExitMaximum_le
  intro colour vertex
  have outside : vertex ∉
      ({xiPositiveTerminal {system with initCol := colour} 0,
        xiNegativeTerminal {system with initCol := colour} 0} : Finset _)ᶜ := by
    cases vertex <;> simp [xiPositiveTerminal, xiNegativeTerminal]
  rw [expExit_zero_of_notMem outside]

end
end EIGS

#print axioms EIGS.xiReplantedTerminalExit_le_maximum
#print axioms EIGS.xiReplantedTerminalExitMaximum_le
#print axioms EIGS.xiReplantedTerminalExitMaximum_nonnegative
#print axioms EIGS.xiReplantedTerminalExitMaximum_zero
