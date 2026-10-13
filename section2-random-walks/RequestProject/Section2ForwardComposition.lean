import RequestProject.Section2LocalBall

/-! Composition of the actual inherited-vertex inclusions, including the
dependent level index. No identification of different actual vertices is assumed. -/

namespace EIGS

variable {K : ℕ}

theorem xiForward_sigma_trans (system : EIGSData K) (initial first second : ℕ)
    (vertex : XiVtx system initial) :
    (⟨(initial + first) + second,
      xiForward system (initial + first) second (xiForward system initial first vertex)⟩ :
        Σ level, XiVtx system level) =
      ⟨initial + (first + second), xiForward system initial (first + second) vertex⟩ := by
  induction second with
  | zero => rfl
  | succ second induction_hypothesis =>
      have lifted := congrArg
        (fun point : Σ level, XiVtx system level =>
          (⟨point.1 + 1, Sum.inl point.2⟩ : Σ level, XiVtx system level))
        induction_hypothesis
      simpa only [xiForward, Nat.add_succ] using lifted

theorem xiForward_ball_card_trans (system : EIGSData K) (initial first second : ℕ)
    (vertex : XiVtx system initial) (radius : ℝ) :
    (finiteGraphBall (XiSimpleGraph system ((initial + first) + second))
      (xiForward system (initial + first) second (xiForward system initial first vertex)) radius).card =
    (finiteGraphBall (XiSimpleGraph system (initial + (first + second)))
      (xiForward system initial (first + second) vertex) radius).card := by
  exact congrArg
    (fun point : Σ level, XiVtx system level =>
      (finiteGraphBall (XiSimpleGraph system point.1) point.2 radius).card)
    (xiForward_sigma_trans system initial first second vertex)

end EIGS

#print axioms EIGS.xiForward_sigma_trans
#print axioms EIGS.xiForward_ball_card_trans
