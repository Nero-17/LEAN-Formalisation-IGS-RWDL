import RequestProject.Section31.EIGSUVFlowerWalkDimension
import RequestProject.Section31.EIGSFlowerWalkDimension

/-! Genuine two-path (2,3)-flower versus the two-branch, length-three DHL.
The legacy flowerSystem name denotes DHL and is not renamed here. Both
statements concern actual admissible finite-graph mean-exit limits, rather
than a comparison of scalar formulas alone. Candidate. -/

namespace EIGS
open Filter Topology
open scoped Classical
noncomputable section

theorem uvFlower23_actual_walk_dimension_gt_two
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, 2 < Real.log (6 : ℝ) / Real.log 2 ∧ ∀ initialLevel (vertex : XiVtx (uvFlowerSystem 2 3) initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (2 : ℝ) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (2 : ℝ) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph (uvFlowerSystem 2 3) (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph (uvFlowerSystem 2 3) (initialLevel + index))
            (xiForward (uvFlowerSystem 2 3) initialLevel index vertex) (radius index))
          (xiForward (uvFlowerSystem 2 3) initialLevel index vertex)) /
        Real.log (radius index)) atTop
          (𝓝 (Real.log (6 : ℝ) / Real.log 2)) := by
  have logarithmLower : 2 * Real.log (2 : ℝ) < Real.log 6 := by
    have bound := Real.log_lt_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) < 6)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at bound
    simpa only [Nat.cast_ofNat] using bound
  have exponentGreaterThanTwo : 2 < Real.log (6 : ℝ) / Real.log 2 :=
    (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr logarithmLower
  obtain ⟨buffer, actualLimit⟩ := uvFlowerSystem_admissible_walk_dimension_limit 2 3
    (by norm_num) (by norm_num) radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  refine ⟨buffer, exponentGreaterThanTwo, ?_⟩
  simpa only [min_eq_left (by norm_num : (2 : ℕ) ≤ 3), Nat.cast_ofNat,
    show (2 : ℝ) * 3 = 6 by norm_num] using actualLimit

theorem dhl23_actual_walk_dimension_eq_two
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, ∀ initialLevel (vertex : XiVtx (flowerSystem 2 3) initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (3 : ℝ) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (3 : ℝ) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph (flowerSystem 2 3) (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph (flowerSystem 2 3) (initialLevel + index))
            (xiForward (flowerSystem 2 3) initialLevel index vertex) (radius index))
          (xiForward (flowerSystem 2 3) initialLevel index vertex)) /
        Real.log (radius index)) atTop (nhds 2) := by
  exact flowerSystem_admissible_walk_dimension_limit 2 3 (by norm_num) (by norm_num)
    radiusLower radiusUpper radiusLowerPositive radiusUpperPositive

end
end EIGS

#print axioms EIGS.uvFlower23_actual_walk_dimension_gt_two
#print axioms EIGS.dhl23_actual_walk_dimension_eq_two
