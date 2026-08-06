import RequestProject.Section33.Skeleton

/-!
# Section 3.3: the birth-level dichotomy in the proof of Lemma "heat-volume"

The current version of §3.3 of arXiv:2603.13798 spells out the last step of the
volume estimate at a `μ`-almost every infinite-born point.  Once Borel–Cantelli
has produced, for large `m`, a terminal `v_m(x)` of the level-`m` cell containing
`x` with

* `d(x, v_m(x)) ≤ C_* ρ_min(D)^{-m}` (so that `B(x, cρ_min(D)^{-m})` is contained
  in `B(v_m(x), (c+C_*)ρ_min(D)^{-m})`), and
* birth level `b_m > m - L_m`, because `x ∉ E_{m,L_m}`,

the paper distinguishes two cases, according to whether the vertex `v_m(x)` is
*old enough* for the uniform finite-born estimate to apply at the scale
`ρ_min(D)^{-m}`:

* if `b_m + c₁ ≤ m`, the uniform finite-born estimate gives
  `μ(B) ≲ ρ(N)^{m-b_m}ρ(M)^{-m} ≤ ρ(N)^{L_m}ρ(M)^{-m}`;
* if `m < b_m + c₁`, the ball is contained in a ball of the *birth* scale and the
  estimate there gives `μ(B) ≲ ρ(M)^{-b_m} ≤ ρ(M)^{c₁}ρ(M)^{-m}`.

Both cases end at `≲ ρ(N)^{L_m}ρ(M)^{-m}`, which is the input of
`Section33.VolumeAE`.  This file proves

* the elementary geometry (`ball_subset_ball_of_near_terminal`),
* the consequence of avoiding the skeleton neighbourhood
  (`birth_level_gt_of_notMem`),
* the arithmetic of the dichotomy (`geom_bound_of_birth_dichotomy`), and
* their combination (`volume_le_of_avoiding_skeleton`).

The two quoted estimates themselves (the uniform finite-born bound of §2 and the
bound at the birth scale) are hypotheses, exactly as in the paper.
-/

namespace IGS
namespace Sec33

open Real MeasureTheory Metric

/--
**The geometric step.**  If a terminal `v` is within `C_* s` of `x`, then the
ball of radius `c s` around `x` sits inside the ball of radius `(c + C_*) s`
around `v`.
-/
theorem ball_subset_ball_of_near_terminal {X : Type*} [PseudoMetricSpace X] (x v : X)
    {c Cstar s : ℝ} (hd : dist x v ≤ Cstar * s) :
    Metric.ball x (c * s) ⊆ Metric.ball v ((c + Cstar) * s) := by
  refine Metric.ball_subset_ball' ?_
  have : c * s + dist x v ≤ c * s + Cstar * s := by linarith
  calc c * s + dist x v ≤ c * s + Cstar * s := this
    _ = (c + Cstar) * s := by ring

/--
**The consequence of avoiding `E_{m,L}`.**  If every point within `rad` of a
vertex of birth level at most `j` belongs to `E`, and `x ∉ E` has a vertex `v`
within `rad`, then the birth level of `v` exceeds `j`.
-/
theorem birth_level_gt_of_notMem' {X Vtx : Type*} [PseudoMetricSpace X]
    (birth : Vtx → ℕ) (pt : Vtx → X) (E : Set X) (x : X) (v : Vtx) (j : ℕ) {rad : ℝ}
    (hE : ∀ w : Vtx, birth w ≤ j → ∀ y : X, dist y (pt w) ≤ rad → y ∈ E)
    (hx : x ∉ E) (hd : dist x (pt v) ≤ rad) :
    j < birth v := by
  by_contra h
  push_neg at h
  exact hx (hE v h x hd)

namespace Params

variable (P : Params)

/--
**The arithmetic of the dichotomy.**

`bm` is the birth level of the nearby terminal, `L` the skeleton parameter (so
`m < bm + L`), `c₁` the fixed integer of the paper.  Whichever of the two cases
occurs, the resulting bound is at most `(C ρ(M)^{c₁}) ρ(N)^{L} ρ(M)^{-m}`.
-/
theorem geom_bound_of_birth_dichotomy {C V : ℝ} (hC : 0 ≤ C)
    (m L bm c1 : ℕ) (hbm : bm ≤ m) (hL : m < bm + L)
    (hold : bm + c1 ≤ m → V ≤ C * (P.rN ^ (m - bm) * P.rM ^ (-(m : ℝ))))
    (hyoung : m < bm + c1 → V ≤ C * P.rM ^ (-(bm : ℝ))) :
    V ≤ (C * P.rM ^ (c1 : ℝ)) * (P.rN ^ L * P.rM ^ (-(m : ℝ))) := by
  have hMc1 : (1:ℝ) ≤ P.rM ^ (c1 : ℝ) :=
    Real.one_le_rpow (le_of_lt P.rM_one_lt) (Nat.cast_nonneg c1)
  have hNL : (1:ℝ) ≤ P.rN ^ L := one_le_pow₀ (le_of_lt P.hrN)
  have hMm : (0:ℝ) < P.rM ^ (-(m : ℝ)) := Real.rpow_pos_of_pos P.rM_pos _
  rcases le_or_gt (bm + c1) m with h | h
  · -- old terminal: the uniform finite-born estimate at scale `m`
    have hV := hold h
    have hmono : P.rN ^ (m - bm) ≤ P.rN ^ L :=
      pow_le_pow_right₀ (le_of_lt P.hrN) (by omega)
    calc V ≤ C * (P.rN ^ (m - bm) * P.rM ^ (-(m : ℝ))) := hV
      _ ≤ C * (P.rN ^ L * P.rM ^ (-(m : ℝ))) := by
          have : P.rN ^ (m - bm) * P.rM ^ (-(m : ℝ)) ≤ P.rN ^ L * P.rM ^ (-(m : ℝ)) :=
            mul_le_mul_of_nonneg_right hmono (le_of_lt hMm)
          exact mul_le_mul_of_nonneg_left this hC
      _ ≤ (C * P.rM ^ (c1 : ℝ)) * (P.rN ^ L * P.rM ^ (-(m : ℝ))) := by
          have hprod : (0:ℝ) ≤ P.rN ^ L * P.rM ^ (-(m : ℝ)) := by positivity
          nlinarith [mul_nonneg (mul_nonneg hC hprod) (sub_nonneg.2 hMc1)]
  · -- young terminal: the estimate at the birth scale
    have hV := hyoung h
    have hexp : -(bm : ℝ) ≤ (c1 : ℝ) + -(m : ℝ) := by
      have : (m : ℝ) < (bm : ℝ) + (c1 : ℝ) := by exact_mod_cast h
      linarith
    have hpow : P.rM ^ (-(bm : ℝ)) ≤ P.rM ^ ((c1 : ℝ) + -(m : ℝ)) :=
      Real.rpow_le_rpow_left_iff P.rM_one_lt |>.2 hexp
    have hsplit : P.rM ^ ((c1 : ℝ) + -(m : ℝ)) = P.rM ^ (c1 : ℝ) * P.rM ^ (-(m : ℝ)) :=
      Real.rpow_add P.rM_pos _ _
    calc V ≤ C * P.rM ^ (-(bm : ℝ)) := hV
      _ ≤ C * (P.rM ^ (c1 : ℝ) * P.rM ^ (-(m : ℝ))) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hpow hC
      _ ≤ (C * P.rM ^ (c1 : ℝ)) * (P.rN ^ L * P.rM ^ (-(m : ℝ))) := by
          have hMc1pos : (0:ℝ) < P.rM ^ (c1 : ℝ) := Real.rpow_pos_of_pos P.rM_pos _
          have hCM : (0:ℝ) ≤ C * P.rM ^ (c1 : ℝ) := mul_nonneg hC (le_of_lt hMc1pos)
          nlinarith [mul_nonneg (mul_nonneg hCM (le_of_lt hMm)) (sub_nonneg.2 hNL)]

/--
**Lemma "heat-volume": the estimate at a point avoiding the skeleton
neighbourhood.**

All the geometric and combinatorial inputs are the hypotheses:

* `hE` describes the skeleton neighbourhood `E_{m,L}` (every point within
  `C_*ρ_min(D)^{-m}` of a vertex of birth level `≤ j` belongs to it), and `hx`
  says that `x` avoids it — this is the Borel–Cantelli output;
* `hnear` is the existence of the nearby terminal `v = v_m(x)`;
* `hold` is the *uniform* finite-born estimate of §2, applicable because the
  birth level is at most `m - c₁`;
* `hyoung` is the same estimate applied at the birth scale.

The conclusion is the bound `μ(B(x,cρ_min(D)^{-m})) ≲ ρ(N)^{L}ρ(M)^{-m}` which
feeds `Params.volume_upper_log`.
-/
theorem volume_le_of_avoiding_skeleton {X Vtx : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (birth : Vtx → ℕ) (pt : Vtx → X) (E : Set X) (x : X) (v : Vtx)
    (m L c1 j : ℕ) {C c Cstar : ℝ} (hC : 0 ≤ C)
    (hjL : m ≤ j + L) (hbm : birth v ≤ m)
    (hE : ∀ w : Vtx, birth w ≤ j →
      ∀ y : X, dist y (pt w) ≤ Cstar * P.rD ^ (-(m : ℝ)) → y ∈ E)
    (hx : x ∉ E) (hnear : dist x (pt v) ≤ Cstar * P.rD ^ (-(m : ℝ)))
    (hold : birth v + c1 ≤ m →
      (mu (Metric.ball (pt v) ((c + Cstar) * P.rD ^ (-(m : ℝ))))).toReal
        ≤ C * (P.rN ^ (m - birth v) * P.rM ^ (-(m : ℝ))))
    (hyoung : m < birth v + c1 →
      (mu (Metric.ball (pt v) ((c + Cstar) * P.rD ^ (-(m : ℝ))))).toReal
        ≤ C * P.rM ^ (-(birth v : ℝ))) :
    (mu (Metric.ball x (c * P.rD ^ (-(m : ℝ))))).toReal
      ≤ (C * P.rM ^ (c1 : ℝ)) * (P.rN ^ L * P.rM ^ (-(m : ℝ))) := by
  -- the terminal is young: its birth level exceeds `j ≥ m - L`
  have hbirth : j < birth v :=
    birth_level_gt_of_notMem' birth pt E x v j hE hx hnear
  have hmL : m < birth v + L := by omega
  -- the ball around `x` is contained in the ball around the terminal
  have hsub : Metric.ball x (c * P.rD ^ (-(m : ℝ)))
      ⊆ Metric.ball (pt v) ((c + Cstar) * P.rD ^ (-(m : ℝ))) :=
    ball_subset_ball_of_near_terminal x (pt v) hnear
  have hmono : (mu (Metric.ball x (c * P.rD ^ (-(m : ℝ))))).toReal
      ≤ (mu (Metric.ball (pt v) ((c + Cstar) * P.rD ^ (-(m : ℝ))))).toReal :=
    ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono hsub)
  refine P.geom_bound_of_birth_dichotomy hC m L (birth v) c1 hbm hmL ?_ ?_
  · exact fun h => le_trans hmono (hold h)
  · exact fun h => le_trans hmono (hyoung h)

end Params

end Sec33
end IGS
