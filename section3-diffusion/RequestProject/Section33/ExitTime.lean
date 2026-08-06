import RequestProject.Section33.Exponents

/-!
# Section 3.3, step 4: the mean exit time (Lemma "heat-exit")

Lemma "heat-exit" of arXiv:2603.13798 states that for every `x` and all small
`r`,

`sup_{y ∈ B(x,r)} E_y[τ_{B(x,r)}] ≤ C_x r^{d_walk}`.

The paper's argument has three ingredients:

1. a *deterministic* comparison: if `y ∈ B(x,r)` then `B(x,r) ⊆ B(y,2r)`, hence
   `τ_{B(x,r)} ≤ τ_{B(y,2r)}` pathwise, so it suffices to bound
   `E_y[τ_{B(y,2r)}]` uniformly in `y`;
2. a Skorokhod coupling of the Poissonised walks `Y^{(n)}` with `W`, giving via
   Fatou `E_y[τ_{B(y,2r)} ∧ T] ≤ liminf_n E_{y_n}[τ_{B(y_n,2r+2η)}(Y^{(n)})]`;
3. the *discrete* mean exit-time bound of §2 (Theorem 2.23),
   `E_{y_n}[τ_{B(y_n,R)}(Y^{(n)})] ≲ R^{d_walk}`, uniform in `n` and `y_n`.

Ingredient 3 is the black box (it is quoted from §2), and the coupling in
ingredient 2 is quoted from the Skorokhod representation theorem.  What is proved
here is ingredient 1 and the two limit passages of ingredient 2 that the paper
performs itself: `T → ∞` (monotone convergence) and `η ↓ 0` (continuity of
`η ↦ C(2r+2η)^{d_walk}`).
-/

namespace IGS
namespace Sec33

open Filter Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- **The deterministic comparison of balls**: `y ∈ B(x,r)` implies `B(x,r) ⊆ B(y,2r)`. -/
lemma ball_subset_ball_two_mul {x y : X} {r : ℝ} (hy : y ∈ Metric.ball x r) :
    Metric.ball x r ⊆ Metric.ball y (2 * r) := by
  intro z hz
  rw [Metric.mem_ball] at *
  calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < r + r := by
        have hxy : dist x y < r := by rwa [dist_comm] at hy
        linarith
    _ = 2 * r := by ring

/--
**The limit passages of Lemma "heat-exit".**

`f T` is `E_y[τ_{B(y,2r)} ∧ T]`, which increases to the mean exit time `Etau`;
for every `η > 0` and every `T` the coupling plus the discrete bound give
`f T ≤ C (2r+2η)^{d_walk}`.  Letting `T → ∞` and then `η ↓ 0` yields
`Etau ≤ C (2r)^{d_walk}`.
-/
theorem mean_exit_le_of_truncated (f : ℝ → ℝ) (Etau C r dw : ℝ) (hr : 0 < r)
    (hlim : Tendsto f atTop (𝓝 Etau))
    (hbound : ∀ eta : ℝ, 0 < eta → ∀ T : ℝ, f T ≤ C * (2 * r + 2 * eta) ^ dw) :
    Etau ≤ C * (2 * r) ^ dw := by
  -- first `T → ∞` for each fixed `η`
  have hfix : ∀ eta : ℝ, 0 < eta → Etau ≤ C * (2 * r + 2 * eta) ^ dw := by
    intro eta heta
    exact le_of_tendsto hlim (Eventually.of_forall fun T => hbound eta heta T)
  -- then `η ↓ 0`, using continuity of `η ↦ C (2r+2η)^{d_walk}` at `0`
  have hcont : Tendsto (fun eta : ℝ => C * (2 * r + 2 * eta) ^ dw) (𝓝[>] (0:ℝ))
      (𝓝 (C * (2 * r) ^ dw)) := by
    have hbase : ContinuousAt (fun eta : ℝ => 2 * r + 2 * eta) 0 := by fun_prop
    have hpos : (2 : ℝ) * r + 2 * 0 ≠ 0 := by simp; linarith
    have h : ContinuousAt (fun eta : ℝ => C * (2 * r + 2 * eta) ^ dw) 0 :=
      ContinuousAt.mul continuousAt_const (hbase.rpow_const (Or.inl hpos))
    have h2 : Tendsto (fun eta : ℝ => C * (2 * r + 2 * eta) ^ dw) (𝓝[>] (0:ℝ))
        (𝓝 (C * (2 * r + 2 * 0) ^ dw)) :=
      h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h2
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact hfix eta heta

/--
**Lemma "heat-exit".**

`Eexp A y` denotes `E_y[τ_A]`.  Monotonicity in the domain (which follows from
the pathwise inequality proved in `ball_subset_ball_two_mul` and monotonicity of
the expectation) plus the uniform bound `E_y[τ_{B(y,2r)}] ≤ C (2r)^{d_walk}`
give the statement of the lemma, with the explicit constant `C 2^{d_walk}`.
-/
theorem heat_exit_bound (Eexp : Set X → X → ℝ) (x : X) (r C dw : ℝ) (hr : 0 < r)
    (hmono : ∀ A B : Set X, A ⊆ B → ∀ y, Eexp A y ≤ Eexp B y)
    (hloc : ∀ y : X, Eexp (Metric.ball y (2 * r)) y ≤ C * (2 * r) ^ dw) :
    ∀ y ∈ Metric.ball x r, Eexp (Metric.ball x r) y ≤ C * 2 ^ dw * r ^ dw := by
  intro y hy
  have h1 : Eexp (Metric.ball x r) y ≤ Eexp (Metric.ball y (2 * r)) y :=
    hmono _ _ (ball_subset_ball_two_mul hy) y
  have h2 : C * (2 * r) ^ dw = C * 2 ^ dw * r ^ dw := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt hr)]
    ring
  calc Eexp (Metric.ball x r) y ≤ Eexp (Metric.ball y (2 * r)) y := h1
    _ ≤ C * (2 * r) ^ dw := hloc y
    _ = C * 2 ^ dw * r ^ dw := h2

end Sec33
end IGS
