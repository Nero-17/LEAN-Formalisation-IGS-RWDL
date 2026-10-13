import RequestProject.Section31.TraceMin
import RequestProject.Section31.HarmonicSplines
import RequestProject.Section31.ProjectionTail
import RequestProject.Section31.SpeedMeasure
import RequestProject.Section31.DiscreteHarmonics
import RequestProject.Section31.ExitTime
import RequestProject.Section31.ContinuousStay
import RequestProject.Section31.Mosco

/-!
# §3.1: the end of the chain (Corollary `sec31_continuous_stay`)

Reference: arXiv:2603.13798, §3.1.

This file puts two of the previous steps together into one conditional theorem
that mirrors the actual logical shape of the end of §3.1:

`continuous_stay_of_coupling` — the stay estimate for the limit diffusion,
derived from

* the *discrete* stay estimate of Lemma `sec31_one_step_stay` (hypothesis
  `hstay`, whose arithmetic core is `stay_probability_lower`, itself fed by the
  exit-time bounds of §2), and
* the Skorokhod coupling coming from Theorem `sec31_ghps` (hypotheses `hG`,
  `hGmeas`: on the coupling, the discrete paths are uniformly `r/4`-close to the
  limit path with probability tending to `1`).

The conclusion is exactly the corollary's
`P_x(τ_{B(x,r)} > t_r) ≥ p_stay`, written as a lower bound for the probability
of the event that the limit path stays in `B(x,r)` up to time `t_r`.

`discrete_stay_probability` records the other half, the passage from the
two-sided mean exit-time bounds of §2 to the uniform stay probability.
-/

namespace IGS.Sec31

open MeasureTheory Filter Topology

/--
**Lemma `sec31_one_step_stay`, assembled.**

`A = a_n δ^{d_w}`.  Given the lower bound `c A ≤ E_x[τ]` from §2 and the strong
Markov estimate `E_x[τ] ≤ c A / 2 + C A · P_x(τ ≥ c A / 2)` (whose second
ingredient is the uniform upper bound `E_y[τ] ≤ C A` for all starting points
`y` in the ball), the stay probability is at least `c/(2C)`, uniformly in `n`,
`x` and `δ`.
-/
theorem discrete_stay_probability (A c C p Etau : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hlow : c * A ≤ Etau) (hup : Etau ≤ c * A / 2 + C * A * p) :
    c / (2 * C) ≤ p :=
  stay_probability_lower A c C p Etau hA hC hlow hup

/--
**Corollary `sec31_continuous_stay`.**

On the Skorokhod coupling of Theorem `sec31_ghps`, with starting points
`x_n → x` (`hxn`), a uniform discrete stay estimate at radius `δ ≤ r/2`
(`hstay`, from Lemma `sec31_one_step_stay`) and almost sure uniform closeness of
the coupled paths (`hG`), the limit diffusion `W` started at `x` stays in
`B(x,r)` up to time `t_r` with probability at least `p_stay`.
-/
theorem continuous_stay_of_coupling
    {X : Type*} [MetricSpace X] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (x : X) (xn : ℕ → X) (Y : ℕ → Ω → ℝ → X) (W : Ω → ℝ → X)
    (r delta tr pstay : ℝ)
    (hxn : ∀ n, dist (xn n) x < r / 4) (hdelta : delta ≤ r / 2)
    (hstay : ∀ n, pstay ≤ (P {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (Y n ω s) (xn n) ≤ delta}).toReal)
    (hGmeas : ∀ n, MeasurableSet {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (Y n ω s) (W ω s) < r / 4})
    (hG : Tendsto (fun n =>
      (P {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (Y n ω s) (W ω s) < r / 4}).toReal) atTop (𝓝 1)) :
    pstay ≤ (P {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (W ω s) x < r}).toReal := by
  refine le_measure_of_eventual_inclusion P pstay _
    (fun n => {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (Y n ω s) (xn n) ≤ delta})
    (fun n => {ω | ∀ s ∈ Set.Icc (0 : ℝ) tr, dist (Y n ω s) (W ω s) < r / 4})
    hGmeas hstay ?_ hG
  rintro n ω ⟨h1, h2⟩ s hs
  exact dist_lt_of_skorokhod_coupling x (xn n) (Y n ω s) (W ω s) r delta
    (hxn n) (h2 s hs) (h1 s hs) hdelta

end IGS.Sec31
