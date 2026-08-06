import RequestProject.Section31.ExitTime

/-!
# §3.1: the chaining bookkeeping of Theorem `sec31_discrete_eld_tightness`

Reference: arXiv:2603.13798, §3.1, Theorem `thm:sec31_discrete_eld_tightness`.

The paper's proof is:

> Choose `δ ≍ (t/r)^{1/(d_w-1)}` with `16δ ≤ r`, define radial stopping times as
> in the standard chaining proof, and let `I_k` record the event that the `k`-th
> radial increment takes at least `c_stay a_n (δ/8)^{d_w}` time. […] If the walk
> exits `B(x,r)` by time `a_n t`, then the number of long increments must be
> abnormally small.  Azuma–Hoeffding therefore yields the stated lower-tail
> estimate.

`ExitTime.lean` already proves the two scaling identities that fix `δ`.  This
file proves the *bookkeeping* that turns them into the stated bound:

* `exit_subset_of_few_long_increments` — the deterministic inclusion of events
  `{τ ≤ t} ⊆ {S_N ≤ t/Δ}`, where `S_N` counts the long increments and `Δ` is the
  length of a long increment (the exit time is at least `Δ` times the number of
  long increments, because those increments occupy disjoint time intervals
  before the exit);
* `exit_prob_le_of_azuma` — combining it with the Azuma–Hoeffding lower-tail
  bound (a hypothesis, as in the paper) gives
  `P(τ ≤ t) ≤ C exp(-c N)`;
* `discrete_eld_tail_bound` — inserting the paper's choice of `δ`, for which
  `N = r/δ = (r^{d_w}/t)^{1/(d_w-1)}` by `radial_step_count`, gives exactly the
  displayed estimate
  `P(τ ≤ t) ≤ C exp[-c (r^{d_w}/t)^{1/(d_w-1)}]`.

Azuma–Hoeffding itself and Aldous' tightness criterion remain black boxes, as in
the paper.
-/

namespace IGS.Sec31

open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/--
**The deterministic step.**  If the exit time is at least `Δ` times the number
`S` of long increments, then exiting before time `t` forces `S ≤ t/Δ`.
-/
theorem exit_subset_of_few_long_increments (tau S : Ω → ℝ) (Δ t : ℝ) (hΔ : 0 < Δ)
    (hlower : ∀ ω, Δ * S ω ≤ tau ω) :
    {ω | tau ω ≤ t} ⊆ {ω | S ω ≤ t / Δ} := by
  intro ω hω
  have h : Δ * S ω ≤ t := le_trans (hlower ω) hω
  rw [Set.mem_setOf_eq, le_div_iff₀ hΔ]
  linarith [h, mul_comm Δ (S ω)]

/--
**Theorem `sec31_discrete_eld_tightness`, probabilistic step.**
`S` counts the long increments, each of which lasts at least `Δ`; `hazuma` is
the Azuma–Hoeffding lower-tail bound for `S` at the level `t/Δ` (the paper's
"the number of long increments must be abnormally small"), and the conclusion is
the exit-time tail estimate.
-/
theorem exit_prob_le_of_azuma (P : Measure Ω) (tau S : Ω → ℝ) (Δ t bound : ℝ) (hΔ : 0 < Δ)
    (hlower : ∀ ω, Δ * S ω ≤ tau ω)
    (hazuma : P {ω | S ω ≤ t / Δ} ≤ ENNReal.ofReal bound) :
    P {ω | tau ω ≤ t} ≤ ENNReal.ofReal bound :=
  le_trans (measure_mono (exit_subset_of_few_long_increments tau S Δ t hΔ hlower)) hazuma

/--
**Theorem `sec31_discrete_eld_tightness`, assembled.**

With the paper's choice `δ = (t/r)^{1/(d_w-1)}` the number of radial increments
is `N = r/δ = (r^{d_w}/t)^{1/(d_w-1)}` (`radial_step_count`), so the
Azuma–Hoeffding bound `C exp(-c N)` reads exactly as in the statement of the
theorem:
`P(τ ≤ t) ≤ C exp[-c (r^{d_w}/t)^{1/(d_w-1)}]`.
-/
theorem discrete_eld_tail_bound (P : Measure Ω) (tau S : Ω → ℝ)
    (r t dw Δ Cc c : ℝ) (hr : 0 < r) (ht : 0 < t) (hdw : 1 < dw) (hΔ : 0 < Δ)
    (hlower : ∀ ω, Δ * S ω ≤ tau ω)
    (hazuma : P {ω | S ω ≤ t / Δ}
      ≤ ENNReal.ofReal (Cc * exp (-c * (r / ((t / r) ^ (1 / (dw - 1)) : ℝ))))) :
    P {ω | tau ω ≤ t}
      ≤ ENNReal.ofReal (Cc * exp (-c * ((r ^ dw / t) ^ (1 / (dw - 1)) : ℝ))) := by
  rw [← radial_step_count r t dw hr ht hdw]
  exact exit_prob_le_of_azuma P tau S Δ t _ hΔ hlower hazuma

end IGS.Sec31
