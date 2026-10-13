import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Diagonal recovery from a metric core

This file proves the diagonal step that extends recovery sequences from a
sequential core to its closure in the joint state/energy topology.  The
selection uses the original discretisation index `n`, not a subsequence of
discretisations.  Its hypotheses concern individual core elements only.

The result is for a fixed pseudometric state space.  Applying it to the
paper's varying Hilbert spaces still requires a compatible common-space
realisation, and does not by itself construct that realisation or prove the
liminf half of Mosco convergence.
-/

namespace IGS.Sec31

open Filter Topology

/-- A genuine diagonal selection for a converging sequence of row limits.
The second index remains `n`, and the chosen row tends to infinity. -/
theorem exists_diagonal_tendsto {X : Type*} [PseudoMetricSpace X]
    (core : ℕ → X) (approximation : ℕ → ℕ → X) (target : X)
    (hcore : Tendsto core atTop (𝓝 target))
    (happroximation : ∀ k, Tendsto (approximation k) atTop (𝓝 (core k))) :
    ∃ stage : ℕ → ℕ, Tendsto stage atTop atTop ∧
      Tendsto (fun n => approximation (stage n) n) atTop (𝓝 target) := by
  classical
  have hthreshold : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      dist (approximation k n) (core k) < 1 / ((k : ℝ) + 1) := by
    intro k
    exact Metric.tendsto_atTop.1 (happroximation k) _ (by positivity)
  choose threshold hthreshold using hthreshold
  let stage : ℕ → ℕ := fun n => Nat.findGreatest (fun k => threshold k ≤ n) n
  have hstage : Tendsto stage atTop atTop := by
    apply tendsto_atTop.2
    intro k
    refine eventually_atTop.2 ⟨max k (threshold k), ?_⟩
    intro n hn
    exact Nat.le_findGreatest (le_trans (le_max_left _ _) hn)
      (le_trans (le_max_right _ _) hn)
  refine ⟨stage, hstage, Metric.tendsto_nhds.2 ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  have hcoreStage := Metric.tendsto_nhds.1 (hcore.comp hstage) (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop (threshold 0),
    hstage.eventually (eventually_ge_atTop k), hcoreStage] with n hn hkn hcore_n
  have hselected : threshold (stage n) ≤ n :=
    Nat.findGreatest_spec (P := fun k => threshold k ≤ n) (Nat.zero_le n) hn
  have hdenominator : (k : ℝ) + 1 ≤ (stage n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hkn 1
  calc
    dist (approximation (stage n) n) target ≤
        dist (approximation (stage n) n) (core (stage n)) +
          dist (core (stage n)) target := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      ((hthreshold (stage n) n hselected).trans_le
        (one_div_le_one_div_of_le (by positivity) hdenominator) |>.trans hk) hcore_n
    _ = ε := add_halves ε

/-- Extend state and energy recovery from core approximants to their joint
limit.  No full-domain recovery statement is assumed. -/
theorem exists_recovery_of_core {H : Type*} [PseudoMetricSpace H]
    (En : ℕ → H → ℝ) (E : H → ℝ) (target : H)
    (core : ℕ → H) (approximation : ℕ → ℕ → H)
    (hcore : Tendsto core atTop (𝓝 target))
    (hcoreEnergy : Tendsto (fun k => E (core k)) atTop (𝓝 (E target)))
    (happroximation : ∀ k, Tendsto (approximation k) atTop (𝓝 (core k)))
    (happroximationEnergy : ∀ k,
      Tendsto (fun n => En n (approximation k n)) atTop (𝓝 (E (core k)))) :
    ∃ recovery : ℕ → H, Tendsto recovery atTop (𝓝 target) ∧
      Tendsto (fun n => En n (recovery n)) atTop (𝓝 (E target)) := by
  obtain ⟨stage, _, hdiagonal⟩ := exists_diagonal_tendsto
    (fun k => (core k, E (core k)))
    (fun k n => (approximation k n, En n (approximation k n)))
    (target, E target) (hcore.prodMk_nhds hcoreEnergy)
    (fun k => (happroximation k).prodMk_nhds (happroximationEnergy k))
  exact ⟨fun n => approximation (stage n) n,
    (continuous_fst.tendsto _).comp hdiagonal,
    (continuous_snd.tendsto _).comp hdiagonal⟩

/-- The same diagonal construction preserves genuinely varying fibres.
Strong convergence is measured by specified maps into a common pseudometric
space.  This theorem proves the selection step; identifying this convergence
with a particular Kuwae--Shioya asymptotic relation is a separate obligation. -/
theorem exists_recovery_of_core_in_varying_spaces
    {H : Type*} {Discrete : ℕ → Type*} {Ambient : Type*} [PseudoMetricSpace Ambient]
    (embed : H → Ambient) (embedDiscrete : ∀ n, Discrete n → Ambient)
    (En : ∀ n, Discrete n → ℝ) (E : H → ℝ) (target : H)
    (core : ℕ → H) (approximation : ℕ → ∀ n, Discrete n)
    (hcore : Tendsto (fun k => embed (core k)) atTop (𝓝 (embed target)))
    (hcoreEnergy : Tendsto (fun k => E (core k)) atTop (𝓝 (E target)))
    (happroximation : ∀ k,
      Tendsto (fun n => embedDiscrete n (approximation k n)) atTop (𝓝 (embed (core k))))
    (happroximationEnergy : ∀ k,
      Tendsto (fun n => En n (approximation k n)) atTop (𝓝 (E (core k)))) :
    ∃ recovery : ∀ n, Discrete n,
      Tendsto (fun n => embedDiscrete n (recovery n)) atTop (𝓝 (embed target)) ∧
        Tendsto (fun n => En n (recovery n)) atTop (𝓝 (E target)) := by
  obtain ⟨stage, _, hdiagonal⟩ := exists_diagonal_tendsto
    (fun k => (embed (core k), E (core k)))
    (fun k n => (embedDiscrete n (approximation k n), En n (approximation k n)))
    (embed target, E target) (hcore.prodMk_nhds hcoreEnergy)
    (fun k => (happroximation k).prodMk_nhds (happroximationEnergy k))
  exact ⟨fun n => approximation (stage n) n,
    (continuous_fst.tendsto _).comp hdiagonal,
    (continuous_snd.tendsto _).comp hdiagonal⟩

end IGS.Sec31
