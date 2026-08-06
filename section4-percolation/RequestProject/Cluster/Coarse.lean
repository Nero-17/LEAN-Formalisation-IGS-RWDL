import RequestProject.Cluster.Prop42

/-!
# Coarse-graining the diamond hierarchical lattice

The level-`(n+1)` DHL is obtained from the level-`n` DHL by replacing every edge with a diamond of
four edges.  Consequently a percolation configuration `c` at level `n+1` induces one at level `n`:
an edge of the level-`n` lattice is declared *open* exactly when the diamond of level-`(n+1)` edges
that replaced it connects its two endpoints.  This is the map `coarse n : Conf (n+1) → Conf n`.

Coarse-graining is the coupling that turns the family of percolation clusters into a *process*:
the level-`n` cluster of `coarse n c` is the cluster obtained from the level-`(n+1)` cluster of `c`
by one step of renormalisation, i.e. it is the level-`n` stage of the substitution construction of
the paper.  Two facts make it work:

* `conn_coarse`: connectivity of the two terminals is preserved by coarse-graining;
* `confMeasure_map_coarse`: **at the critical parameter** `p_c` (and only there) the coarse-grained
  configuration is again an i.i.d. Bernoulli(`p_c`) configuration, because
  `2 p_c ^ 2 - p_c ^ 4 = p_c`.

This file also records the combinatorial connectivity predicate `conn` and its identification with
finiteness of the effective resistance.
-/

namespace Cluster

open MeasureTheory Reduced
open scoped ENNReal

/-! ### Connectivity of a configuration -/

/-- `conn n c = true` exactly when the two terminals of the level-`n` DHL are joined by open
edges in the configuration `c`. -/
def conn : (n : ℕ) → Conf n → Bool
  | 0 => fun c => c
  | (n + 1) => fun c =>
      (conn n c.1 && conn n c.2.1) || (conn n c.2.2.1 && conn n c.2.2.2)

@[simp] lemma conn_zero (b : Conf 0) : conn 0 b = b := rfl

@[simp] lemma conn_succ (n : ℕ) (c : Conf (n + 1)) :
    conn (n + 1) c = ((conn n c.1 && conn n c.2.1) || (conn n c.2.2.1 && conn n c.2.2.2)) := rfl

instance instConfFintype : (n : ℕ) → Fintype (Conf n)
  | 0 => inferInstanceAs (Fintype Bool)
  | (n + 1) =>
      let _ := instConfFintype n
      inferInstanceAs (Fintype (Conf n × Conf n × Conf n × Conf n))

instance instConfDiscrete : (n : ℕ) → DiscreteMeasurableSpace (Conf n)
  | 0 => inferInstanceAs (DiscreteMeasurableSpace Bool)
  | (n + 1) =>
      let _ := instConfDiscrete n
      let _ := instConfFintype n
      inferInstanceAs (DiscreteMeasurableSpace (Conf n × Conf n × Conf n × Conf n))

/-- Every two-terminal resistance is at least `1` (`⊤` when disconnected). -/
lemma one_le_res : ∀ (n : ℕ) (c : Conf n), 1 ≤ res n c
  | 0 => by
      intro c
      match c with
      | true => simp
      | false => simp
  | (n + 1) => by
      intro c
      have h1 := one_le_res n c.1
      have h2 := one_le_res n c.2.1
      have h3 := one_le_res n c.2.2.1
      have h4 := one_le_res n c.2.2.2
      have hA : (2 : ℝ≥0∞) ≤ res n c.1 + res n c.2.1 := by
        calc (2 : ℝ≥0∞) = 1 + 1 := by norm_num
        _ ≤ res n c.1 + res n c.2.1 := add_le_add h1 h2
      have hB : (2 : ℝ≥0∞) ≤ res n c.2.2.1 + res n c.2.2.2 := by
        calc (2 : ℝ≥0∞) = 1 + 1 := by norm_num
        _ ≤ res n c.2.2.1 + res n c.2.2.2 := add_le_add h3 h4
      rw [res_succ]
      refine ENNReal.one_le_inv.mpr ?_
      have hA' : (res n c.1 + res n c.2.1)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr hA
      have hB' : (res n c.2.2.1 + res n c.2.2.2)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr hB
      calc (res n c.1 + res n c.2.1)⁻¹ + (res n c.2.2.1 + res n c.2.2.2)⁻¹
          ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := add_le_add hA' hB'
        _ = 1 := by
            rw [ENNReal.inv_two_add_inv_two]

/-- The effective resistance is finite exactly when the two terminals are connected. -/
lemma res_ne_top_iff_conn : ∀ (n : ℕ) (c : Conf n), res n c ≠ ⊤ ↔ conn n c = true
  | 0 => by
      intro c
      match c with
      | true => simp
      | false => simp
  | (n + 1) => by
      intro c
      have h1 := res_ne_top_iff_conn n c.1
      have h2 := res_ne_top_iff_conn n c.2.1
      have h3 := res_ne_top_iff_conn n c.2.2.1
      have h4 := res_ne_top_iff_conn n c.2.2.2
      rw [res_succ]
      have hiff : ((res n c.1 + res n c.2.1)⁻¹ + (res n c.2.2.1 + res n c.2.2.2)⁻¹)⁻¹ ≠ ⊤
          ↔ ¬ ((res n c.1 + res n c.2.1 = ⊤) ∧ (res n c.2.2.1 + res n c.2.2.2 = ⊤)) := by
        rw [Ne, ENNReal.inv_eq_top, add_eq_zero, ENNReal.inv_eq_zero, ENNReal.inv_eq_zero]
      rw [hiff, ENNReal.add_eq_top, ENNReal.add_eq_top, conn_succ]
      by_cases a1 : conn n c.1 <;> by_cases a2 : conn n c.2.1 <;>
        by_cases a3 : conn n c.2.2.1 <;> by_cases a4 : conn n c.2.2.2 <;>
        simp_all

/-- The set of configurations connecting the two terminals. -/
lemma setOf_res_ne_top (n : ℕ) : {c : Conf n | res n c ≠ ⊤} = {c : Conf n | conn n c = true} := by
  ext c
  exact res_ne_top_iff_conn n c

/-! ### Coarse-graining -/

/-- Coarse-graining: an edge of the level-`n` lattice is open in `coarse n c` exactly when the
diamond of level-`(n+1)` edges replacing it connects its endpoints in `c`. -/
def coarse : (n : ℕ) → Conf (n + 1) → Conf n
  | 0 => fun c => conn 1 c
  | (n + 1) => fun c =>
      (coarse n c.1, coarse n c.2.1, coarse n c.2.2.1, coarse n c.2.2.2)

@[simp] lemma coarse_zero (c : Conf 1) : coarse 0 c = conn 1 c := rfl

@[simp] lemma coarse_succ (n : ℕ) (c : Conf (n + 2)) :
    coarse (n + 1) c = (coarse n c.1, coarse n c.2.1, coarse n c.2.2.1, coarse n c.2.2.2) := rfl

/-- Coarse-graining preserves connectivity of the two terminals. -/
lemma conn_coarse : ∀ (n : ℕ) (c : Conf (n + 1)), conn n (coarse n c) = conn (n + 1) c
  | 0 => fun _ => rfl
  | (n + 1) => fun c => by
      rw [coarse_succ, conn_succ, conn_succ, conn_coarse n c.1, conn_coarse n c.2.1,
        conn_coarse n c.2.2.1, conn_coarse n c.2.2.2]

lemma measurable_coarse (n : ℕ) : Measurable (coarse n) := Measurable.of_discrete

/-! ### Coarse-graining preserves the critical percolation measure -/

/-- Two probability measures on the level-`0` configuration space agreeing on `{true}` are
equal. -/
lemma conf0_measure_ext {mu nu : Measure (Conf 0)} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (ht : mu {true} = nu {true}) : mu = nu := by
  have hc : ({false} : Set (Conf 0)) = ({true} : Set (Conf 0))ᶜ := by
    ext b
    match b with
    | true => simp
    | false => simp
  have hf : mu {false} = nu {false} := by
    rw [hc, prob_compl_eq_one_sub MeasurableSet.of_discrete,
      prob_compl_eq_one_sub MeasurableSet.of_discrete, ht]
  rw [← Measure.sum_smul_dirac mu, ← Measure.sum_smul_dirac nu]
  congr 1
  funext b
  match b with
  | true => rw [ht]
  | false => rw [hf]

lemma bern_true {p : ℝ} : bern p {true} = ENNReal.ofReal p := by
  simp [bern]

/-- **At the critical parameter** the coarse-grained configuration is again an i.i.d.
Bernoulli(`p_c`) percolation configuration.  This is the fixed-point identity
`2 p_c^2 - p_c^4 = p_c`, and it is what makes the levels of the critical cluster a consistent
process. -/
theorem confMeasure_map_coarse (n : ℕ) :
    (confMeasure pc (n + 1)).map (coarse n) = confMeasure pc n := by
  induction n with
  | zero =>
      haveI := isProb_confMeasure pc_nonneg pc_le_one 1
      haveI := isProb_confMeasure pc_nonneg pc_le_one 0
      haveI : IsProbabilityMeasure ((confMeasure pc 1).map (coarse 0)) :=
        Measure.isProbabilityMeasure_map (measurable_coarse 0).aemeasurable
      refine conf0_measure_ext ?_
      have hpre : (coarse 0) ⁻¹' ({true} : Set (Conf 0)) = {c : Conf 1 | res 1 c ≠ ⊤} := by
        rw [setOf_res_ne_top]
        rfl
      rw [Measure.map_apply (measurable_coarse 0) MeasurableSet.of_discrete, hpre,
        prob_connected 1]
      exact (bern_true (p := pc)).symm
  | succ n ih =>
      haveI := isProb_confMeasure pc_nonneg pc_le_one n
      haveI := isProb_confMeasure pc_nonneg pc_le_one (n + 1)
      have hfun : (coarse (n + 1))
          = Prod.map (coarse n) (Prod.map (coarse n) (Prod.map (coarse n) (coarse n))) := by
        funext c
        rfl
      show (Measure.prod (confMeasure pc (n + 1))
        ((confMeasure pc (n + 1)).prod ((confMeasure pc (n + 1)).prod
          (confMeasure pc (n + 1))))).map (coarse (n + 1)) = _
      rw [hfun, ← Measure.map_prod_map _ _ (measurable_coarse n)
        (by exact (measurable_coarse n).prodMap ((measurable_coarse n).prodMap
          (measurable_coarse n))),
        ← Measure.map_prod_map _ _ (measurable_coarse n)
          (by exact (measurable_coarse n).prodMap (measurable_coarse n)),
        ← Measure.map_prod_map _ _ (measurable_coarse n) (measurable_coarse n), ih]
      rfl

end Cluster
