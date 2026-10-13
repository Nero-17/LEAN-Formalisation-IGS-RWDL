import RequestProject.Cluster.Law

/-!
# Proposition 4.2 of *Iterated Graph Systems (I)*

At the critical parameter `p = p_c`, for every `n` the two-terminal effective resistance of the
level-`n` critical percolation cluster on the diamond hierarchical lattice, conditioned on the two
boundary vertices being connected, has exactly the law of the reduced resistance `R_n` of
Subsection 4.1.

The critical identity `p_c ^ 2 = 1 - p_c` makes the two conditional parameters of the reduced
process equal to `p_diamond = p_c ^ 3` and `p_series = 2 p_c ^ 2`, and makes the probability that
the two boundary vertices are connected equal to `p_c` at *every* level.
-/

namespace Cluster

open MeasureTheory Reduced
open scoped ENNReal

/-! ### The critical parameters -/

lemma pc_nonneg : (0 : ℝ) ≤ pc := pc_pos.le

lemma pc_le_one : pc ≤ 1 := pc_lt_one.le

lemma one_sub_pc_nonneg : (0 : ℝ) ≤ 1 - pc := by linarith [pc_lt_one]

lemma two_sub_pc_sq : 2 - pc ^ 2 = 1 + pc := by
  have h := pc_sq
  linarith

/-- At criticality the diamond parameter is `p_c ^ 3`. -/
lemma pdiamond_pc_eq : pdiamond pc = pc ^ 3 := by
  have h := pc_sq
  have hden : (0 : ℝ) < 1 + pc := by linarith [pc_pos]
  rw [pdiamond, two_sub_pc_sq, div_eq_iff (ne_of_gt hden)]
  linear_combination (-pc ^ 2) * h

/-- At criticality the series parameter is `2 p_c ^ 2`. -/
lemma pseries_pc_eq : pseries pc = 2 * pc ^ 2 := by
  have h := pc_sq
  have hden : (0 : ℝ) < 1 + pc := by linarith [pc_pos]
  rw [pseries, two_sub_pc_sq, div_eq_iff (ne_of_gt hden)]
  linear_combination (-2 * pc - 2) * h

lemma pdiamond_pc_nonneg : 0 ≤ pdiamond pc := pdiamond_nonneg pc_pos pc_lt_one

lemma pseries_pc_nonneg : 0 ≤ pseries pc := pseries_nonneg pc_pos pc_lt_one

lemma pseries_add_pdiamond_pc : pseries pc + pdiamond pc = 1 :=
  pseries_add_pdiamond pc_pos pc_lt_one

instance isProb_lawMeasure_pc (n : ℕ) :
    IsProbabilityMeasure (lawMeasure (pdiamond pc) (pseries pc) n) :=
  isProb_lawMeasure pdiamond_pc_nonneg pseries_pc_nonneg pseries_add_pdiamond_pc n

lemma lawMeasure_pc_nonneg (n : ℕ) :
    ∀ᵐ x ∂(lawMeasure (pdiamond pc) (pseries pc) n), 0 < x := by
  filter_upwards [lawMeasure_support pdiamond_pc_nonneg pseries_pc_nonneg
    pseries_add_pdiamond_pc n] with x hx
  exact lt_of_lt_of_le zero_lt_one hx.1

/-! ### The main induction -/

/-- The law of the level-`n` critical cluster resistance is a resistance law with disconnection
mass `1 - p_c` and finite part `p_c` times the law of the reduced resistance `R_n`. -/
theorem resLaw_isResLaw (n : ℕ) :
    IsResLaw (resLaw pc n) (ENNReal.ofReal (1 - pc))
      (ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [resLaw_zero, lawMeasure_zero, Measure.map_smul,
        Measure.map_dirac ENNReal.measurable_ofReal, ENNReal.ofReal_one]
      abel
    · have hp := lawMeasure_pc_nonneg 0
      rw [ae_iff] at hp ⊢
      simp only [Measure.smul_apply, smul_eq_mul, hp, mul_zero]
    · exact isFiniteMeasure_smul ENNReal.ofReal_ne_top _
    · exact ENNReal.ofReal_ne_top
  | succ n ih =>
    set L := lawMeasure (pdiamond pc) (pseries pc) n with hLdef
    set q := ENNReal.ofReal pc with hq
    have hunivL : L Set.univ = 1 := measure_univ
    have huniv : (q • L) Set.univ = q := by
      rw [Measure.smul_apply, hunivL, smul_eq_mul, mul_one]
    have hstep := (ih.sum ih).par (ih.sum ih)
    rw [← resLaw_succ pc_nonneg pc_le_one n] at hstep
    -- the disconnection mass of a single series branch
    have hMs : ENNReal.ofReal (1 - pc) * ENNReal.ofReal (1 - pc)
        + ENNReal.ofReal (1 - pc) * (q • L) Set.univ
        + ENNReal.ofReal (1 - pc) * (q • L) Set.univ = q := by
      rw [huniv, hq, ← ENNReal.ofReal_mul one_sub_pc_nonneg,
        ← ENNReal.ofReal_mul one_sub_pc_nonneg, ← ENNReal.ofReal_add (by nlinarith [pc_lt_one])
          (by nlinarith [pc_pos, pc_lt_one]),
        ← ENNReal.ofReal_add (by nlinarith [pc_pos, pc_lt_one])
          (by nlinarith [pc_pos, pc_lt_one])]
      congr 1
      nlinarith [pc_sq]
    rw [hMs] at hstep
    -- the finite part of a single series branch
    have hS : ((q • L).prod (q • L)).map seriesMap
        = (q * q) • ((L.prod L).map seriesMap) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    rw [hS] at hstep
    have hmass : q * q = ENNReal.ofReal (1 - pc) := by
      rw [hq, ← ENNReal.ofReal_mul pc_nonneg]
      congr 1
      nlinarith [pc_sq]
    have c1 : q * (q * q) + q * (q * q) = q * ENNReal.ofReal (pseries pc) := by
      rw [hq, ← ENNReal.ofReal_mul pc_nonneg, ← ENNReal.ofReal_mul pc_nonneg,
        ← ENNReal.ofReal_add (by nlinarith [pc_pos]) (by nlinarith [pc_pos]),
        ← ENNReal.ofReal_mul pc_nonneg]
      congr 1
      rw [pseries_pc_eq]
      ring
    have c2 : (q * q) * (q * q) = q * ENNReal.ofReal (pdiamond pc) := by
      rw [hq, ← ENNReal.ofReal_mul pc_nonneg,
        ← ENNReal.ofReal_mul (mul_nonneg pc_nonneg pc_nonneg),
        ← ENNReal.ofReal_mul pc_nonneg]
      congr 1
      rw [pdiamond_pc_eq]
      ring
    have hlam : q • ((q * q) • ((L.prod L).map seriesMap))
        + q • ((q * q) • ((L.prod L).map seriesMap))
        + ((((q * q) • ((L.prod L).map seriesMap))).prod
            (((q * q) • ((L.prod L).map seriesMap)))).map parMap
        = q • lawMeasure (pdiamond pc) (pseries pc) (n + 1) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
        Measure.map_smul, smul_smul,
        par_series_prod L, lawMeasure_succ, smul_add, smul_smul, smul_smul, ← add_smul,
        c1, c2, hLdef]
    rw [hmass] at hlam
    rw [hmass, hlam] at hstep
    exact hstep

/-! ### Proposition 4.2 -/

lemma measurableSet_ne_top : MeasurableSet {x : ℝ≥0∞ | x ≠ ⊤} :=
  (measurableSet_singleton (⊤ : ℝ≥0∞)).compl

/-- At the critical parameter, the two boundary vertices of the level-`n` DHL are connected in the
percolation cluster with probability `p_c`, for every `n`. -/
theorem prob_connected (n : ℕ) :
    confMeasure pc n {c | res n c ≠ ⊤} = ENNReal.ofReal pc := by
  have h := resLaw_isResLaw n
  have hmeas : Measurable (res n) := measurable_res n
  have hpush : confMeasure pc n {c | res n c ≠ ⊤} = resLaw pc n {x : ℝ≥0∞ | x ≠ ⊤} := by
    rw [resLaw, Measure.map_apply hmeas measurableSet_ne_top]
    rfl
  rw [hpush, h.eq]
  have h1 : (ENNReal.ofReal (1 - pc) • Measure.dirac (⊤ : ℝ≥0∞)) {x : ℝ≥0∞ | x ≠ ⊤} = 0 := by
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_ne_top]
    simp
  have h2 : ((ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n).map
      ENNReal.ofReal) {x : ℝ≥0∞ | x ≠ ⊤} = ENNReal.ofReal pc := by
    rw [Measure.map_apply ENNReal.measurable_ofReal measurableSet_ne_top]
    have : ENNReal.ofReal ⁻¹' {x : ℝ≥0∞ | x ≠ ⊤} = Set.univ := by
      ext x
      simp [ENNReal.ofReal_ne_top]
    rw [this, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [Measure.add_apply, h1, h2, zero_add]

/-- **Proposition 4.2.** At the critical parameter, for every `n` the two-terminal effective
resistance of the level-`n` percolation cluster on the diamond hierarchical lattice, conditioned
on the two boundary vertices being connected, has exactly the law of the reduced resistance `R_n`
of Subsection 4.1. -/
theorem cluster_resistance_law (n : ℕ) :
    (ProbabilityTheory.cond (confMeasure pc n) {c | res n c ≠ ⊤}).map
        (fun c => (res n c).toReal)
      = lawMeasure (pdiamond pc) (pseries pc) n := by
  have h := resLaw_isResLaw n
  have hmeas : Measurable (res n) := measurable_res n
  -- the restricted law is the finite part of the resistance law
  have hres : (resLaw pc n).restrict {x : ℝ≥0∞ | x ≠ ⊤}
      = (ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n).map ENNReal.ofReal := by
    rw [h.eq, Measure.restrict_add]
    have h1 : (ENNReal.ofReal (1 - pc) • Measure.dirac (⊤ : ℝ≥0∞)).restrict
        {x : ℝ≥0∞ | x ≠ ⊤} = 0 := by
      have hd : (Measure.dirac (⊤ : ℝ≥0∞)).restrict {x : ℝ≥0∞ | x ≠ ⊤} = 0 := by
        rw [Measure.restrict_eq_zero, Measure.dirac_apply' _ measurableSet_ne_top]
        simp
      rw [Measure.restrict_smul, hd, smul_zero]
    have h2 : ((ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n).map
        ENNReal.ofReal).restrict {x : ℝ≥0∞ | x ≠ ⊤}
        = (ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n).map ENNReal.ofReal := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff, Measure.map_apply ENNReal.measurable_ofReal (by measurability)]
      have hemp : (ENNReal.ofReal ⁻¹' {x : ℝ≥0∞ | ¬ x ∈ {x : ℝ≥0∞ | x ≠ ⊤}}) = ∅ := by
        ext x
        simp [ENNReal.ofReal_ne_top]
      rw [hemp, measure_empty]
    rw [h1, h2, zero_add]
  -- the image of the restricted measure under `toReal`
  have hmap : ((confMeasure pc n).restrict {c | res n c ≠ ⊤}).map (fun c => (res n c).toReal)
      = ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n := by
    have hcomp : (fun c => (res n c).toReal) = ENNReal.toReal ∘ res n := rfl
    have hrm : ((confMeasure pc n).restrict {c | res n c ≠ ⊤}).map (res n)
        = (resLaw pc n).restrict {x : ℝ≥0∞ | x ≠ ⊤} := by
      rw [resLaw, Measure.restrict_map hmeas measurableSet_ne_top]
      rfl
    rw [hcomp, ← Measure.map_map ENNReal.measurable_toReal hmeas, hrm, hres,
      Measure.map_map ENNReal.measurable_toReal ENNReal.measurable_ofReal]
    have hid : (ENNReal.toReal ∘ ENNReal.ofReal)
        =ᵐ[ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n] id := by
      have hp : ∀ᵐ x ∂(ENNReal.ofReal pc • lawMeasure (pdiamond pc) (pseries pc) n), 0 < x := by
        have hp0 := lawMeasure_pc_nonneg n
        rw [ae_iff] at hp0 ⊢
        simp only [Measure.smul_apply, smul_eq_mul, hp0, mul_zero]
      filter_upwards [hp] with x hx
      simp [ENNReal.toReal_ofReal hx.le]
    rw [Measure.map_congr hid, Measure.map_id]
  rw [ProbabilityTheory.cond, Measure.map_smul, hmap, prob_connected n, smul_smul,
    ENNReal.inv_mul_cancel (by simp [pc_pos]) ENNReal.ofReal_ne_top, one_smul]

end Cluster
