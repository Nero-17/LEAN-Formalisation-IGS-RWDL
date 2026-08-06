import RequestProject.Cluster.Network
import RequestProject.Reduced.Process

/-!
# Bond percolation on the diamond hierarchical lattice, and its two-terminal resistance

The level-`n` diamond hierarchical lattice (DHL) is the two-terminal network obtained from a single
edge by `n` steps of the substitution "replace every edge by a diamond of four edges" (two parallel
branches, each a series of two edges).  Equivalently, and this is the description used here, the
level-`(n+1)` DHL is the *parallel* composition of two *series* compositions of two copies of the
level-`n` DHL.

A **percolation configuration** at level `n` is therefore an element of

  `Conf n`,   `Conf 0 = Bool`,   `Conf (n+1) = Conf n × Conf n × Conf n × Conf n`,

the boolean at a leaf recording whether the corresponding finest edge is open.  `net n c` is the
genuine finite electrical network obtained by keeping the open edges only (a closed edge becomes a
pair of unlinked terminals), and

  `res n c = (net n c).effRes ∈ ℝ≥0∞`

is the effective resistance of the open cluster between the two boundary vertices, with the value
`⊤` exactly when the two terminals are not connected.  Note that this is the resistance of the
whole open subgraph: dangling pieces are not deleted by hand, they are automatically invisible to
the effective resistance (see `TTN.effRes_par`).

Finally `confMeasure p n` is the i.i.d. Bernoulli(`p`) bond percolation measure at level `n`, and
`resLaw p n` is the law of `res n` under it.
-/

namespace Cluster

open MeasureTheory
open scoped ENNReal

/-- Percolation configurations of the level-`n` diamond hierarchical lattice. -/
def Conf : ℕ → Type
  | 0 => Bool
  | (n + 1) => Conf n × Conf n × Conf n × Conf n

instance instConfMeasurableSpace : (n : ℕ) → MeasurableSpace (Conf n)
  | 0 => inferInstanceAs (MeasurableSpace Bool)
  | (n + 1) =>
      let _ := instConfMeasurableSpace n
      inferInstanceAs (MeasurableSpace (Conf n × Conf n × Conf n × Conf n))

/-- The level-`n` DHL network of open edges determined by the configuration `c`. -/
def net : (n : ℕ) → Conf n → TTN
  | 0 => (fun c : Bool => if c then TTN.edgeTTN else TTN.gapTTN)
  | (n + 1) => fun c =>
      TTN.parTTN (TTN.seriesTTN (net n c.1) (net n c.2.1))
        (TTN.seriesTTN (net n c.2.2.1) (net n c.2.2.2))

/-- The two-terminal effective resistance of the open cluster (`⊤` if disconnected). -/
noncomputable def res (n : ℕ) (c : Conf n) : ℝ≥0∞ := (net n c).effRes

@[simp] lemma res_zero_true : res 0 true = 1 := by
  simp [res, net, TTN.effRes_edge]

@[simp] lemma res_zero_false : res 0 false = ⊤ := by
  simp [res, net, TTN.effRes_gap]

/-- The one-step recursion for the two-terminal resistance: two series branches in parallel. -/
theorem res_succ (n : ℕ) (c : Conf (n + 1)) :
    res (n + 1) c =
      ((res n c.1 + res n c.2.1)⁻¹ + (res n c.2.2.1 + res n c.2.2.2)⁻¹)⁻¹ := by
  simp [res, net, TTN.effRes_par, TTN.effRes_series]

lemma measurable_res : ∀ n, Measurable (res n)
  | 0 => show Measurable (fun b : Bool => res 0 b) from Measurable.of_discrete
  | (n + 1) => by
      have h := measurable_res n
      show Measurable (fun c : Conf n × Conf n × Conf n × Conf n => res (n + 1) c)
      have hfun : (fun c : Conf n × Conf n × Conf n × Conf n => res (n + 1) c)
          = fun c : Conf n × Conf n × Conf n × Conf n =>
            ((res n c.1 + res n c.2.1)⁻¹ + (res n c.2.2.1 + res n c.2.2.2)⁻¹)⁻¹ := by
        funext c
        exact res_succ n c
      rw [hfun]
      fun_prop

/-! ### The percolation measure -/

/-- The Bernoulli(`p`) measure on `Bool` (`true` = open). -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The i.i.d. Bernoulli(`p`) bond percolation measure on level-`n` configurations. -/
noncomputable def confMeasure (p : ℝ) : (n : ℕ) → Measure (Conf n)
  | 0 => bern p
  | (n + 1) =>
      (confMeasure p n).prod ((confMeasure p n).prod ((confMeasure p n).prod (confMeasure p n)))

lemma isProb_bern {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbabilityMeasure (bern p) := by
  constructor
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    MeasureTheory.Measure.dirac_apply', MeasurableSet.univ, Set.indicator_univ,
    smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

lemma isProb_confMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n, IsProbabilityMeasure (confMeasure p n)
  | 0 => isProb_bern hp0 hp1
  | (n + 1) => by
      have h := isProb_confMeasure hp0 hp1 n
      show IsProbabilityMeasure
        ((confMeasure p n).prod ((confMeasure p n).prod ((confMeasure p n).prod (confMeasure p n))))
      infer_instance

/-- The law of the two-terminal resistance of the percolation cluster at level `n`. -/
noncomputable def resLaw (p : ℝ) (n : ℕ) : Measure ℝ≥0∞ := (confMeasure p n).map (res n)

/-! ### Series and parallel combination of laws -/

/-- Series combination of two resistance values. -/
noncomputable def sumE (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ := x.1 + x.2

/-- Parallel combination of two resistance values (`⊤` means "disconnected"). -/
noncomputable def parE (x : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ := (x.1⁻¹ + x.2⁻¹)⁻¹

/-- The fourfold diamond combination of resistance values. -/
noncomputable def diamondE (x : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  ((x.1 + x.2.1)⁻¹ + (x.2.2.1 + x.2.2.2)⁻¹)⁻¹

@[fun_prop, measurability]
lemma measurable_sumE : Measurable sumE := by unfold sumE; fun_prop

@[fun_prop, measurability]
lemma measurable_parE : Measurable parE := by unfold parE; fun_prop
lemma measurable_diamondE : Measurable diamondE := by unfold diamondE; fun_prop

/-- The law of the sum of two independent resistances. -/
noncomputable def sumLaw (rho sig : Measure ℝ≥0∞) : Measure ℝ≥0∞ :=
  (rho.prod sig).map sumE

/-- The law of the parallel combination of two independent resistances. -/
noncomputable def parLaw (rho sig : Measure ℝ≥0∞) : Measure ℝ≥0∞ :=
  (rho.prod sig).map parE

lemma resLaw_zero (p : ℝ) :
    resLaw p 0 =
      ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac ⊤ := by
  have hmeas : Measurable (res 0) := measurable_res 0
  show ((ENNReal.ofReal p • Measure.dirac true
      + ENNReal.ofReal (1 - p) • Measure.dirac false).map (res 0)) = _
  rw [Measure.map_add _ _ hmeas, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac hmeas, Measure.map_dirac hmeas, res_zero_true, res_zero_false]

/-- The distributional recursion of the percolation resistance: the level-`(n+1)` law is the
parallel combination of two independent series combinations of two independent copies of the
level-`n` law. -/
theorem resLaw_succ {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    resLaw p (n + 1) =
      parLaw (sumLaw (resLaw p n) (resLaw p n)) (sumLaw (resLaw p n) (resLaw p n)) := by
  haveI hmu := isProb_confMeasure hp0 hp1 n
  have hres : Measurable (res n) := measurable_res n
  haveI hrho : IsProbabilityMeasure (resLaw p n) := by
    unfold resLaw
    exact Measure.isProbabilityMeasure_map hres.aemeasurable
  have h4 : (resLaw p n).prod ((resLaw p n).prod ((resLaw p n).prod (resLaw p n)))
      = Measure.map (Prod.map (res n) (Prod.map (res n) (Prod.map (res n) (res n))))
        (confMeasure p (n + 1)) := by
    show _ = Measure.map _ ((confMeasure p n).prod
      ((confMeasure p n).prod ((confMeasure p n).prod (confMeasure p n))))
    unfold resLaw
    rw [Measure.map_prod_map _ _ hres hres, Measure.map_prod_map _ _ hres (by fun_prop),
      Measure.map_prod_map _ _ hres (by fun_prop)]
  have hLHS : resLaw p (n + 1) = Measure.map diamondE
      ((resLaw p n).prod ((resLaw p n).prod ((resLaw p n).prod (resLaw p n)))) := by
    rw [h4, Measure.map_map measurable_diamondE (by fun_prop)]
    unfold resLaw
    congr 1
    funext c
    exact res_succ n c
  have hRHS : parLaw (sumLaw (resLaw p n) (resLaw p n)) (sumLaw (resLaw p n) (resLaw p n))
      = Measure.map (parE ∘ Prod.map sumE sumE)
        (((resLaw p n).prod (resLaw p n)).prod ((resLaw p n).prod (resLaw p n))) := by
    unfold parLaw sumLaw
    rw [Measure.map_prod_map _ _ measurable_sumE measurable_sumE,
      Measure.map_map measurable_parE (by fun_prop)]
  have hassoc : Measure.map (⇑MeasurableEquiv.prodAssoc)
      (((resLaw p n).prod (resLaw p n)).prod ((resLaw p n).prod (resLaw p n)))
      = (resLaw p n).prod ((resLaw p n).prod ((resLaw p n).prod (resLaw p n))) :=
    (measurePreserving_prodAssoc (resLaw p n) (resLaw p n)
      ((resLaw p n).prod (resLaw p n))).map_eq
  rw [hLHS, hRHS, ← hassoc, Measure.map_map measurable_diamondE
    MeasurableEquiv.prodAssoc.measurable]
  congr 1

end Cluster
