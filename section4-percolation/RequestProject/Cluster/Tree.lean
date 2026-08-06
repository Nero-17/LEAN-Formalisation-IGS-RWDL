import RequestProject.Reduced.Process

/-!
# The reduced random EIGS as a *process*: the tree of replacement choices

Subsection 4.1 builds the reduced two-terminal networks `G_0, G_1, G_2, …` by *substitution*:
`G_{n+1}` is obtained from `G_n` by replacing every edge, independently, by a two-edge series
(probability `p_series`) or by a diamond (probability `p_diamond`).  All the levels therefore live
on one probability space — the space of *trees of replacement choices* — and the whole sequence
`(R_n)_n` is a single random object.

This file constructs the depth-`n` truncation of that space,
```
RConf 0 = Unit,
RConf (n+1) = (RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n)),
```
the left summand recording a series cell together with its two descendant subtrees and the right
summand a diamond cell together with its four descendant subtrees.  On it we define

* `Rres n : RConf n → ℝ`, the two-terminal resistance of the level-`n` reduced network;
* `rtrunc n : RConf (n+1) → RConf n`, forgetting the finest generation of choices;
* `rMeasure pd ps n`, the law of the depth-`n` tree (root choice `pd`/`ps`, i.i.d. subtrees);
* `rwin n : RConf n → (Fin (n+1) → ℝ)`, the *window* `(R_0, R_1, …, R_n)` of the process.

The link with Subsection 4.1 is `rMeasure_map_Rres`: the image of `rMeasure pd ps n` under
`Rres n` is exactly the law `lawMeasure pd ps n` of `R_n` used throughout `RequestProject/Reduced`.
-/

namespace Cluster

open MeasureTheory Reduced

/-- Depth-`n` tree of replacement choices for the reduced process: a series cell carries two
descendant subtrees, a diamond cell carries four. -/
def RConf : ℕ → Type
  | 0 => Unit
  | (n + 1) => (RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n))

instance instRConfFintype : (n : ℕ) → Fintype (RConf n)
  | 0 => inferInstanceAs (Fintype Unit)
  | (n + 1) =>
      let _ := instRConfFintype n
      inferInstanceAs (Fintype ((RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n))))

instance instRConfMeasurableSpace : (n : ℕ) → MeasurableSpace (RConf n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | (n + 1) =>
      let _ := instRConfMeasurableSpace n
      inferInstanceAs (MeasurableSpace
        ((RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n))))

instance instRConfDiscrete : (n : ℕ) → DiscreteMeasurableSpace (RConf n)
  | 0 => inferInstanceAs (DiscreteMeasurableSpace Unit)
  | (n + 1) =>
      let _ := instRConfDiscrete n
      ⟨fun s => by
        show MeasurableSet[Sum.instMeasurableSpace] s
        rw [measurableSet_sum_iff]
        exact ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩⟩

/-- A series cell with its two descendant subtrees. -/
def rinl (n : ℕ) : RConf n × RConf n → RConf (n + 1) := Sum.inl

/-- A diamond cell with its four descendant subtrees (given as two pairs). -/
def rinr (n : ℕ) : (RConf n × RConf n) × (RConf n × RConf n) → RConf (n + 1) := Sum.inr

lemma rinl_injective (n : ℕ) : Function.Injective (rinl n) := Sum.inl_injective

lemma rinr_injective (n : ℕ) : Function.Injective (rinr n) := Sum.inr_injective

/-- The two-terminal resistance of the level-`n` reduced network encoded by a tree. -/
noncomputable def Rres : (n : ℕ) → RConf n → ℝ
  | 0 => fun _ => 1
  | (n + 1) => fun t =>
      match t with
      | Sum.inl q => Rres n q.1 + Rres n q.2
      | Sum.inr q => diamondVal (Rres n q.1.1) (Rres n q.1.2) (Rres n q.2.1) (Rres n q.2.2)

@[simp] lemma Rres_zero (t : RConf 0) : Rres 0 t = 1 := rfl

@[simp] lemma Rres_rinl (n : ℕ) (q : RConf n × RConf n) :
    Rres (n + 1) (rinl n q) = Rres n q.1 + Rres n q.2 := rfl

@[simp] lemma Rres_rinr (n : ℕ) (q : (RConf n × RConf n) × (RConf n × RConf n)) :
    Rres (n + 1) (rinr n q)
      = diamondVal (Rres n q.1.1) (Rres n q.1.2) (Rres n q.2.1) (Rres n q.2.2) := rfl

/-- Forget the finest generation of replacement choices. -/
def rtrunc : (n : ℕ) → RConf (n + 1) → RConf n
  | 0 => fun _ => ()
  | (n + 1) => fun t =>
      match t with
      | Sum.inl q => rinl n (rtrunc n q.1, rtrunc n q.2)
      | Sum.inr q =>
          rinr n ((rtrunc n q.1.1, rtrunc n q.1.2), (rtrunc n q.2.1, rtrunc n q.2.2))

@[simp] lemma rtrunc_rinl (n : ℕ) (q : RConf (n + 1) × RConf (n + 1)) :
    rtrunc (n + 1) (rinl (n + 1) q) = rinl n (rtrunc n q.1, rtrunc n q.2) := rfl

@[simp] lemma rtrunc_rinr (n : ℕ)
    (q : (RConf (n + 1) × RConf (n + 1)) × (RConf (n + 1) × RConf (n + 1))) :
    rtrunc (n + 1) (rinr (n + 1) q)
      = rinr n ((rtrunc n q.1.1, rtrunc n q.1.2), (rtrunc n q.2.1, rtrunc n q.2.2)) := rfl

/-- Fourfold product of a measure, written as a product of two pairs. -/
noncomputable def rprod4 {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Measure ((α × α) × (α × α)) := (μ.prod μ).prod (μ.prod μ)

/-- The law of the depth-`n` tree of replacement choices. -/
noncomputable def rMeasure (pd ps : ℝ) : (n : ℕ) → Measure (RConf n)
  | 0 => Measure.dirac ()
  | (n + 1) =>
      ENNReal.ofReal ps • ((rMeasure pd ps n).prod (rMeasure pd ps n)).map (rinl n)
        + ENNReal.ofReal pd • (rprod4 (rMeasure pd ps n)).map (rinr n)

lemma rMeasure_succ (pd ps : ℝ) (n : ℕ) :
    rMeasure pd ps (n + 1) =
      ENNReal.ofReal ps • ((rMeasure pd ps n).prod (rMeasure pd ps n)).map (rinl n)
        + ENNReal.ofReal pd • (rprod4 (rMeasure pd ps n)).map (rinr n) := rfl

variable {pd ps : ℝ}

instance isProb_rMeasure (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∀ n, IsProbabilityMeasure (rMeasure pd ps n)
  | 0 => by
      constructor
      simp [rMeasure]
  | (n + 1) => by
      haveI := isProb_rMeasure hpd hps hsum n
      constructor
      rw [rMeasure_succ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
        Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
      rw [Set.preimage_univ, Set.preimage_univ, rprod4]
      rw [measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
        ← ENNReal.ofReal_add hps hpd, hsum, ENNReal.ofReal_one]

/-- The law of `R_n` computed from the tree is the law of `R_n` from Subsection 4.1. -/
theorem rMeasure_map_Rres (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    (rMeasure pd ps n).map (Rres n) = lawMeasure pd ps n := by
  induction n with
  | zero =>
      rw [lawMeasure_zero, rMeasure, Measure.map_dirac Measurable.of_discrete]
      rfl
  | succ n ih =>
      haveI := isProb_rMeasure hpd hps hsum n
      haveI : IsProbabilityMeasure (lawMeasure pd ps n) := isProb_lawMeasure hpd hps hsum n
      rw [rMeasure_succ, lawMeasure_succ, Measure.map_add _ _ Measurable.of_discrete,
        Measure.map_smul, Measure.map_smul]
      congr 1
      · congr 1
        rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        have h : (Rres (n + 1)) ∘ (rinl n) = seriesMap ∘ (Prod.map (Rres n) (Rres n)) := by
          funext q
          simp [seriesMap]
        rw [h, ← Measure.map_map measurable_seriesMap Measurable.of_discrete,
          ← Measure.map_prod_map _ _ (f := Rres n) (g := Rres n)
            Measurable.of_discrete Measurable.of_discrete, ih]
      · congr 1
        rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        have hmapprod : (rprod4 (rMeasure pd ps n)).map
            (Prod.map (Prod.map (Rres n) (Rres n)) (Prod.map (Rres n) (Rres n)))
            = ((lawMeasure pd ps n).prod (lawMeasure pd ps n)).prod
                ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
          rw [rprod4, ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
            ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete, ih]
        have key : (rprod4 (rMeasure pd ps n)).map
            ((⇑MeasurableEquiv.prodAssoc) ∘
              (Prod.map (Prod.map (Rres n) (Rres n)) (Prod.map (Rres n) (Rres n))))
            = Reduced.prod4 (lawMeasure pd ps n) := by
          rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable Measurable.of_discrete,
            hmapprod]
          exact (measurePreserving_prodAssoc (lawMeasure pd ps n) (lawMeasure pd ps n)
            ((lawMeasure pd ps n).prod (lawMeasure pd ps n))).map_eq
        have hcomp : (Rres (n + 1)) ∘ (rinr n)
            = diamondMap ∘ ((⇑MeasurableEquiv.prodAssoc) ∘
                (Prod.map (Prod.map (Rres n) (Rres n)) (Prod.map (Rres n) (Rres n)))) := by
          funext q
          simp [diamondMap, MeasurableEquiv.prodAssoc]
        rw [hcomp, ← Measure.map_map measurable_diamondMap Measurable.of_discrete, key]

/-- The window `(R_0, R_1, …, R_n)` of the reduced process, read off a depth-`n` tree. -/
noncomputable def rwin : (n : ℕ) → RConf n → (Fin (n + 1) → ℝ)
  | 0 => fun t _ => Rres 0 t
  | (n + 1) => fun t => Fin.snoc (rwin n (rtrunc n t)) (Rres (n + 1) t)

lemma rwin_succ (n : ℕ) (t : RConf (n + 1)) :
    rwin (n + 1) t = Fin.snoc (rwin n (rtrunc n t)) (Rres (n + 1) t) := rfl

end Cluster
