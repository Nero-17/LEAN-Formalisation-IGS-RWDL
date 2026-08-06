import RequestProject.Cluster.Coarse
import RequestProject.Cluster.Tree

/-!
# Proposition 4.2 as an identity of processes: the reduction map

This file builds the *coupling* announced in the proof of Proposition 4.2: the map

  `Phi n : Conf n → RConf n`

that reads off, from a percolation configuration of the level-`n` DHL, the tree of series/diamond
replacement choices of the reduced process of Subsection 4.1.  Concretely, at each cell one looks
at the two first-generation branches: if both connect the terminals the reduced cell is a
*diamond*, if only one does the reduced cell is the *series* of that branch, and the pieces hanging
off the other branch are deleted (they are dangling, and do not change the two-terminal
resistance).

Three facts are proved about `Phi`:

* `rtrunc_Phi` — `Phi` intertwines coarse-graining of configurations with truncation of trees:
  `rtrunc n (Phi (n+1) c) = Phi n (coarse n c)`; this is the compatibility of the reduction with
  one substitution step;
* `toReal_res_eq_Rres` — `Phi` preserves the two-terminal resistance: for a connected
  configuration, `(res n c).toReal = Rres n (Phi n c)`;
* `Phi_pushforward` — at the critical parameter, `Phi n` pushes the critical percolation measure
  restricted to the connected configurations forward to `p_c` times the law of the reduced tree.

Together they give the process form of Proposition 4.2 (`cluster_resistance_process`): for every
`N`, the whole window `(R_0, R_1, …, R_N)` of two-terminal resistances of the critical cluster,
conditioned on the terminals being connected, has exactly the law of the window
`(R_0, R_1, …, R_N)` of the reduced process.
-/

namespace Cluster

open MeasureTheory Reduced
open scoped ENNReal

/-! ### Auxiliary measure-theoretic lemmas -/

lemma map_comp_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (mu : Measure α) (nu : Measure β) [SFinite mu] [SFinite nu] {f : α → γ} (hf : Measurable f) :
    ((mu.prod nu).map (f ∘ Prod.fst)) = (nu Set.univ) • (mu.map f) := by
  have hfst : (mu.prod nu).map (Prod.fst) = (nu Set.univ) • mu := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply measurable_fst hs, Measure.smul_apply, smul_eq_mul,
      ← Set.prod_univ, Measure.prod_prod, mul_comm]
  rw [← Measure.map_map hf measurable_fst, hfst, Measure.map_smul]

lemma map_comp_snd {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (mu : Measure α) (nu : Measure β) [SFinite mu] [SFinite nu] {f : β → γ} (hf : Measurable f) :
    ((mu.prod nu).map (f ∘ Prod.snd)) = (mu Set.univ) • (nu.map f) := by
  have hsnd : (mu.prod nu).map (Prod.snd) = (mu Set.univ) • nu := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply measurable_snd hs, Measure.smul_apply, smul_eq_mul,
      ← Set.univ_prod, Measure.prod_prod]
  rw [← Measure.map_map hf measurable_snd, hsnd, Measure.map_smul]

/-- If two maps agree on a set, the images of the restricted measure agree. -/
lemma map_restrict_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) {s : Set α} (hs : MeasurableSet s) {f g : α → β} (h : Set.EqOn f g s) :
    (mu.restrict s).map f = (mu.restrict s).map g :=
  Measure.map_congr ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun _ hx => h hx))

/-! ### The reduction map -/

/-- The reduction map: from a percolation configuration of the level-`n` DHL to the tree of
series/diamond replacement choices of the reduced process. -/
def Phi : (n : ℕ) → Conf n → RConf n
  | 0 => fun _ => ()
  | (n + 1) => fun c =>
      if (conn n c.1 && conn n c.2.1) && (conn n c.2.2.1 && conn n c.2.2.2) then
        rinr n ((Phi n c.1, Phi n c.2.1), (Phi n c.2.2.1, Phi n c.2.2.2))
      else if (conn n c.1 && conn n c.2.1) then rinl n (Phi n c.1, Phi n c.2.1)
      else rinl n (Phi n c.2.2.1, Phi n c.2.2.2)

lemma Phi_succ_both (n : ℕ) (c : Conf (n + 1)) (h1 : conn n c.1 = true)
    (h2 : conn n c.2.1 = true) (h3 : conn n c.2.2.1 = true) (h4 : conn n c.2.2.2 = true) :
    Phi (n + 1) c = rinr n ((Phi n c.1, Phi n c.2.1), (Phi n c.2.2.1, Phi n c.2.2.2)) := by
  simp [Phi, h1, h2, h3, h4]

lemma Phi_succ_left (n : ℕ) (c : Conf (n + 1)) (h1 : conn n c.1 = true)
    (h2 : conn n c.2.1 = true) (hB : (conn n c.2.2.1 && conn n c.2.2.2) = false) :
    Phi (n + 1) c = rinl n (Phi n c.1, Phi n c.2.1) := by
  simp [Phi, h1, h2, hB]

lemma Phi_succ_right (n : ℕ) (c : Conf (n + 1)) (hA : (conn n c.1 && conn n c.2.1) = false) :
    Phi (n + 1) c = rinl n (Phi n c.2.2.1, Phi n c.2.2.2) := by
  simp [Phi, hA]

lemma measurable_Phi (n : ℕ) : Measurable (Phi n) := Measurable.of_discrete

/-- The reduction map intertwines coarse-graining with truncation of trees. -/
theorem rtrunc_Phi : ∀ (n : ℕ) (c : Conf (n + 1)), rtrunc n (Phi (n + 1) c) = Phi n (coarse n c)
  | 0 => fun _ => rfl
  | (n + 1) => fun c => by
      have e1 := conn_coarse n c.1
      have e2 := conn_coarse n c.2.1
      have e3 := conn_coarse n c.2.2.1
      have e4 := conn_coarse n c.2.2.2
      have i1 := rtrunc_Phi n c.1
      have i2 := rtrunc_Phi n c.2.1
      have i3 := rtrunc_Phi n c.2.2.1
      have i4 := rtrunc_Phi n c.2.2.2
      by_cases hA : (conn (n + 1) c.1 && conn (n + 1) c.2.1) = true
      · rw [Bool.and_eq_true] at hA
        by_cases hB : (conn (n + 1) c.2.2.1 && conn (n + 1) c.2.2.2) = true
        · rw [Bool.and_eq_true] at hB
          rw [Phi_succ_both (n + 1) c hA.1 hA.2 hB.1 hB.2, rtrunc_rinr,
            Phi_succ_both n (coarse (n + 1) c) (by rw [coarse_succ, e1]; exact hA.1)
              (by rw [coarse_succ, e2]; exact hA.2)
              (by rw [coarse_succ, e3]; exact hB.1)
              (by rw [coarse_succ, e4]; exact hB.2)]
          rw [coarse_succ]
          rw [i1, i2, i3, i4]
        · rw [Bool.not_eq_true] at hB
          rw [Phi_succ_left (n + 1) c hA.1 hA.2 hB, rtrunc_rinl,
            Phi_succ_left n (coarse (n + 1) c) (by rw [coarse_succ, e1]; exact hA.1)
              (by rw [coarse_succ, e2]; exact hA.2)
              (by rw [coarse_succ, e3, e4]; exact hB)]
          rw [coarse_succ, i1, i2]
      · rw [Bool.not_eq_true] at hA
        rw [Phi_succ_right (n + 1) c hA, rtrunc_rinl,
          Phi_succ_right n (coarse (n + 1) c) (by rw [coarse_succ, e1, e2]; exact hA)]
        rw [coarse_succ, i3, i4]

/-! ### The reduction map preserves the resistance -/

lemma toReal_parE {x y : ℝ≥0∞} (hx0 : 0 < x.toReal) (hy0 : 0 < y.toReal) :
    ((x⁻¹ + y⁻¹)⁻¹).toReal = par x.toReal y.toReal := by
  have hx : x ≠ ⊤ := by
    intro h
    rw [h] at hx0
    simp at hx0
  have hxinv : x⁻¹ ≠ ⊤ := by
    simp only [Ne, ENNReal.inv_eq_top]
    intro h
    rw [h] at hx0
    simp at hx0
  have hyinv : y⁻¹ ≠ ⊤ := by
    simp only [Ne, ENNReal.inv_eq_top]
    intro h
    rw [h] at hy0
    simp at hy0
  have hsum : x⁻¹ + y⁻¹ ≠ 0 := by
    intro h
    rw [add_eq_zero, ENNReal.inv_eq_zero] at h
    rw [h.1] at hx
    exact hx rfl
  rw [ENNReal.toReal_inv, ENNReal.toReal_add hxinv hyinv, ENNReal.toReal_inv, ENNReal.toReal_inv]
  rw [par]
  field_simp
  ring

/-- The reduction map preserves the two-terminal resistance. -/
theorem toReal_res_eq_Rres : ∀ (n : ℕ) (c : Conf n), conn n c = true →
    (res n c).toReal = Rres n (Phi n c)
  | 0 => by
      intro c hc
      match c with
      | true => simp
      | false => simp at hc
  | (n + 1) => by
      intro c hc
      have hne : ∀ (m : ℕ) (d : Conf m), conn m d = true → res m d ≠ ⊤ :=
        fun m d h => (res_ne_top_iff_conn m d).2 h
      have htop : ∀ (m : ℕ) (d : Conf m), conn m d = false → res m d = ⊤ := by
        intro m d h
        by_contra hcon
        rw [(res_ne_top_iff_conn m d).1 hcon] at h
        exact Bool.noConfusion h
      have hone : ∀ (m : ℕ) (d : Conf m), res m d ≠ ⊤ → (1 : ℝ) ≤ (res m d).toReal := by
        intro m d h
        have := ENNReal.toReal_mono h (one_le_res m d)
        simpa using this
      by_cases hA : (conn n c.1 && conn n c.2.1) = true
      · rw [Bool.and_eq_true] at hA
        have hx1 := hne n c.1 hA.1
        have hx2 := hne n c.2.1 hA.2
        have ht12 : (0 : ℝ) < (res n c.1 + res n c.2.1).toReal := by
          rw [ENNReal.toReal_add hx1 hx2]
          have := hone n c.1 hx1
          have := hone n c.2.1 hx2
          linarith
        by_cases hB : (conn n c.2.2.1 && conn n c.2.2.2) = true
        · rw [Bool.and_eq_true] at hB
          have hx3 := hne n c.2.2.1 hB.1
          have hx4 := hne n c.2.2.2 hB.2
          have ht34 : (0 : ℝ) < (res n c.2.2.1 + res n c.2.2.2).toReal := by
            rw [ENNReal.toReal_add hx3 hx4]
            have := hone n c.2.2.1 hx3
            have := hone n c.2.2.2 hx4
            linarith
          rw [Phi_succ_both n c hA.1 hA.2 hB.1 hB.2, Rres_rinr, res_succ,
            toReal_parE ht12 ht34, ENNReal.toReal_add hx1 hx2,
            ENNReal.toReal_add hx3 hx4, toReal_res_eq_Rres n c.1 hA.1,
            toReal_res_eq_Rres n c.2.1 hA.2, toReal_res_eq_Rres n c.2.2.1 hB.1,
            toReal_res_eq_Rres n c.2.2.2 hB.2]
          rfl
        · rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hB
          have hs34 : res n c.2.2.1 + res n c.2.2.2 = ⊤ := by
            rw [ENNReal.add_eq_top]
            rcases hB with h | h
            · exact Or.inl (htop n c.2.2.1 (by simpa using h))
            · exact Or.inr (htop n c.2.2.2 (by simpa using h))
          rw [Phi_succ_left n c hA.1 hA.2 (by
              rw [Bool.and_eq_false_iff]; exact hB), Rres_rinl, res_succ, hs34]
          rw [ENNReal.inv_top, add_zero, inv_inv, ENNReal.toReal_add hx1 hx2,
            toReal_res_eq_Rres n c.1 hA.1, toReal_res_eq_Rres n c.2.1 hA.2]
      · rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hA
        have hs12 : res n c.1 + res n c.2.1 = ⊤ := by
          rw [ENNReal.add_eq_top]
          rcases hA with h | h
          · exact Or.inl (htop n c.1 (by simpa using h))
          · exact Or.inr (htop n c.2.1 (by simpa using h))
        have hB : conn n c.2.2.1 = true ∧ conn n c.2.2.2 = true := by
          rw [conn_succ, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
          rcases hc with h | h
          · rcases hA with h' | h' <;> simp_all
          · exact h
        have hx3 := hne n c.2.2.1 hB.1
        have hx4 := hne n c.2.2.2 hB.2
        rw [Phi_succ_right n c (by rw [Bool.and_eq_false_iff]; exact hA), Rres_rinl, res_succ,
          hs12, ENNReal.inv_top, zero_add, inv_inv, ENNReal.toReal_add hx3 hx4,
          toReal_res_eq_Rres n c.2.2.1 hB.1, toReal_res_eq_Rres n c.2.2.2 hB.2]

/-! ### The reduction map transports the critical percolation measure -/

/-- The connected configurations at level `n`. -/
def connSet (n : ℕ) : Set (Conf n) := {c : Conf n | conn n c = true}

lemma measurableSet_connSet (n : ℕ) : MeasurableSet (connSet n) := MeasurableSet.of_discrete

lemma confMeasure_connSet (n : ℕ) : confMeasure pc n (connSet n) = ENNReal.ofReal pc := by
  rw [connSet, ← setOf_res_ne_top, prob_connected n]

/-- Regrouping a level-`(n+1)` configuration as a pair of pairs of level-`n` configurations. -/
def asc (n : ℕ) : (Conf n × Conf n) × (Conf n × Conf n) → Conf (n + 1) :=
  fun w => (w.1.1, w.1.2, w.2.1, w.2.2)

lemma measurable_asc (n : ℕ) : Measurable (asc n) := Measurable.of_discrete

lemma confMeasure_succ_eq_map_asc (n : ℕ) :
    Measure.map (asc n) (((confMeasure pc n).prod (confMeasure pc n)).prod
        ((confMeasure pc n).prod (confMeasure pc n)))
      = confMeasure pc (n + 1) :=
  (measurePreserving_prodAssoc (confMeasure pc n) (confMeasure pc n)
    ((confMeasure pc n).prod (confMeasure pc n))).map_eq

/-- **The coupling identity.**  At the critical parameter, the reduction map pushes the percolation
measure restricted to the connected configurations forward to `p_c` times the law of the reduced
tree of replacement choices. -/
theorem Phi_pushforward (n : ℕ) :
    ((confMeasure pc n).restrict (connSet n)).map (Phi n)
      = ENNReal.ofReal pc • rMeasure (pdiamond pc) (pseries pc) n := by
  induction n with
  | zero =>
      show ((confMeasure pc 0).restrict (connSet 0)).map (fun _ => ())
        = ENNReal.ofReal pc • Measure.dirac ()
      rw [Measure.map_const, Measure.restrict_apply_univ, confMeasure_connSet 0]
  | succ n ih =>
      haveI : IsProbabilityMeasure (confMeasure pc n) := isProb_confMeasure pc_nonneg pc_le_one n
      haveI : IsProbabilityMeasure (rMeasure (pdiamond pc) (pseries pc) n) :=
        isProb_rMeasure pdiamond_pc_nonneg pseries_pc_nonneg pseries_add_pdiamond_pc n
      set mu := confMeasure pc n with hmu
      set q := ENNReal.ofReal pc with hq
      set rM := rMeasure (pdiamond pc) (pseries pc) n with hrM
      set C : Set (Conf n) := connSet n with hC
      set P : Measure (Conf n × Conf n) := mu.prod mu with hP
      set CC : Set (Conf n × Conf n) := C ×ˢ C with hCC
      set Psi : Conf n × Conf n → RConf n × RConf n := Prod.map (Phi n) (Phi n) with hPsi
      haveI hPprob : IsProbabilityMeasure P := by rw [hP]; infer_instance
      have hmeasC : MeasurableSet C := measurableSet_connSet n
      have hmeasCC : MeasurableSet CC := hmeasC.prod hmeasC
      have hmeasPsi : Measurable Psi := Measurable.of_discrete
      -- masses
      have hmuC : mu C = q := confMeasure_connSet n
      have hPCC : P CC = q * q := by rw [hP, hCC, Measure.prod_prod, hmuC]
      have hqq : q * q = ENNReal.ofReal (1 - pc) := by
        rw [hq, ← ENNReal.ofReal_mul pc_nonneg]
        congr 1
        nlinarith [pc_sq]
      have hPCCc : P CCᶜ = q := by
        rw [measure_compl hmeasCC (measure_ne_top _ _), measure_univ, hPCC, hqq]
        refine ENNReal.sub_eq_of_eq_add ENNReal.ofReal_ne_top ?_
        rw [hq, ← ENNReal.ofReal_add pc_nonneg one_sub_pc_nonneg]
        norm_num
      -- the image of the restricted product measure under the pair of reduction maps
      have hPsimap : (P.restrict CC).map Psi = (q * q) • (rM.prod rM) := by
        rw [hP, hCC, ← Measure.prod_restrict, hPsi,
          ← Measure.map_prod_map _ _ (measurable_Phi n) (measurable_Phi n), ih,
          Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
      -- the three pieces of the connected event
      have hE : (asc n) ⁻¹' (connSet (n + 1))
          = (CC ×ˢ CC) ∪ ((CC ×ˢ CCᶜ) ∪ (CCᶜ ×ˢ CC)) := by
        ext w
        simp only [Set.mem_preimage, connSet, Set.mem_setOf_eq, conn_succ, Bool.or_eq_true,
          Bool.and_eq_true, Set.mem_union, Set.mem_prod, Set.mem_compl_iff, hCC, hC, asc,
          connSet]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h3, h4⟩)
          · by_cases hb : (conn n w.2.1 = true ∧ conn n w.2.2 = true)
            · exact Or.inl ⟨⟨h1, h2⟩, hb⟩
            · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, hb⟩)
          · by_cases ha : (conn n w.1.1 = true ∧ conn n w.1.2 = true)
            · exact Or.inl ⟨ha, h3, h4⟩
            · exact Or.inr (Or.inr ⟨ha, h3, h4⟩)
        · rintro (⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩ | ⟨_, h3, h4⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h3, h4⟩
      have hdisj2 : Disjoint (CC ×ˢ CCᶜ) (CCᶜ ×ˢ CC) := by
        rw [Set.disjoint_left]
        rintro w ⟨h1, _⟩ ⟨h2, _⟩
        exact h2 h1
      have hdisj1 : Disjoint (CC ×ˢ CC) ((CC ×ˢ CCᶜ) ∪ (CCᶜ ×ˢ CC)) := by
        rw [Set.disjoint_left]
        rintro w ⟨h1, h2⟩ (⟨_, h⟩ | ⟨h, _⟩)
        · exact h h2
        · exact h h1
      -- the reduction map on each of the three pieces
      have hEq1 : Set.EqOn ((Phi (n + 1)) ∘ (asc n))
          (fun w => rinr n ((Phi n w.1.1, Phi n w.1.2), (Phi n w.2.1, Phi n w.2.2)))
          (CC ×ˢ CC) := by
        rintro w ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact Phi_succ_both n (asc n w) h1 h2 h3 h4
      have hEq2 : Set.EqOn ((Phi (n + 1)) ∘ (asc n))
          (((rinl n) ∘ Psi) ∘ Prod.fst) (CC ×ˢ CCᶜ) := by
        rintro w ⟨⟨h1, h2⟩, hb⟩
        refine Phi_succ_left n (asc n w) h1 h2 ?_
        rw [Bool.and_eq_false_iff]
        by_contra hcon
        push_neg at hcon
        exact hb ⟨by simpa using hcon.1, by simpa using hcon.2⟩
      have hEq3 : Set.EqOn ((Phi (n + 1)) ∘ (asc n))
          (((rinl n) ∘ Psi) ∘ Prod.snd) (CCᶜ ×ˢ CC) := by
        rintro w ⟨ha, _, _⟩
        refine Phi_succ_right n (asc n w) ?_
        rw [Bool.and_eq_false_iff]
        by_contra hcon
        push_neg at hcon
        exact ha ⟨by simpa using hcon.1, by simpa using hcon.2⟩
      -- the three contributions
      have hpiece1 : ((P.prod P).restrict (CC ×ˢ CC)).map ((Phi (n + 1)) ∘ (asc n))
          = ((q * q) * (q * q)) • ((rprod4 rM).map (rinr n)) := by
        rw [map_restrict_congr _ (hmeasCC.prod hmeasCC) hEq1, ← Measure.prod_restrict]
        have hfun : (fun w : (Conf n × Conf n) × (Conf n × Conf n) =>
            rinr n ((Phi n w.1.1, Phi n w.1.2), (Phi n w.2.1, Phi n w.2.2)))
            = (rinr n) ∘ (Prod.map Psi Psi) := rfl
        rw [hfun, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
          ← Measure.map_prod_map _ _ hmeasPsi hmeasPsi, hPsimap,
          Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul, rprod4]
      have hpiece2 : ((P.prod P).restrict (CC ×ˢ CCᶜ)).map ((Phi (n + 1)) ∘ (asc n))
          = q • ((q * q) • ((rM.prod rM).map (rinl n))) := by
        rw [map_restrict_congr _ (hmeasCC.prod hmeasCC.compl) hEq2, ← Measure.prod_restrict,
          map_comp_fst _ _ (Measurable.of_discrete : Measurable ((rinl n) ∘ Psi)),
          Measure.restrict_apply_univ, hPCCc,
          ← Measure.map_map Measurable.of_discrete hmeasPsi, hPsimap, Measure.map_smul]
      have hpiece3 : ((P.prod P).restrict (CCᶜ ×ˢ CC)).map ((Phi (n + 1)) ∘ (asc n))
          = q • ((q * q) • ((rM.prod rM).map (rinl n))) := by
        rw [map_restrict_congr _ (hmeasCC.compl.prod hmeasCC) hEq3, ← Measure.prod_restrict,
          map_comp_snd _ _ (Measurable.of_discrete : Measurable ((rinl n) ∘ Psi)),
          Measure.restrict_apply_univ, hPCCc,
          ← Measure.map_map Measurable.of_discrete hmeasPsi, hPsimap, Measure.map_smul]
      -- assembling
      have hsplit : ((confMeasure pc (n + 1)).restrict (connSet (n + 1))).map (Phi (n + 1))
          = ((P.prod P).restrict (CC ×ˢ CC)).map ((Phi (n + 1)) ∘ (asc n))
            + (((P.prod P).restrict (CC ×ˢ CCᶜ)).map ((Phi (n + 1)) ∘ (asc n))
              + ((P.prod P).restrict (CCᶜ ×ˢ CC)).map ((Phi (n + 1)) ∘ (asc n))) := by
        rw [← confMeasure_succ_eq_map_asc n, ← hP,
          Measure.restrict_map (measurable_asc n) (measurableSet_connSet (n + 1)),
          Measure.map_map (measurable_Phi (n + 1)) (measurable_asc n), hE,
          Measure.restrict_union hdisj1 (((hmeasCC.prod hmeasCC.compl).union
            (hmeasCC.compl.prod hmeasCC))),
          Measure.restrict_union hdisj2 (hmeasCC.compl.prod hmeasCC),
          Measure.map_add _ _ (by exact (measurable_Phi (n + 1)).comp (measurable_asc n)),
          Measure.map_add _ _ (by exact (measurable_Phi (n + 1)).comp (measurable_asc n))]
      -- the arithmetic of the critical parameter
      have hnumd : (q * q) * (q * q) = q * ENNReal.ofReal (pdiamond pc) := by
        rw [hq, ← ENNReal.ofReal_mul pc_nonneg,
          ← ENNReal.ofReal_mul (mul_nonneg pc_nonneg pc_nonneg),
          ← ENNReal.ofReal_mul pc_nonneg]
        congr 1
        rw [pdiamond_pc_eq]
        ring
      have hnums : q * (q * q) + q * (q * q) = q * ENNReal.ofReal (pseries pc) := by
        rw [hq, ← ENNReal.ofReal_mul pc_nonneg, ← ENNReal.ofReal_mul pc_nonneg,
          ← ENNReal.ofReal_add (by nlinarith [pc_pos]) (by nlinarith [pc_pos]),
          ← ENNReal.ofReal_mul pc_nonneg]
        congr 1
        rw [pseries_pc_eq]
        ring
      rw [hsplit, hpiece1, hpiece2, hpiece3, rMeasure_succ, smul_add, smul_smul, smul_smul,
        smul_smul, ← add_smul, hnumd, hnums, ← hrM]
      exact add_comm _ _

/-! ### Proposition 4.2, process form -/

/-- The window `(R_0, R_1, …, R_n)` of two-terminal resistances of the percolation cluster. -/
noncomputable def cwin : (n : ℕ) → Conf n → (Fin (n + 1) → ℝ)
  | 0 => fun c _ => (res 0 c).toReal
  | (n + 1) => fun c => Fin.snoc (cwin n (coarse n c)) ((res (n + 1) c).toReal)

lemma measurable_cwin (n : ℕ) : Measurable (cwin n) := Measurable.of_discrete

/-- On connected configurations the cluster window agrees with the reduced window of the
corresponding tree. -/
theorem cwin_eq_rwin_Phi : ∀ (n : ℕ) (c : Conf n), conn n c = true →
    cwin n c = rwin n (Phi n c)
  | 0 => by
      intro c hc
      funext i
      show (res 0 c).toReal = Rres 0 (Phi 0 c)
      exact toReal_res_eq_Rres 0 c hc
  | (n + 1) => by
      intro c hc
      have hcoarse : conn n (coarse n c) = true := by rw [conn_coarse n c]; exact hc
      rw [show cwin (n + 1) c = Fin.snoc (cwin n (coarse n c)) ((res (n + 1) c).toReal) from rfl,
        rwin_succ, cwin_eq_rwin_Phi n (coarse n c) hcoarse, ← rtrunc_Phi n c,
        toReal_res_eq_Rres (n + 1) c hc]

/-- **Proposition 4.2 (process form).**  At the critical parameter, for every `N` the window
`(R_0, R_1, …, R_N)` of two-terminal effective resistances of the percolation cluster on the
diamond hierarchical lattice — the levels being coupled by coarse-graining, i.e. by the
substitution construction of the paper — conditioned on the two boundary vertices being connected,
has exactly the law of the window `(R_0, R_1, …, R_N)` of the reduced resistance process of
Subsection 4.1. -/
theorem cluster_resistance_process (n : ℕ) :
    (ProbabilityTheory.cond (confMeasure pc n) {c | res n c ≠ ⊤}).map (cwin n)
      = (rMeasure (pdiamond pc) (pseries pc) n).map (rwin n) := by
  have hq : ENNReal.ofReal pc ≠ 0 := by
    simp [pc_pos]
  have hqtop : ENNReal.ofReal pc ≠ ⊤ := ENNReal.ofReal_ne_top
  have hset : {c : Conf n | res n c ≠ ⊤} = connSet n := by
    rw [connSet, setOf_res_ne_top]
  rw [hset, ProbabilityTheory.cond, confMeasure_connSet n, Measure.map_smul,
    map_restrict_congr _ (measurableSet_connSet n)
      (f := cwin n) (g := (rwin n) ∘ (Phi n)) (fun c hc => cwin_eq_rwin_Phi n c hc),
    ← Measure.map_map (Measurable.of_discrete) (measurable_Phi n), Phi_pushforward n,
    Measure.map_smul, smul_smul, ENNReal.inv_mul_cancel hq hqtop, one_smul]

/-! ### Consistency with the one-level statement -/

@[simp] lemma cwin_last : ∀ (n : ℕ) (c : Conf n), cwin n c (Fin.last n) = (res n c).toReal
  | 0 => fun _ => rfl
  | (n + 1) => fun c => by
      rw [show cwin (n + 1) c = Fin.snoc (cwin n (coarse n c)) ((res (n + 1) c).toReal) from rfl,
        Fin.snoc_last]

@[simp] lemma rwin_last : ∀ (n : ℕ) (t : RConf n), rwin n t (Fin.last n) = Rres n t
  | 0 => fun _ => rfl
  | (n + 1) => fun t => by
      rw [rwin_succ, Fin.snoc_last]

/-- The last coordinate of the process statement is the one-level statement: conditionally on the
two terminals being connected, the level-`n` cluster resistance has the law of `R_n`. -/
theorem cluster_resistance_law_of_process (n : ℕ) :
    (ProbabilityTheory.cond (confMeasure pc n) {c | res n c ≠ ⊤}).map
        (fun c => (res n c).toReal)
      = lawMeasure (pdiamond pc) (pseries pc) n := by
  have heval : Measurable (fun v : Fin (n + 1) → ℝ => v (Fin.last n)) := measurable_pi_apply _
  have h := congrArg (fun mu : Measure (Fin (n + 1) → ℝ) => mu.map
    (fun v : Fin (n + 1) → ℝ => v (Fin.last n))) (cluster_resistance_process n)
  simp only at h
  rw [Measure.map_map heval (measurable_cwin n), Measure.map_map heval Measurable.of_discrete,
    show ((fun v : Fin (n + 1) → ℝ => v (Fin.last n)) ∘ cwin n)
      = (fun c => (res n c).toReal) from funext fun c => cwin_last n c,
    show ((fun v : Fin (n + 1) → ℝ => v (Fin.last n)) ∘ rwin n) = Rres n from
      funext fun t => rwin_last n t,
    rMeasure_map_Rres pdiamond_pc_nonneg pseries_pc_nonneg pseries_add_pdiamond_pc n] at h
  exact h

end Cluster
