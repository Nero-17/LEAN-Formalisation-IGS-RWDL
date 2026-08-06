import RequestProject.Cluster.DHL

/-!
# Resistance laws and their series / parallel combinations

This file introduces the notion of a **resistance law**: a measure `rho` on `ℝ≥0∞` which splits as
a mass `m` at `⊤` (the two terminals are disconnected) plus the image under `ENNReal.ofReal` of a
finite measure `lam` carried by the positive reals (the resistance of a connected cluster).

We compute how a resistance law transforms under the series (`sumLaw`) and parallel (`parLaw`)
combinations of two independent copies.  Together with the recursion `resLaw_succ` of `DHL.lean`
this is the engine of Proposition 4.2.
-/

namespace Cluster

open MeasureTheory Reduced
open scoped ENNReal

/-- Parallel combination of two real resistances, as a map on pairs. -/
noncomputable def parMap (q : ℝ × ℝ) : ℝ := Reduced.par q.1 q.2

@[fun_prop, measurability]
lemma measurable_parMap : Measurable parMap := by
  unfold parMap Reduced.par; fun_prop

attribute [fun_prop, measurability] Reduced.measurable_seriesMap Reduced.measurable_diamondMap

lemma isFiniteMeasure_smul {α : Type*} [MeasurableSpace α] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (mu : Measure α) [IsFiniteMeasure mu] : IsFiniteMeasure (c • mu) := by
  constructor
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top mu _)

/-- Parallel combination of two positive resistances, in `ℝ≥0∞`. -/
lemma ofReal_parE {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parE (ENNReal.ofReal x, ENNReal.ofReal y) = ENNReal.ofReal (parMap (x, y)) := by
  have h1 : (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal x⁻¹ := (ENNReal.ofReal_inv_of_pos hx).symm
  have h2 : (ENNReal.ofReal y)⁻¹ = ENNReal.ofReal y⁻¹ := (ENNReal.ofReal_inv_of_pos hy).symm
  rw [parE, h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [parMap, Reduced.par]
  field_simp
  ring

/-- The parallel combination with a disconnected branch is the identity. -/
@[simp] lemma parE_top_left (z : ℝ≥0∞) : parE (⊤, z) = z := by
  simp [parE]

@[simp] lemma parE_top_right (z : ℝ≥0∞) : parE (z, ⊤) = z := by
  simp [parE]

/-- `rho` is the law of a two-terminal resistance with disconnection mass `m` and finite part
`lam`: a measure on `ℝ≥0∞` given by mass `m` at `⊤` plus the image of the finite measure `lam`,
which is carried by the positive reals. -/
structure IsResLaw (rho : Measure ℝ≥0∞) (m : ℝ≥0∞) (lam : Measure ℝ) : Prop where
  /-- the decomposition of `rho` -/
  eq : rho = m • Measure.dirac ⊤ + lam.map ENNReal.ofReal
  /-- the finite part is carried by the positive reals -/
  pos : ∀ᵐ x ∂lam, 0 < x
  /-- the finite part is a finite measure -/
  finite : IsFiniteMeasure lam
  /-- the disconnection mass is finite -/
  mass_ne_top : m ≠ ⊤

namespace IsResLaw

variable {rho sig : Measure ℝ≥0∞} {m m' : ℝ≥0∞} {lam lam' : Measure ℝ}

lemma finite_rho (h : IsResLaw rho m lam) : IsFiniteMeasure rho := by
  haveI := h.finite
  haveI := isFiniteMeasure_smul h.mass_ne_top (Measure.dirac (⊤ : ℝ≥0∞))
  rw [h.eq]
  infer_instance

/-- The product of two resistance laws splits into four pieces. -/
lemma prod_eq (h : IsResLaw rho m lam) (h' : IsResLaw sig m' lam') :
    rho.prod sig =
      ((m * m') • Measure.dirac (⊤, ⊤)
        + m • Measure.map (fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y)) lam')
      + (m' • Measure.map (fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞))) lam
        + Measure.map (Prod.map ENNReal.ofReal ENNReal.ofReal) (lam.prod lam')) := by
  haveI := h.finite
  haveI := h'.finite
  haveI := isFiniteMeasure_smul h.mass_ne_top (Measure.dirac (⊤ : ℝ≥0∞))
  haveI := isFiniteMeasure_smul h'.mass_ne_top (Measure.dirac (⊤ : ℝ≥0∞))
  have hof : Measurable (ENNReal.ofReal) := ENNReal.measurable_ofReal
  have p1 : (m • Measure.dirac (⊤ : ℝ≥0∞)).prod (m' • Measure.dirac (⊤ : ℝ≥0∞))
      = (m * m') • Measure.dirac ((⊤ : ℝ≥0∞), (⊤ : ℝ≥0∞)) := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac, smul_smul]
  have p2 : (m • Measure.dirac (⊤ : ℝ≥0∞)).prod (Measure.map ENNReal.ofReal lam')
      = m • Measure.map (fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y)) lam' := by
    rw [Measure.prod_smul_left, Measure.dirac_prod, Measure.map_map (by fun_prop) hof]
    rfl
  have p3 : (Measure.map ENNReal.ofReal lam).prod (m' • Measure.dirac (⊤ : ℝ≥0∞))
      = m' • Measure.map (fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞))) lam := by
    rw [Measure.prod_smul_right, Measure.prod_dirac, Measure.map_map (by fun_prop) hof]
    rfl
  have p4 : (Measure.map ENNReal.ofReal lam).prod (Measure.map ENNReal.ofReal lam')
      = Measure.map (Prod.map ENNReal.ofReal ENNReal.ofReal) (lam.prod lam') :=
    Measure.map_prod_map _ _ hof hof
  rw [h.eq, h'.eq, Measure.add_prod, Measure.prod_add, Measure.prod_add, p1, p2, p3, p4]

end IsResLaw

/-- Series combination of two resistance laws. -/
theorem IsResLaw.sum {rho sig : Measure ℝ≥0∞} {m m' : ℝ≥0∞} {lam lam' : Measure ℝ}
    (h : IsResLaw rho m lam) (h' : IsResLaw sig m' lam') :
    IsResLaw (sumLaw rho sig) (m * m' + m * lam' Set.univ + m' * lam Set.univ)
      ((lam.prod lam').map seriesMap) := by
  haveI := h.finite
  haveI := h'.finite
  have hof : Measurable (ENNReal.ofReal) := ENNReal.measurable_ofReal
  have haeprod : ∀ᵐ z ∂(lam.prod lam'), z.1 ∈ Set.Ioi (0 : ℝ) ∧ z.2 ∈ Set.Ioi (0 : ℝ) :=
    Reduced.ae_prod_box measurableSet_Ioi measurableSet_Ioi
      (by filter_upwards [h.pos] with x hx using hx)
      (by filter_upwards [h'.pos] with x hx using hx)
  have hkey : (sumE ∘ Prod.map ENNReal.ofReal ENNReal.ofReal)
      =ᵐ[lam.prod lam'] (ENNReal.ofReal ∘ seriesMap) := by
    filter_upwards [haeprod] with z hz
    simp only [sumE, Prod.map, seriesMap, Function.comp_apply]
    exact (ENNReal.ofReal_add hz.1.le hz.2.le).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sumLaw
    rw [h.prod_eq h']
    simp only [Measure.map_add _ _ measurable_sumE, Measure.map_smul,
      Measure.map_dirac measurable_sumE]
    rw [Measure.map_map measurable_sumE
        (by fun_prop : Measurable (fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y))),
      Measure.map_map measurable_sumE
        (by fun_prop : Measurable (fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞)))),
      Measure.map_map measurable_sumE
        (by fun_prop : Measurable (Prod.map ENNReal.ofReal ENNReal.ofReal)),
      Measure.map_congr hkey, ← Measure.map_map hof measurable_seriesMap]
    have e1 : (sumE ∘ fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y)) = fun _ : ℝ => (⊤ : ℝ≥0∞) := by
      funext y; simp [sumE]
    have e2 : (sumE ∘ fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞))) = fun _ : ℝ => (⊤ : ℝ≥0∞) := by
      funext x; simp [sumE]
    rw [e1, e2, Measure.map_const, Measure.map_const, smul_smul, smul_smul, sumE]
    simp only [add_top]
    rw [add_smul, add_smul]
    abel
  · have hmeas : Measurable seriesMap := measurable_seriesMap
    rw [ae_map_iff hmeas.aemeasurable measurableSet_Ioi]
    filter_upwards [haeprod] with z hz
    simp only [Set.mem_Ioi, seriesMap] at *
    linarith [hz.1, hz.2]
  · infer_instance
  · have h1 : lam Set.univ ≠ ⊤ := measure_ne_top lam _
    have h2 : lam' Set.univ ≠ ⊤ := measure_ne_top lam' _
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h.mass_ne_top h'.mass_ne_top,
        ENNReal.mul_ne_top h.mass_ne_top h2⟩, ENNReal.mul_ne_top h'.mass_ne_top h1⟩

/-- Parallel combination of two resistance laws.  The two mixed terms are exactly the deletion of
a dangling (disconnected) branch. -/
theorem IsResLaw.par {rho sig : Measure ℝ≥0∞} {m m' : ℝ≥0∞} {lam lam' : Measure ℝ}
    (h : IsResLaw rho m lam) (h' : IsResLaw sig m' lam') :
    IsResLaw (parLaw rho sig) (m * m')
      (m • lam' + m' • lam + (lam.prod lam').map parMap) := by
  haveI := h.finite
  haveI := h'.finite
  haveI := isFiniteMeasure_smul h.mass_ne_top lam'
  haveI := isFiniteMeasure_smul h'.mass_ne_top lam
  have hof : Measurable (ENNReal.ofReal) := ENNReal.measurable_ofReal
  have haeprod : ∀ᵐ z ∂(lam.prod lam'), z.1 ∈ Set.Ioi (0 : ℝ) ∧ z.2 ∈ Set.Ioi (0 : ℝ) :=
    Reduced.ae_prod_box measurableSet_Ioi measurableSet_Ioi
      (by filter_upwards [h.pos] with x hx using hx)
      (by filter_upwards [h'.pos] with x hx using hx)
  have hkey : (parE ∘ Prod.map ENNReal.ofReal ENNReal.ofReal)
      =ᵐ[lam.prod lam'] (ENNReal.ofReal ∘ parMap) := by
    filter_upwards [haeprod] with z hz
    exact ofReal_parE hz.1 hz.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold parLaw
    rw [h.prod_eq h']
    simp only [Measure.map_add _ _ measurable_parE, Measure.map_smul,
      Measure.map_dirac measurable_parE]
    rw [Measure.map_map measurable_parE
        (by fun_prop : Measurable (fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y))),
      Measure.map_map measurable_parE
        (by fun_prop : Measurable (fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞)))),
      Measure.map_map measurable_parE
        (by fun_prop : Measurable (Prod.map ENNReal.ofReal ENNReal.ofReal)),
      Measure.map_congr hkey, ← Measure.map_map hof measurable_parMap]
    have e1 : (parE ∘ fun y : ℝ => ((⊤ : ℝ≥0∞), ENNReal.ofReal y)) = ENNReal.ofReal := by
      funext y; simp
    have e2 : (parE ∘ fun x : ℝ => (ENNReal.ofReal x, (⊤ : ℝ≥0∞))) = ENNReal.ofReal := by
      funext x; simp
    have htop : parE ((⊤ : ℝ≥0∞), (⊤ : ℝ≥0∞)) = ⊤ := by simp [parE]
    rw [e1, e2, htop, Measure.map_add _ _ hof, Measure.map_add _ _ hof,
      Measure.map_smul, Measure.map_smul]
    abel
  · have hmeas : Measurable parMap := measurable_parMap
    have hpar : ∀ᵐ z ∂((lam.prod lam').map parMap), 0 < z := by
      rw [ae_map_iff hmeas.aemeasurable measurableSet_Ioi]
      filter_upwards [haeprod] with z hz
      obtain ⟨h1, h2⟩ := hz
      simp only [Set.mem_Ioi] at h1 h2
      simp only [parMap, Reduced.par]
      positivity
    have hl : ∀ᵐ x ∂(m • lam'), 0 < x := by
      have hp := h'.pos
      rw [ae_iff] at hp ⊢
      simp only [Measure.smul_apply, smul_eq_mul, hp, mul_zero]
    have hr : ∀ᵐ x ∂(m' • lam), 0 < x := by
      have hp := h.pos
      rw [ae_iff] at hp ⊢
      simp only [Measure.smul_apply, smul_eq_mul, hp, mul_zero]
    simp only [MeasureTheory.ae_add_measure_iff]
    exact ⟨⟨hl, hr⟩, hpar⟩
  · infer_instance
  · exact ENNReal.mul_ne_top h.mass_ne_top h'.mass_ne_top

/-! ### Rearranging the fourfold product -/

/-- Rearranging a parallel combination of two series pairs into the fourfold diamond map. -/
lemma par_series_prod (L : Measure ℝ) [IsProbabilityMeasure L] :
    (((L.prod L).map seriesMap).prod ((L.prod L).map seriesMap)).map parMap
      = (prod4 L).map diamondMap := by
  have hassoc : Measure.map (⇑MeasurableEquiv.prodAssoc)
      ((L.prod L).prod (L.prod L)) = L.prod (L.prod (L.prod L)) :=
    (measurePreserving_prodAssoc L L (L.prod L)).map_eq
  rw [Measure.map_prod_map _ _ measurable_seriesMap measurable_seriesMap,
    Measure.map_map measurable_parMap (by fun_prop), prod4, ← hassoc,
    Measure.map_map measurable_diamondMap MeasurableEquiv.prodAssoc.measurable]
  congr 1

end Cluster
