import Mathlib

/-!
# §3.2, step 3: Theorem `sec32_resistance_metric`

*Iterated Graph Systems (I)* (arXiv:2603.13798), Theorem `sec32_resistance_metric`
states that there is a resistance form `(ℰ_R, ℱ_R)` on `Ξ_M` whose trace on
`V(Ξ^m)` is `ℰ_m^W`, that its resistance metric restricts to `R_*` on `𝒱`, and
that **it induces the same topology as the natural metric `d_{Ξ_M}`**.

The construction of the resistance form out of compatible finite traces, and the
identification of its resistance metric with `R_*`, are what the paper imports
from Kigami; they stay black boxes.  What the paper actually argues is the last
point, and that is what is proved here:

* `uniformContinuous_of_cell_bound` — the consequence of Lemma
  `sec32_point_boundary` used in the proof: if any two points of `𝒱` that are
  `d`-close lie in a common level-`m` cell (or star), so that
  `R_*(x_j,x_{j'}) ≤ 2C_∂ρ(Ψ)^{-m}`, then the identity `(𝒱,d) → (𝒱,R_*)` is
  uniformly continuous.  In particular `d`-convergent sequences are
  `R_*`-Cauchy, which is exactly the paper's first display.
* `iota` — the resulting extension `ι : Ξ_M → Ξ_R` to the `R_*`-completion,
  together with `iota_coe`, `continuous_iota`.
* `iota_surjective` — the image is compact, hence closed, and contains the dense
  set `𝒱`.
* `iota_injective` — two distinct points of `Ξ_M` are separated by a harmonic
  spline (Lemma `sec31_continuous_harmonics`), which has finite energy and
  therefore extends continuously to `Ξ_R`.
* `resistanceHomeo` — a continuous bijection from a compact space to a Hausdorff
  space is a homeomorphism.

The setting is the abstract one the argument needs: `X` is a compact metric space
(`Ξ_M` with its natural metric), `s ⊆ X` a dense subset (`𝒱`), `Y` a complete
metric space (`Ξ_R`) and `g : s → Y` the canonical map with dense range, whose
metric is `R_*` by construction.
-/

namespace IGS.Sec32

open Filter Topology Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {s : Set X} {g : s → Y}

/--
**From Lemma `sec32_point_boundary` to uniform continuity.**
If for every level `m` there is a `d`-scale `δ` below which any two points of
`𝒱` have `R_*`-distance at most `2C ρ^{-m}`, and `ρ > 1`, then the canonical map
`(𝒱, d) → (𝒱, R_*)` is uniformly continuous.
-/
theorem uniformContinuous_of_cell_bound (g : s → Y) {rho C : ℝ} (hrho : 1 < rho)
    (hcell : ∀ m : ℕ, ∃ δ > 0, ∀ u v : s,
      dist (u : X) (v : X) < δ → dist (g u) (g v) ≤ 2 * C * (rho ^ m)⁻¹) :
    UniformContinuous g := by
  rw [Metric.uniformContinuous_iff]
  intro eps heps
  -- pick a level `m` with `2Cρ^{-m} < eps`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C < eps * rho ^ m := by
    have hpow : Tendsto (fun m : ℕ => eps * rho ^ m) atTop atTop :=
      Tendsto.const_mul_atTop heps (tendsto_pow_atTop_atTop_of_one_lt hrho)
    exact (hpow.eventually_gt_atTop (2 * C)).exists
  obtain ⟨δ, hδ, hbound⟩ := hcell m
  refine ⟨δ, hδ, fun {u v} huv => ?_⟩
  have hpowpos : (0 : ℝ) < rho ^ m := by positivity
  have hlt : 2 * C * (rho ^ m)⁻¹ < eps := by
    rw [mul_inv_lt_iff₀ hpowpos]
    exact hm
  exact lt_of_le_of_lt (hbound u v huv) hlt

variable [CompleteSpace Y]

/-- The map `ι : Ξ_M → Ξ_R` of Theorem `sec32_resistance_metric`. -/
noncomputable def iota (hs : Dense s) (g : s → Y) : X → Y := hs.extend g

omit [CompleteSpace Y] in
theorem iota_coe (hs : Dense s) (hg : UniformContinuous g) (x : s) : iota hs g x = g x :=
  hs.extend_of_ind hg x

theorem uniformContinuous_iota (hs : Dense s) (hg : UniformContinuous g) :
    UniformContinuous (iota hs g) :=
  hs.uniformContinuous_extend hg

theorem continuous_iota (hs : Dense s) (hg : UniformContinuous g) : Continuous (iota hs g) :=
  (uniformContinuous_iota hs hg).continuous

variable [CompactSpace X]

/--
**Surjectivity.**  `ι(Ξ_M)` is compact, hence closed, and contains `𝒱`, which is
dense in the completion `Ξ_R`.
-/
theorem iota_surjective (hs : Dense s) (hg : UniformContinuous g) (hgd : DenseRange g) :
    Function.Surjective (iota hs g) := by
  have hcont := continuous_iota hs hg
  have hcompact : IsCompact (range (iota hs g)) := isCompact_range hcont
  have hclosed : IsClosed (range (iota hs g)) := hcompact.isClosed
  have hsub : range g ⊆ range (iota hs g) := by
    rintro y ⟨x, rfl⟩
    exact ⟨(x : X), iota_coe hs hg x⟩
  have : (univ : Set Y) ⊆ range (iota hs g) := by
    calc (univ : Set Y) = closure (range g) := hgd.closure_eq.symm
      _ ⊆ closure (range (iota hs g)) := closure_mono hsub
      _ = range (iota hs g) := hclosed.closure_eq
  intro y
  exact this (mem_univ y)

omit [CompactSpace X] in
/--
**Injectivity.**  If any two distinct points of `Ξ_M` are separated by a function
`u` that is continuous for the natural topology and is the restriction of a
function `ũ` continuous on `Ξ_R` (a finite-energy harmonic spline, by Lemma
`sec31_continuous_harmonics`), then `ι` is injective.
-/
theorem iota_injective (hs : Dense s) (hg : UniformContinuous g)
    (hsep : ∀ x y : X, x ≠ y → ∃ (u : X → ℝ) (u' : Y → ℝ),
      Continuous u ∧ Continuous u' ∧ (∀ p : s, u' (g p) = u (p : X)) ∧ u x ≠ u y) :
    Function.Injective (iota hs g) := by
  intro x y hxy
  by_contra hne
  obtain ⟨u, u', hu, hu', hcomp, hsepxy⟩ := hsep x y hne
  -- `u' ∘ ι` and `u` are continuous and agree on the dense set `s`
  have hagree : ∀ z ∈ s, (u' ∘ iota hs g) z = u z := by
    intro z hz
    have := hcomp ⟨z, hz⟩
    simpa [Function.comp, iota_coe hs hg ⟨z, hz⟩] using this
  have heq : ∀ z : X, u' (iota hs g z) = u z :=
    fun z => congrFun (Continuous.ext_on hs (hu'.comp (continuous_iota hs hg)) hu hagree) z
  have : u x = u y := by rw [← heq x, ← heq y, hxy]
  exact hsepxy this

/--
**Theorem `sec32_resistance_metric`, topological part.**
`ι : Ξ_M → Ξ_R` is a homeomorphism: the resistance metric induces the same
topology as the natural metric.
-/
noncomputable def resistanceHomeo (hs : Dense s) (hg : UniformContinuous g) (hgd : DenseRange g)
    (hsep : ∀ x y : X, x ≠ y → ∃ (u : X → ℝ) (u' : Y → ℝ),
      Continuous u ∧ Continuous u' ∧ (∀ p : s, u' (g p) = u (p : X)) ∧ u x ≠ u y) :
    X ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (iota hs g) ⟨iota_injective hs hg hsep, iota_surjective hs hg hgd⟩)
    (continuous_iota hs hg)

@[simp]
theorem resistanceHomeo_apply (hs : Dense s) (hg : UniformContinuous g) (hgd : DenseRange g)
    (hsep : ∀ x y : X, x ≠ y → ∃ (u : X → ℝ) (u' : Y → ℝ),
      Continuous u ∧ Continuous u' ∧ (∀ p : s, u' (g p) = u (p : X)) ∧ u x ≠ u y) (x : X) :
    resistanceHomeo hs hg hgd hsep x = iota hs g x := rfl

/-- On `𝒱` the homeomorphism is the identity: it extends the canonical map. -/
theorem resistanceHomeo_coe (hs : Dense s) (hg : UniformContinuous g) (hgd : DenseRange g)
    (hsep : ∀ x y : X, x ≠ y → ∃ (u : X → ℝ) (u' : Y → ℝ),
      Continuous u ∧ Continuous u' ∧ (∀ p : s, u' (g p) = u (p : X)) ∧ u x ≠ u y) (p : s) :
    resistanceHomeo hs hg hgd hsep (p : X) = g p := iota_coe hs hg p

end IGS.Sec32
