import Mathlib
import RequestProject.Section3.ResistanceForm

/-!
# §3.2, step 1: the renormalised effective resistance `R_*` is well defined

Subsection 3.2 of *Iterated Graph Systems (I)* (arXiv:2603.13798) opens with the
definition
`R_m(x,y) := (inf {ℰ_m^W(f,f) : f(x)=0, f(y)=1})⁻¹`
and the assertion that trace compatibility (Lemma `sec31_trace_weighted`) gives
`R_{m+1}(x,y) = R_m(x,y)` for `x,y ∈ V(Ξ^m)`, so that
`R_*(x,y) := R_m(x,y)` is well defined for `x,y ∈ 𝒱 = ⋃_m V(Ξ^m)`.

This file proves exactly that, in an abstract setting that keeps only what the
argument uses:

* an increasing family of "vertex sets" `V : ℕ → Set 𝒱`;
* energies `E m : (𝒱 → ℝ) → ℝ`, non-negative, depending on a function only
  through its restriction to `V m`;
* **trace compatibility**: `E m f` is the greatest lower bound of the energies
  `E (m+1) g` over all `g` agreeing with `f` on `V m`.

Nothing about graphs, conductances or Dirichlet principles is needed here: the
one-cell Dirichlet principle and the trace identity are the content of
`Section31.DirichletPrinciple` and `Section31.TraceMin`.
-/

namespace IGS.Sec32

open Set

variable {𝒱 : Type*}

/-- Two functions agree on a set. -/
def AgreeOn (V : Set 𝒱) (f g : 𝒱 → ℝ) : Prop := ∀ x ∈ V, f x = g x

theorem AgreeOn.rfl' (V : Set 𝒱) (f : 𝒱 → ℝ) : AgreeOn V f f := fun _ _ => rfl

/--
The structural hypotheses of §3.2 on the compatible family `(ℰ_m^W)_{m ≥ 0}`.
`trace` is the trace compatibility of Lemma `sec31_trace_weighted`.
-/
structure CompatibleEnergies (V : ℕ → Set 𝒱) (E : ℕ → (𝒱 → ℝ) → ℝ) : Prop where
  /-- the vertex sets increase along the levels -/
  vmono : ∀ m, V m ⊆ V (m + 1)
  /-- energies are non-negative -/
  nonneg : ∀ m f, 0 ≤ E m f
  /-- `E m` only sees the restriction of its argument to `V m` -/
  loc : ∀ m f g, AgreeOn (V m) f g → E m f = E m g
  /-- trace compatibility: `E m f = min {E (m+1) g : g|_{V m} = f|_{V m}}` -/
  trace : ∀ m f, IsGLB {c | ∃ g, AgreeOn (V m) f g ∧ E (m + 1) g = c} (E m f)

variable {V : ℕ → Set 𝒱} {E : ℕ → (𝒱 → ℝ) → ℝ}

/-- Trace compatibility makes the traced energies non-decreasing in the level. -/
theorem CompatibleEnergies.energy_mono (h : CompatibleEnergies V E) (m : ℕ) (f : 𝒱 → ℝ) :
    E m f ≤ E (m + 1) f :=
  (h.trace m f).1 ⟨f, AgreeOn.rfl' _ f, rfl⟩

/-- The conductance `R_m(x,y)⁻¹`: the minimal energy of a function with `f x = 0`, `f y = 1`. -/
noncomputable def condEnergy (F : (𝒱 → ℝ) → ℝ) (x y : 𝒱) : ℝ :=
  sInf {c | ∃ f : 𝒱 → ℝ, f x = 0 ∧ f y = 1 ∧ F f = c}

open scoped Classical in
/-- The renormalised effective resistance at level `m`. -/
noncomputable def Reff (E : ℕ → (𝒱 → ℝ) → ℝ) (m : ℕ) (x y : 𝒱) : ℝ :=
  if x = y then 0 else (condEnergy (E m) x y)⁻¹

private theorem condSet_nonempty (F : (𝒱 → ℝ) → ℝ) {x y : 𝒱} (hxy : x ≠ y) :
    {c | ∃ f : 𝒱 → ℝ, f x = 0 ∧ f y = 1 ∧ F f = c}.Nonempty := by
  classical
  refine ⟨F (fun z => if z = y then 1 else 0), ⟨fun z => if z = y then 1 else 0, ?_, ?_, rfl⟩⟩
  · simp [hxy]
  · simp

private theorem condSet_bddBelow (F : (𝒱 → ℝ) → ℝ) (hF : ∀ f, 0 ≤ F f) (x y : 𝒱) :
    BddBelow {c | ∃ f : 𝒱 → ℝ, f x = 0 ∧ f y = 1 ∧ F f = c} := by
  refine ⟨0, ?_⟩
  rintro c ⟨f, -, -, rfl⟩
  exact hF f

/--
**Trace compatibility of the conductances.**
For `x ≠ y` in `V m`, minimising the level-`(m+1)` energy under the constraints
`f x = 0`, `f y = 1` gives the same value as minimising the level-`m` energy.
-/
theorem condEnergy_succ_eq (h : CompatibleEnergies V E) {m : ℕ} {x y : 𝒱}
    (hx : x ∈ V m) (hy : y ∈ V m) (hxy : x ≠ y) :
    condEnergy (E (m + 1)) x y = condEnergy (E m) x y := by
  set A := {c | ∃ f : 𝒱 → ℝ, f x = 0 ∧ f y = 1 ∧ E (m + 1) f = c} with hA
  set B := {c | ∃ f : 𝒱 → ℝ, f x = 0 ∧ f y = 1 ∧ E m f = c} with hB
  have hAne : A.Nonempty := condSet_nonempty _ hxy
  have hBne : B.Nonempty := condSet_nonempty _ hxy
  have hAbd : BddBelow A := condSet_bddBelow _ (h.nonneg (m + 1)) x y
  have hBbd : BddBelow B := condSet_bddBelow _ (h.nonneg m) x y
  refine le_antisymm ?_ ?_
  · -- `sInf A ≤ sInf B`: any competitor at level `m` is the infimum of competitors above
    refine le_csInf hBne ?_
    rintro b ⟨f, hf0, hf1, rfl⟩
    refine (h.trace m f).2 ?_
    rintro c ⟨g, hg, rfl⟩
    refine csInf_le hAbd ⟨g, ?_, ?_, rfl⟩
    · rw [← hg x hx]; exact hf0
    · rw [← hg y hy]; exact hf1
  · -- `sInf B ≤ sInf A`: a competitor at level `m+1` restricts to one at level `m`
    refine le_csInf hAne ?_
    rintro a ⟨g, hg0, hg1, rfl⟩
    exact le_trans (csInf_le hBbd ⟨g, hg0, hg1, rfl⟩) (h.energy_mono m g)

/-- The resistances themselves are compatible: `R_{m+1} = R_m` on `V m`. -/
theorem Reff_succ_eq (h : CompatibleEnergies V E) {m : ℕ} {x y : 𝒱}
    (hx : x ∈ V m) (hy : y ∈ V m) :
    Reff E (m + 1) x y = Reff E m x y := by
  unfold Reff
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, condEnergy_succ_eq h hx hy hxy]

/-- Monotonicity of the vertex sets along arbitrary level increments. -/
theorem CompatibleEnergies.vmono_add (h : CompatibleEnergies V E) (m k : ℕ) : V m ⊆ V (m + k) := by
  induction k with
  | zero => simp
  | succ n ih => exact fun x hx => h.vmono (m + n) (ih hx)

/--
**`R_*` is well defined.**
For `x, y ∈ V m` the value `R_n(x,y)` is the same for every level `n ≥ m`.
-/
theorem Reff_stable (h : CompatibleEnergies V E) {m : ℕ} {x y : 𝒱}
    (hx : x ∈ V m) (hy : y ∈ V m) (k : ℕ) :
    Reff E (m + k) x y = Reff E m x y := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hx' : x ∈ V (m + n) := h.vmono_add m n hx
      have hy' : y ∈ V (m + n) := h.vmono_add m n hy
      have hstep : Reff E (m + n + 1) x y = Reff E (m + n) x y := Reff_succ_eq h hx' hy'
      rw [show m + (n + 1) = m + n + 1 from rfl, hstep, ih]

/--
**The domain `ℱ_𝒱` and the limit energy `ℰ_𝒱`.**
Trace compatibility makes `m ↦ E m f` monotone, so for `f` in the domain
(where it is bounded above) the limit defining `ℰ_𝒱(f,f)` exists and is the
supremum.  This is the first sentence of the proof of Theorem
`sec32_resistance_metric`.
-/
theorem traced_energy_tendsto (h : CompatibleEnergies V E) (f : 𝒱 → ℝ)
    (hbdd : BddAbove (Set.range fun m => E m f)) :
    Filter.Tendsto (fun m => E m f) Filter.atTop (nhds (⨆ m, E m f)) :=
  IGS.tendsto_traced_energy (fun m => E m f)
    (monotone_nat_of_le_succ fun m => h.energy_mono m f) hbdd

/-- Consequently `R_m` and `R_n` agree whenever both levels contain `x` and `y`. -/
theorem Reff_eq_of_mem (h : CompatibleEnergies V E) {m n : ℕ} {x y : 𝒱}
    (hxm : x ∈ V m) (hym : y ∈ V m) (hxn : x ∈ V n) (hyn : y ∈ V n) :
    Reff E m x y = Reff E n x y := by
  rcases le_total m n with hmn | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (Reff_stable h hxm hym k).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact Reff_stable h hxn hyn k

end IGS.Sec32
