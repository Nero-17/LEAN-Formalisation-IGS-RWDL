import RequestProject.Section3.SpectralDimension

/-!
# Section 3, step 5: the spectral-dimension theorem as a conditional statement

This file shows what a *black-box* formalisation of the main output of Section 3
of *Iterated Graph Systems (I)* (arXiv:2603.13798) looks like.

The whole construction of Section 3 — the Gromov–Hausdorff limit `Ξ_M`, the
limiting measure `μ`, the Dirichlet form `(ℰ_W, ℱ_W)`, the diffusion `W`, its
heat kernel and the two-sided on-diagonal estimates of Theorem "diffusion-heat" —
is packaged into the structure `HeatKernelData`.  Nothing in that structure is
proved here: it is exactly the list of hypotheses one would have to import from
the analytic theory (Kigami's resistance forms, Fukushima's Dirichlet-form
theory, Kuwae–Shioya's Mosco convergence in varying spaces).

What *is* proved here is the last step of the paper, Theorem
"diffusion-spectral": from that data, the local spectral dimension

  `d_s(x) = -2 lim_{t↓0} log p_t(x,x) / log t`

exists at every finite-born point and at `μ`-almost every infinite-born point,
and equals `2 d_box (1 - 1/d_deg)/d_walk` resp. `2 d_box/d_walk`.

This is a faithful, non-vacuous conditional theorem: the hypotheses are
satisfiable (see `dhlData`-style instances built from the estimates of the
paper's DHL example in `RequestProject.Section3.DHL`), and the conclusion is the
paper's dichotomy.
-/

namespace IGS

open Filter Topology MeasureTheory

/-- `x` has local spectral dimension `d` for the kernel `p`. -/
def LocalSpectralDim {X : Type*} (p : ℝ → X → X → ℝ) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun t => -2 * Real.log (p t x x) / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 d)

/--
All of Section 3 packaged as data: a state space with a reference measure, a set
`V` of finite-born points, an on-diagonal heat kernel and the two families of
two-sided estimates proved in the paper (Theorem "diffusion-heat").
-/
structure HeatKernelData (X : Type*) [MeasurableSpace X] where
  /-- the limiting reference measure `μ_{Ξ_M}` -/
  mu : Measure X
  /-- the set `𝒱` of finite-born points -/
  V : Set X
  /-- the (jointly continuous) heat kernel of the limiting diffusion -/
  p : ℝ → X → X → ℝ
  /-- box (Hausdorff) dimension `d_box(Ξ)` -/
  dbox : ℝ
  /-- degree dimension `d_deg(Ξ)`, `> 1` in the scale-free regime -/
  ddeg : ℝ
  /-- walk dimension `d_walk(Ξ)` -/
  dwalk : ℝ
  hddeg : 1 < ddeg
  hdwalk : 0 < dwalk
  /-- Theorem "diffusion-heat", finite-born case -/
  finite_born_bounds : ∀ x ∈ V, ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      c * t ^ (-(dbox * (1 - 1 / ddeg) / dwalk)) ≤ p t x x ∧
      p t x x ≤ C * t ^ (-(dbox * (1 - 1 / ddeg) / dwalk))
  /-- Theorem "diffusion-heat", almost-every infinite-born case -/
  infinite_born_bounds : ∀ᵐ x ∂mu, x ∉ V → ∀ eps > (0 : ℝ), ∃ c C t₀ : ℝ,
    0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      c * |Real.log t| ^ (-((1 + 1 / (ddeg - 1)) + eps)) * t ^ (-(dbox / dwalk)) ≤ p t x x ∧
      p t x x ≤ C * t ^ (-(dbox / dwalk))

variable {X : Type*} [MeasurableSpace X]

/-- **Theorem "diffusion-spectral", finite-born case.** -/
theorem HeatKernelData.spectral_dim_finite_born (D : HeatKernelData X) {x : X} (hx : x ∈ D.V) :
    LocalSpectralDim D.p x (2 * (D.dbox * (1 - 1 / D.ddeg) / D.dwalk)) := by
  obtain ⟨c, C, t₀, hc, hC, ht₀, hbounds⟩ := D.finite_born_bounds x hx
  exact tendsto_spectral_dimension_of_pure_bounds (fun t => D.p t x x) _ c C t₀ hc hC ht₀
    (fun t ht => (hbounds t ht).1) (fun t ht => (hbounds t ht).2)

/-- **Theorem "diffusion-spectral", almost-every infinite-born case.** -/
theorem HeatKernelData.spectral_dim_infinite_born (D : HeatKernelData X) :
    ∀ᵐ x ∂D.mu, x ∉ D.V → LocalSpectralDim D.p x (2 * (D.dbox / D.dwalk)) := by
  filter_upwards [D.infinite_born_bounds] with x hx hxV
  obtain ⟨c, C, t₀, hc, hC, ht₀, hbounds⟩ := hx hxV 1 zero_lt_one
  exact tendsto_spectral_dimension_of_bounds (fun t => D.p t x x) _
    ((1 + 1 / (D.ddeg - 1)) + 1) c C t₀ hc hC ht₀
    (fun t ht => (hbounds t ht).1) (fun t ht => (hbounds t ht).2)

/--
**The dichotomy of Theorem "diffusion-spectral".**
At `μ`-almost every point the local spectral dimension exists, and it takes the
finite-born value on `𝒱` and the infinite-born value off `𝒱`.
-/
theorem HeatKernelData.spectral_dim_dichotomy (D : HeatKernelData X) :
    ∀ᵐ x ∂D.mu,
      (x ∈ D.V → LocalSpectralDim D.p x (2 * (D.dbox * (1 - 1 / D.ddeg) / D.dwalk))) ∧
      (x ∉ D.V → LocalSpectralDim D.p x (2 * (D.dbox / D.dwalk))) := by
  filter_upwards [D.spectral_dim_infinite_born] with x hx
  exact ⟨fun h => D.spectral_dim_finite_born h, hx⟩

/--
The two values differ exactly in the scale-free regime: the finite-born spectral
dimension is strictly smaller whenever `d_box > 0` and `d_deg < ∞`
(here encoded by `1 < d_deg`).
-/
theorem HeatKernelData.finite_born_dim_lt (D : HeatKernelData X) (hdbox : 0 < D.dbox) :
    2 * (D.dbox * (1 - 1 / D.ddeg) / D.dwalk) < 2 * (D.dbox / D.dwalk) := by
  have h1 : 0 < D.ddeg := lt_trans zero_lt_one D.hddeg
  have h2 : 1 / D.ddeg < 1 := by
    rw [div_lt_one h1]; exact D.hddeg
  have h2' : 0 < 1 / D.ddeg := by positivity
  have h3 : D.dbox * (1 - 1 / D.ddeg) < D.dbox := by nlinarith
  have h4 : D.dbox * (1 - 1 / D.ddeg) / D.dwalk < D.dbox / D.dwalk :=
    div_lt_div_of_pos_right h3 D.hdwalk
  linarith

end IGS
