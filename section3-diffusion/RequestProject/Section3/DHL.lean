import RequestProject.Section3.SpectralDimension
import RequestProject.Section3.Recursions
import RequestProject.Section3.ConditionalMain

/-!
# Section 3, step 4: the diamond hierarchical lattice as a worked example

The final example of Section 3 of *Iterated Graph Systems (I)* (arXiv:2603.13798)
specialises the on-diagonal heat-kernel estimates to the one-colour EIGS
generating the diamond hierarchical lattice (DHL), where

  `d_box = 2`, `d_deg = 2`, `d_res = 0`, `d_walk = 2`.

The paper then records
* `p_t(x,x) ≍ t^{-1/2}` for every finite-born point `x ∈ 𝒱`;
* `|log t|^{-2-ε} t^{-1} ≲ p_t(x,x) ≲ t^{-1}` for `μ`-a.e. infinite-born point.

Taking those two-sided estimates as input (they are the black boxes here), the
local spectral dimensions `1` and `2` follow from
`tendsto_spectral_dimension_of_bounds`.  The DHL exponents themselves are checked
by `norm_num` from the dimension formulas.
-/

namespace IGS

open Filter Topology

/-- The finite-born exponent `d_box (1 - 1/d_deg) / d_walk` equals `1/2` for the DHL. -/
theorem dhl_finite_born_exponent :
    (2 : ℝ) * (1 - 1 / 2) / 2 = 1 / 2 := by norm_num

/-- The infinite-born exponent `d_box / d_walk` equals `1` for the DHL. -/
theorem dhl_infinite_born_exponent : (2 : ℝ) / 2 = 1 := by norm_num

/--
**DHL, finite-born points.**
From `c t^{-1/2} ≤ p_t(x,x) ≤ C t^{-1/2}` for small `t`, the local spectral
dimension at a finite-born point of the DHL equals `1`.
-/
theorem dhl_spectral_dimension_finite_born
    (p : ℝ → ℝ) (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, c * t ^ (-(1 / 2 : ℝ)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, p t ≤ C * t ^ (-(1 / 2 : ℝ))) :
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := tendsto_spectral_dimension_of_pure_bounds p (1 / 2 : ℝ) c C t₀ hc hC ht₀ hlow hup
  norm_num at h
  convert h using 2 with t
  ring

/--
**DHL, almost every infinite-born point.**
From `c |log t|^{-2-ε} t^{-1} ≤ p_t(x,x) ≤ C t^{-1}` for small `t`, the local
spectral dimension equals `2`; the logarithmic correction is invisible to the
spectral dimension.
-/
theorem dhl_spectral_dimension_infinite_born
    (p : ℝ → ℝ) (eps c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      c * |Real.log t| ^ (-(2 + eps)) * t ^ (-(1 : ℝ)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, p t ≤ C * t ^ (-(1 : ℝ))) :
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have h := tendsto_spectral_dimension_of_bounds p (1 : ℝ) (2 + eps) c C t₀ hc hC ht₀ hlow hup
  norm_num at h
  convert h using 2 with t
  ring

/--
**DHL and the recurrence criterion.**
For the DHL one has `d_box = 2` and `d_res = 0`, so the Einstein relation gives
local spectral dimension `2 d_box / (d_box + d_res) = 2` at almost every
infinite-born point, which is *not* `< 2`; consistently with
`spectral_lt_two_iff_resistance_pos`, the resistance dimension is not positive.
-/
theorem dhl_not_strictly_recurrent :
    ¬ (2 * (2 : ℝ) / (2 + 0) < 2) := by
  rw [spectral_lt_two_iff_resistance_pos 2 0 (by norm_num)]
  norm_num

/-!
### Non-vacuity of the conditional formulation

`HeatKernelData` is a bundle of hypotheses, so it is worth exhibiting an
instance: the DHL finite-born exponents with the exact kernel `p_t = t^{-1/2}`.
This confirms that the conditional theorems of
`RequestProject.Section3.ConditionalMain` are not vacuously true.
-/

open MeasureTheory in
/-- A toy instance of `HeatKernelData` carrying the DHL exponents. -/
noncomputable def dhlToyData : HeatKernelData Unit where
  mu := Measure.dirac ()
  V := Set.univ
  p := fun t _ _ => t ^ (-(1 / 2 : ℝ))
  dbox := 2
  ddeg := 2
  dwalk := 2
  hddeg := by norm_num
  hdwalk := by norm_num
  finite_born_bounds := by
    intro x _
    refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro t _
    norm_num
  infinite_born_bounds := by
    filter_upwards with x hx
    exact absurd (Set.mem_univ x) hx

/-- The local spectral dimension of the toy DHL data equals `1`, as in the paper. -/
theorem dhlToyData_spectral_dim :
    LocalSpectralDim dhlToyData.p () 1 := by
  have h := dhlToyData.spectral_dim_finite_born (x := ()) (Set.mem_univ _)
  norm_num [dhlToyData] at h ⊢
  exact h

end IGS
