import RequestProject.Section33.Exponents
import RequestProject.Section33.Volume
import RequestProject.Section33.Skeleton
import RequestProject.Section33.VolumeAE
import RequestProject.Section33.BirthLevel
import RequestProject.Section33.ExitTime
import RequestProject.Section33.HeatUpper
import RequestProject.Section33.Resolvent
import RequestProject.Section33.Main
import RequestProject.Section33.GeneralLower
import RequestProject.Section33.DHLExample
import RequestProject.Section33.BrownianHeat
import RequestProject.Section33.TwoColourExample

/-!
# A formalisation of Section 3.3 of arXiv:2603.13798

*Iterated Graph Systems (I): random walks and diffusion limits*,
§3.3 "Heat kernel for the diffusion limit".

Same rule as for §3.1 and §3.2: **everything the paper itself imports from the
literature (or from its own §2) is an explicit hypothesis**, and everything the
paper argues itself is proved.  No `sorry` and no new axioms appear.

The four scaling parameters `ρ(M), ρ(N), ρ(Ψ), ρ_min(D)` and the four dimensions

`d_box = log ρ(M)/log ρ_min(D)`,  `d_deg = log ρ(M)/log ρ(N)`,
`d_R = log ρ(Ψ)/log ρ_min(D)`,  `d_walk = log(ρ(M)ρ(Ψ))/log ρ_min(D)`

are bundled in `IGS.Sec33.Params`; the standing assumptions are those of the
scale-free regime, `1 < ρ_min(D)`, `1 < ρ(N) < ρ(M)`, `ρ(Ψ) > 0`,
`ρ(M)ρ(Ψ) > 1` (i.e. `d_deg > 1` and `d_walk > 0`; the paper proves
`d_walk ≥ 2`).

This formalisation follows the **current version** of §3.3, in which

* the logarithmic exponent of Lemma `heat-volume` and of the on-diagonal lower
  bound is the sharp `1/(d_deg-1) + ε` (`Params.logExp`), one unit better than
  the exponent `d_deg/(d_deg-1)` of the Hambly–Kumagai route
  (`Params.logExpHK`, `logExp_lt_logExpHK`);
* the proof of Lemma `heat-volume` at a typical infinite-born point distinguishes
  the two cases according to the birth level of the nearby terminal
  (`Section33.BirthLevel`);
* Theorem `general-lower` is stated as `p_t(x,x) ≥ c_x/μ(B(x,C_x t^{1/d_walk}))`,
  at time `t` rather than `2t` (`Section33.GeneralLower`).

## Correspondence with the paper

| paper | file | what is proved here |
|---|---|---|
| definitions of `d_box, d_deg, d_R, d_walk`, Einstein relation | `Section33.Exponents` | `dwalk_eq_dbox_add_dR`, and the three rescaling identities that convert every geometric estimate into a power: `volume_scaling` (`(ρ(N)/ρ(M))^m = (ρ_min(D)^{-m})^{d_box(1-1/d_deg)}`), `mass_scaling`, `time_scaling_fin`/`time_scaling_inf`, plus `log ρ(N)/log(ρ(M)/ρ(N)) = 1/(d_deg-1)` |
| Lemma `heat-volume`, finite-born case | `Section33.Volume` | the choice of the scale `m(r)` with `ρ_min(D)^{-(m+1)} < r ≤ ρ_min(D)^{-m}` (`exists_dyadic_scale`) and the conversion of the quoted counting estimate `μ(B(x,r)) ≍ ρ(N)^{m-k}ρ(M)^{-m}` into `μ(B(x,r)) ≍ r^{d_box(1-1/d_deg)}` with explicit constants (`volume_finite_born`); the lower bound `μ(B(x,r)) ≥ c r^{d_box}` from the cell mass (`volume_lower_cell`) |
| Lemma `heat-volume`, the skeleton estimate `μ(E_{m,L}) ≲ (ρ(N)/ρ(M))^L` | `Section33.Skeleton` | the geometric summation `Σ_{k≤m-L} ρ(M)^kρ(N)^{m-k}ρ(M)^{-m} ≤ (1-q)^{-1}q^L` (`skeleton_sum_bound`, `skeleton_mass_le`) |
| Lemma `heat-volume`, Borel–Cantelli | `Section33.Skeleton` | with `L_m = ⌈(1+ε)log m/log(ρ(M)/ρ(N))⌉`: `q^{L_m} ≤ m^{-(1+ε)}` (`q_pow_Lscale_le`), summability (`summable_q_pow_Lscale`) and the Borel–Cantelli conclusion "almost every `x` avoids `E_{m,L_m}` eventually" (`ae_eventually_notMem_skeleton`); the exponent estimate `ρ(N)^{L_m} ≤ ρ(N) m^{(1+ε)/(d_deg-1)}` (`rN_pow_Lscale_le`), and in the paper's calibration `ρ(N)^{L_m} ≤ ρ(N) m^{1/(d_deg-1)+ε}` (`rN_pow_Lscale_le_logExp`) |
| Lemma `heat-volume`, the two cases for the birth level of the nearby terminal | `Section33.BirthLevel` | `B(x,cρ_min(D)^{-m}) ⊆ B(v,(c+C_*)ρ_min(D)^{-m})` (`ball_subset_ball_of_near_terminal`), "`x ∉ E_{m,L}` forces the birth level of the terminal above `m-L`" (`birth_level_gt_of_notMem'`), and the dichotomy `b_m + c₁ ≤ m` / `m < b_m + c₁` ending at `μ(B) ≲ ρ(N)^{L}ρ(M)^{-m}` in both cases (`geom_bound_of_birth_dichotomy`, `volume_le_of_avoiding_skeleton`) |
| Lemma `heat-volume`, upper bound at a.e. infinite-born point | `Section33.VolumeAE` | the conversion of `μ(B(x,ρ_min(D)^{-m})) ≲ ρ(N)^{L_m}ρ(M)^{-m}` into `μ(B(x,r)) ≤ C|log r|^{(1+ε)/(d_deg-1)}r^{d_box}` (`volume_upper_log`), i.e. into the paper's `C|log r|^{1/(d_deg-1)+ε}r^{d_box}` (`volume_upper_logExp`) |
| Lemma `heat-exit` | `Section33.ExitTime` | the deterministic comparison `y ∈ B(x,r) ⟹ B(x,r) ⊆ B(y,2r)` (`ball_subset_ball_two_mul`), the two limit passages `T → ∞` and `η ↓ 0` of the Fatou argument (`mean_exit_le_of_truncated`), and the resulting `sup_{y∈B(x,r)}E_y[τ_{B(x,r)}] ≤ C2^{d_walk}r^{d_walk}` (`heat_exit_bound`) |
| Proposition `heat-kernel` (exponent) | `Section33.HeatUpper` | the parabolic time scale `T_n = (ρ(M)ρ(Ψ))^{-n}` and the fact that the ultracontractive bound `q(t) ≲ ρ(M)^n` for `T_n ≤ t < T_{n-1}` *is* the stated `C t^{-d_box/d_walk}` (`power_of_geometric`, `global_upper_of_geometric`) |
| Proposition `heat-kernel` (continuity of the resolvent) | `Section33.Resolvent` | the error term of the strong Markov decomposition, `|E_y[∫_0^τ e^{-λt}f(W_t)dt]| ≤ ‖f‖_∞ E_y[τ]` (`abs_integral_le_of_le_mul`), and the resulting oscillation bound "osc `U_λ f` ≤ osc (harmonic) + `2C‖f‖_∞ r^{d_walk}`" (`resolvent_osc_bound`) |
| Theorem `general-lower` | `Section3.OnDiagonalLower`, `Section33.Main`, `Section33.GeneralLower` | the Cauchy–Schwarz argument (earlier file) and its combination with the volume estimates: `on_diagonal_lower_of_volume` (finite-born) and `on_diagonal_lower_of_volume_log` (a.e. infinite-born, including the bound `|log(a t^b)| ≤ (|log a|+b)|log t|`); in the form of the current version, `p_t(x,x) ≥ p_x²/μ(B(x,C_x t^{1/d_walk}))` (`on_diagonal_lower_ball`), together with the two steps of its proof: "`t ≤ a_x r^{d_walk}` ⇒ `P_x(W_t ∈ B(x,r)) ≥ p_x`" (`prob_mem_of_exit_time`) and the choice `r = (t/a_x)^{1/d_walk}` (`exit_radius_eq`) |
| Theorem `diffusion-heat`, lower bounds | `Section33.GeneralLower` | `p_t(x,x) ≥ c t^{-d_box(1-1/d_deg)/d_walk}` at a finite-born point (`heat_lower_finite_born`) and `p_t(x,x) ≥ c|log t|^{-1/(d_deg-1)-ε}t^{-d_box/d_walk}` at a.e. infinite-born point (`heat_lower_infinite_born`) |
| Theorem `diffusion-heat`, finite-born upper bound | `Section33.HeatUpper` | the paper's Nash-type iteration, in full: the mean-value choice of `s∈[t/2,t]` with `ℰ(u_s,u_s) ≤ q(t)/t` (`exists_small_energy`), the inequality `q(s)² ≤ (2/κ)(ρ(M)^n/d_n)(q(2s)+K T_nℰ)` (`nash_step`), its consequence `q(t) ≲ ρ(M)^n/d_n` (`nash_chain`), the degree growth `d_n ≥ c ρ(N)^{n-k}` (`ratio_le_of_degree_growth`) and the final power `q(t) ≤ C t^{-d_box(1-1/d_deg)/d_walk}` (`finite_born_on_diagonal_upper`) |
| Theorem `diffusion-spectral` | `Section33.Main`, `Section3.SpectralDimension` | both cases: `spectral_dim_finite_born` (value `2d_box(1-1/d_deg)/d_walk`) and `spectral_dim_infinite_born` (value `2d_box/d_walk`, the logarithmic correction being immaterial) |
| Proposition `final_recurrent` | `Section33.Main` | `2d_box/d_walk < 2 ↔ d_R > 0`, via the Einstein relation (`spectral_lt_two_iff`) |
| Corollary 3.27 (heat kernel of the resistance-form Brownian motion) | `Section33.BrownianHeat` | under `dim_R > 0`, the identification `q_t = p_t` of Theorem 3.18 transfers both estimates of Theorem `diffusion-heat` to `q` (`brownian_heat_finite_born`, `brownian_heat_infinite_born`) |
| Theorem 3.28 (`dim_S^{(R)} = dim_S^{(N)}`) | `Section33.BrownianHeat` | the transfer of the limit itself (`tendsto_spectral_congr`, `brownian_spectral_eq_diffusion`), the two values `2d_box(1-1/d_deg)/d_walk` and `2d_box/d_walk` (`brownian_spectral_finite_born`, `brownian_spectral_infinite_born`) and the final Einstein-relation identity `2d_box/d_walk = 2(d_box/d_R)/(1+d_box/d_R)` (`spectral_infinite_eq_resistance_ratio`) |
| Remark 3.29 (the sign of `d_R`) | `Section33.BrownianHeat` | the algebraic part: `d_R > 0 ↔ ρ(Ψ) > 1 ↔ d_box < d_walk` (`dR_pos_iff_one_lt_rPsi`, `dbox_lt_dwalk_of_dR_pos`) |
| Example 3.30 (the two-coloured EIGS of Figure 3) | `Section33.TwoColourExample` | `ρ(M)=3+√6, ρ(N)=ρ_min(D)=2` and `ρ(Ψ)` the unique root of `27λ⁴+6λ³-50λ²+6λ+6` in `(1,∞)` (`exists_unique_rPsi`, with the enclosure `1.1061 < ρ(Ψ) < 1.1062`, `rPsi_mem_Ioo`); the two closed formulas `2log((3+√6)/2)/log((3+√6)ρ(Ψ))` and `2log(3+√6)/log((3+√6)ρ(Ψ))` (`twoColour_spectral_finite_eq`, `twoColour_spectral_infinite_eq`) and rigorous numerical enclosures `1.1159 < · < 1.1161`, `1.8876 < · < 1.8878` confirming the quoted `≈1.1160` and `≈1.8877` (`twoColour_spectral_finite`, `twoColour_spectral_infinite`) |
| the DHL example | `Section33.DHLExample` | `ρ(M)=4, ρ(N)=2, ρ(Ψ)=1, ρ_min(D)=2` give `d_box=d_deg=d_walk=2`, `d_R=0`, exponents `1/2` and `1`, logarithmic exponent `1/(d_deg-1)=1` against the Hambly–Kumagai `d_deg/(d_deg-1)=2` (`dhl_log_exponent`, `dhl_log_exponent_HK`, `dhl_log_exponent_lt_HK`), spectral dimensions `1` and `2` (`dhl_spectral_finite`, `dhl_spectral_infinite'`); and a check that the hypotheses of the volume lemma are satisfiable (`dhl_volume_nonvacuous`) |

## What is *not* proved (and is not claimed to be)

Exactly the inputs the paper quotes:

* the counting estimates of §2 (Lemmas 2.13, 2.14: numbers of `k`-born points and
  sizes of balls in `Ξ^n`), including the fact that their constants may be taken
  uniform over the finitely many birth types, the degree growth
  `d_n ≍ ρ(N)^{n-k}` and the discrete mean exit-time bound (Theorem 2.23);
* the strong Markov property used to split the resolvent at an exit time;
* Lemma `GHP_convergence` (mass of a level-`m` cell `≍ ρ(M)^{-m}`) and Theorem
  `sec31_ghps` (convergence of the Poissonised walks), together with the
  Skorokhod representation theorem used to couple them;
* Corollary `sec31_continuous_stay` (the survival estimate feeding
  Theorem `general-lower`);
* the multiscale Nash argument of Hambly–Kumagai giving ultracontractivity, and
  the Dirichlet-form theory producing a jointly continuous heat kernel;
* the Poincaré/eigenvalue estimate on a prototype cell and the mass of a harmonic
  profile, which are the two analytic inputs of the Nash step.

Each of these appears as a named hypothesis of the statements above, so the place
where it enters is visible.  Remarks on the statements themselves are collected
in `SECTION33_NOTES.md`.
-/
