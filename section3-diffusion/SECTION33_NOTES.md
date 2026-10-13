# Remarks on §3.3 of arXiv:2603.13798 arising from the formalisation

These are observations made while formalising §3.3 ("Heat kernel for the
diffusion limit").  None of them affects the conclusions of the subsection in the
regime the paper is interested in; they are places where a hypothesis is used
silently, or where the statement is slightly off from what the proof gives.

1. **The logarithmic exponent in Lemma `heat-volume`.**
   The proof chooses `L_m = ⌈(1+ε) log m / log(ρ(M)/ρ(N))⌉` and then uses
   `ρ(N)^{L_m} ≤ C_ε m^{1+1/(d_deg-1)+ε}`.  What the choice actually gives is
   `ρ(N)^{L_m} ≤ ρ(N)·m^{(1+ε)/(d_deg-1)}` (formalised as
   `Params.rN_pow_Lscale_le`).  The stated exponent is larger — hence the stated
   estimate is weaker and still correct — exactly when
   `ε ≤ (1+ε)(d_deg-1)`, in particular whenever `d_deg ≥ 2`
   (`Params.exponent_le_paper`).  For `d_deg` close to `1` the exponent written
   in the paper is *smaller* than the one the argument produces, so the sharp
   form should be preferred.  Either way the local spectral dimension is
   unchanged, since any fixed power of `|log t|` is invisible in the limit
   (`Section3.SpectralDimension`).

2. **`L_m ≤ m`.**  The set `E_{m,L}` is only defined for `L ≤ m`, and the
   geometric summation `Σ_{k=0}^{m-L}` presupposes it.  With
   `L_m ≍ log m` this holds for all large `m`, but it is worth saying: the
   Borel–Cantelli conclusion is about large `m` anyway.

3. **Scale-freeness is used throughout.**  `d_deg > 1`, i.e. `ρ(N) < ρ(M)`, is
   what makes the geometric sum in step 1 of Lemma `heat-volume` converge and
   what makes `L_m` well defined.  In the non-scale-free case (`ρ(N) = 1`,
   `d_deg = ∞`) the two cases of Theorem `diffusion-heat` coincide, and the
   argument has to be read with `L_m` removed.

4. **Lemma `heat-exit`.**  The Fatou step is applied to the *truncated* exit
   times `τ ∧ T`; the passage back to `E_y[τ]` is monotone convergence in `T`,
   and only then can `η ↓ 0` be taken.  Both limits are separate steps and are
   formalised as such (`mean_exit_le_of_truncated`).  Also, the `sup` over
   `y ∈ B(x,r)` costs the factor `2^{d_walk}` coming from the inclusion
   `B(x,r) ⊆ B(y,2r)`; the constant in the statement is therefore not the
   constant of the discrete estimate.

5. **The choice of `s` in Theorem `diffusion-heat`.**  "Choose `s ∈ [t/2,t]` so
   that `ℰ_W(u_s,u_s) ≤ q(t)/t`" is a mean-value argument: it uses
   `∫_{t/2}^{t} ℰ_W(u_s,u_s) ds = (q(t)-q(2t))/2 ≤ q(t)/2` together with
   integrability of `s ↦ ℰ_W(u_s,u_s)` on `[t/2,t]`.  Both are needed, and the
   formalisation makes them explicit hypotheses of `exists_small_energy`.

6. **The scale `n = n(t)`.**  Only the inequality `t < T_{n-1}` is used for the
   upper bound (`power_of_geometric`); `T_n ≤ t` is used in the Nash chain to
   dominate `T_n ℰ(u_s,u_s)` by `q(t)`.  Both halves of `T_n ≤ t < T_{n-1}` are
   therefore genuinely needed, at different places.

7. **Non-negativity of the on-diagonal values.**  In the passage from
   `p_x² ≤ μ(B) p_{2t}(x,x)` to a lower bound for `p_{2t}(x,x)` one uses that
   `μ(B) > 0`; the volume lower bound of Lemma `heat-volume` supplies this, and
   the formalisation keeps it as an explicit hypothesis.

8. **Proposition `final_recurrent`.**  The equivalence
   `2 d_box/d_walk < 2 ⟺ d_R > 0` uses the Einstein relation
   `d_walk = d_box + d_R` and `d_box > 0`; it is proved here
   (`Params.spectral_lt_two_iff`), the identification of `d_R > 0` with
   recurrence of the walk being the quoted Proposition of §2.

9. **`d_walk > 0` is a standing assumption of the whole subsection.**  It is
   equivalent to `ρ(M)ρ(Ψ) > 1`, and it is what makes the parabolic scales
   `T_n = (ρ(M)ρ(Ψ))^{-n}` decrease.  (§3.2, by contrast, needed the strictly
   stronger `d_R > 0`; §3.3 does not, which is why the DHL example with
   `d_R = 0` is admissible here.)

---

## Appendix: remarks on the revised §3.3 (heat-kernel lower bound)

The revised version of §3.3 changes three things, and the formalisation has been
updated accordingly.

**A. The logarithmic exponent is now the sharp one.**  Lemma `heat-volume` now
states the upper bound at a `μ`-almost every infinite-born point as

`μ(B(x,r)) ≤ C |log r|^{1/(d_deg-1)+ε} r^{d_box}`,

and Theorem `diffusion-heat` correspondingly carries `|log t|^{-1/(d_deg-1)-ε}`.
This agrees with what the argument produces, and it supersedes remark 1 above:
the earlier exponent `1 + 1/(d_deg-1) + ε` is no longer stated.  The two forms
are related by a calibration of the parameter in
`L_m = ⌈(1+ε)log m/log(ρ(M)/ρ(N))⌉`, namely `ε ↦ ε(d_deg-1)`
(`Params.calibrated_exponent`, `Params.rN_pow_Lscale_le_logExp`,
`Params.volume_upper_logExp`); the formalisation keeps both, since the proof
naturally yields `(1+ε)/(d_deg-1)`.  The discussion after the theorem, comparing
with the Hambly–Kumagai route, is the identity
`d_deg/(d_deg-1) = 1/(d_deg-1) + 1` (`Params.logExpHK_eq`), so the gain is
exactly one power of `|log t|` (`Params.logExp_lt_logExpHK`; for the DHL, `1`
against `2`).

**B. The proof of Lemma `heat-volume` now treats the birth level of the nearby
terminal explicitly.**  The new text fixes `c₁` so that the *uniform* finite-born
estimate applies to every ball of radius `Cρ_min(D)^{-m}` centred at a vertex of
birth level at most `m - c₁`, and then splits into `b_m + c₁ ≤ m` (use that
estimate at scale `m`) and `m < b_m + c₁` (use it at the birth scale, at the cost
of the constant `ρ(M)^{c₁}`).  Both branches end at `ρ(N)^{L_m}ρ(M)^{-m}`; this
is `Params.geom_bound_of_birth_dichotomy`, and the whole step, including the
inclusion `B(x,cρ_min(D)^{-m}) ⊆ B(v_m,(c+C_*)ρ_min(D)^{-m})` and the use of
`x ∉ E_{m,L_m}`, is `Params.volume_le_of_avoiding_skeleton`
(`RequestProject/Section33/BirthLevel.lean`).  Note that the second branch uses
`ρ(N)^{L} ≥ 1`, i.e. `ρ(N) > 1`, and that the uniformity of the constants over
the finitely many birth types is a hypothesis, as in the paper.

**C. Theorem `general-lower` is now stated at time `t`.**  The displayed
statement is `p_t(x,x) ≥ c_x/μ(B(x,C_x t^{1/d_walk}))`, while the Cauchy–Schwarz
step produces `p_{2t}(x,x) ≥ p_x²/μ(B(x,r))`.  The passage between the two is a
halving of the time variable, which changes the constant in the radius by the
factor `2^{-1/d_walk}` (`Params.halved_radius`) and, in the version with a
logarithmic correction, replaces `|log(t/2)|` by `|log t|` at the cost of a
factor `2^{θ}`.  The formalisation performs the halving explicitly
(`Params.on_diagonal_lower_ball`, `Params.heat_lower_finite_born`,
`Params.heat_lower_infinite_born`), so the statement proved is literally the one
displayed in the paper.  Two further details of that proof are now formalised:
the implication "`t ≤ a_x r^{d_walk}` ⟹ `P_x(W_t ∈ B(x,r)) ≥ p_x`", which is
monotonicity of the exit-time events (`prob_mem_of_exit_time`), and the fact that
the choice `r = (t/a_x)^{1/d_walk}` makes `t = a_x r^{d_walk}` an identity
(`Params.exit_radius_eq`).

**D. Two smaller additions.**

* The continuity half of Proposition `heat-kernel` (the resolvent maps `L^∞` to
  `C(Ξ_M)`) is now supported by `RequestProject/Section33/Resolvent.lean`: the
  error term of the strong Markov decomposition is bounded by
  `‖f‖_∞ E_y[τ] ≤ C‖f‖_∞ r^{d_walk}` (Lemma `heat-exit`), whence the oscillation
  of `U_λ f` exceeds that of the harmonic part by at most
  `2C‖f‖_∞ r^{d_walk}`.  The strong Markov property itself, and the continuity of
  the harmonic part (via `sec31_continuous_harmonics`), remain quoted inputs.
* Lemma `GHP_convergence` now *proves* `ρ(N) < ρ(M)` rather than assuming it: if
  `ρ(N) = ρ(M)` then `Σ_{k≤n} ρ(M)^kρ(N)^{n-k} = (n+1)ρ(M)^n`, which is not
  `O(ρ(M)^n)`.  This is `IGS.Sec31.rN_lt_rM_of_edge_bound` in
  `RequestProject/Section31/CellMass.lean`.  It matters here because `ρ(N) < ρ(M)`
  (i.e. `d_deg > 1`) is used throughout §3.3.

The renewal argument sketched at the end of the discussion — for the DHL,
infinitely many scales satisfy `μ(B(x,r)) ≥ c|log r|^{1-ε}r²` at a typical point,
so the exponent `1/(d_deg-1)` cannot be lowered — is explicitly not pursued in the
paper, and is not formalised here either.

## Appendix (later run): Corollary 3.27, Theorem 3.28 and Example 3.30

These three items close §3.3, and are formalised in
`RequestProject/Section33/BrownianHeat.lean` (3.27, 3.28, and the algebraic part
of Remark 3.29) and `RequestProject/Section33/TwoColourExample.lean` (3.30).

**1. What is actually quoted, and where.**  Both 3.27 and 3.28 rest on a single
external input, namely Theorem 3.18: under `dim_R(Ξ) > 0` the resistance-form
Brownian motion and the diffusion `W` are the same `L²(Ξ_M, μ)` process, hence
`q_t(x,y) = p_t(x,y)`.  In the formalisation this is the hypothesis

`hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t`,

deliberately stated *under* `dim_R > 0`, so the standing assumption of this part
of the section is genuinely used and cannot be silently dropped.  Everything
else is proved: the transfer of the two-sided bounds (`brownian_heat_*`), the
transfer of the limit defining the spectral dimension (`tendsto_spectral_congr`,
which is just `Tendsto.congr'` along `𝓝[>]0`, where `q = p` holds pointwise),
and the closing identity
`2 dim_B/dim_W = 2(dim_B/dim_R)/(1 + dim_B/dim_R)` from the Einstein relation
(`spectral_infinite_eq_resistance_ratio`).

**2. A small remark on 3.27.**  The corollary is stated in the paper for *every*
`x ∈ V` and for `μ`-a.e. `x ∈ V^∞`, with the constants of Theorem 3.23.  Since
`q_t = p_t` identically, the transfer is exact: the same constants
`c_x, C_x, t_0(x)` work, and the logarithmic exponent stays
`1/(dim_D-1)+ε`.  There is nothing to optimise, which is why the formalised
statements are literally "the bounds for `p` also hold for `q`".

**3. Example 3.30 and the Perron root.**  The example needs `ρ(Ψ)`, which
Example 2.12 describes twice: as `(t+2)(t+1)/(2t+3)` for the positive root `t` of
`3t⁴+10t³+4t²-8t-3`, and as the root in `(1,∞)` of
`27λ⁴+6λ³-50λ²+6λ+6`.  Both descriptions are formalised and shown to agree:
`psiPoly_of_tPoly` is the elimination identity

`(2t+3)⁴ psiPoly((t+2)(t+1)/(2t+3)) = tPoly(t)·(9t⁴+82t³+248t²+310t+138)`,

and `exists_unique_rPsi` proves that `psiPoly` has exactly one root in `(1,∞)`
(strict monotonicity on `[1,∞)` plus the intermediate value theorem), with the
enclosure `1.1061 < ρ(Ψ) < 1.1062` (`rPsi_mem_Ioo`).  Note that the paper's
rounded value `1.1061` is the *lower* end of that interval: the root is
`1.10612801…`, so `≈ 1.1061` is correct but `ρ(Ψ) > 1.1061`.

**4. The numerics of Example 3.30 are proved, not computed.**  The two values
`≈ 1.1160` and `≈ 1.8877` are certified by the enclosures

`1.1159 < 2 log((3+√6)/2)/log((3+√6)ρ(Ψ)) < 1.1161`,
`1.8876 < 2 log(3+√6)/log((3+√6)ρ(Ψ)) < 1.8878`,

obtained from `Real.exp_one_gt_d9`/`Real.exp_one_lt_d9`,
`Real.log_two_gt_d9`/`Real.log_two_lt_d9` and the elementary inequalities
`1 - 1/x ≤ log x ≤ x - 1` only.  Two tricks make the elementary bounds sharp
enough: `log((3+√6)/2)` is estimated through `log a ≤ a/e` and `log a ≥ 2 - e/a`
(the argument is within `0.24 %` of `e`), and `log ρ(Ψ)` through
`log ρ(Ψ) = (log 2 + log(ρ(Ψ)⁷/2))/7`, the seventh power bringing the argument
within `1.3 %` of `1`.

**5. Why `dim_R > 0` is not a restriction here.**  `dim_R > 0` is equivalent to
`ρ(Ψ) > 1` (`dR_pos_iff_one_lt_rPsi`) and implies `dim_B < dim_W`.  The
two-coloured EIGS of Figure 3 has `ρ(Ψ) ≈ 1.1061 > 1`, so it is in the Brownian
regime and 3.27/3.28 do apply to it (`twoColour_dR_pos`); the DHL, with
`ρ(Ψ) = 1`, is not, which is exactly the trichotomy of Remark 3.29.
