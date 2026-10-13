import Mathlib
import RequestProject.Section2
import RequestProject.Section2Network

/-!
# Completing the formalisation of Section 2.1 of arXiv:2603.13798
  *Iterated Graph Systems (I): random walks and diffusion limits*

`Section2.lean` and `Section2Network.lean` already formalise:
* **Definition 2.1** (the resistance renormalisation map `Ψ`, both abstractly and
  via genuine finite electrical networks);
* **Lemma 2.3** (monotonicity, homogeneity, concavity, superadditivity, and the
  extension part of continuity);
* **Corollary 2.7** (`RenormMap.iterate_one_two_sided`, two-sided growth of the
  iterates `Ψ^[ℓ] 1`);
* the **eigenvalue-uniqueness** half of **Lemma 2.6** (`RenormMap.eigenvalue_unique`).

This file completes the remaining numbered items of Section 2.1:

* **Lemma 2.4** (`renorm_iterate_of_recurrence`): the algebraic core, that a sequence
  satisfying `y₀ = x`, `yₙ₊₁ = Ψ(yₙ)` is exactly `yₙ = Ψ^[n] x`.  (The geometric
  reduction producing this recurrence from the substitution structure `Ξⁿ` belongs
  to Section 1's combinatorial framework and is recorded in the docstring.)
* **Lemma 2.6** (`lemma_2_6`): the *eigenvalue* existence-and-uniqueness statement,
  conditional on existence of one positive eigenpair — the Nussbaum–Perron–Frobenius
  input of [21] — which is taken as a hypothesis exactly as the paper cites it.
* **Corollary 2.8** (`RenormMap.iterate_normalised_limit`): convergence of
  `Ψⁿ(1)/ρ(Ψ)ⁿ` to a positive multiple of the eigenvector, conditional on the
  geometric convergence of the normalised iterates (the Hilbert-projective-metric
  contraction of [21, Thm 4.2]) taken as a hypothesis.
* **Lemma 2.9** (`RenormMap.single_edge_resistance_growth`): a direct specialisation
  of Corollary 2.7 to a single coordinate (one-edge `Ξ⁰`).
* **Definition 2.10 / Theorem 2.11** (`resistanceDimension`, `resistance_dimension_eq`):
  the resistance dimension as a limit, and its closed form `log ρ(Ψ)/log ρ_min(𝒟)`,
  built on the general analytic limit `resistance_dimension_limit`.
* **Example 2.2 / Example 2.12** (`example22Psi`, `example212_eigen_iff_quartic`,
  `example212_unique_positive_root`, `example212_unique_eigenvalue_root`): the explicit
  two-colour renormalisation map of Figure 3, its degree-1 homogeneity, and the
  Perron-eigenpair polynomial computations.
-/

namespace EIGS

open scoped BigOperators
open Filter Topology

/-! ### Lemma 2.4 (renormalisation map): the algebraic iterate identity

In the paper, a geometric/combinatorial argument over the substitution networks
`Ξⁿ` shows that `𝐲ₙ(𝐱)` defined by the effective resistances of the substituted
copies satisfies `𝐲₀ = 𝐱` and `𝐲ₙ₊₁ = Ψ(𝐲ₙ)`, and concludes `𝐲ₙ = Ψⁿ(𝐱)`.  The
combinatorial reduction (decomposing `Ξⁿ` into edge-disjoint copies `H_e^{(n)}`)
belongs to Section 1's substitution framework; the purely algebraic conclusion of
Lemma 2.4 — that a sequence with this recurrence is the iterate of `Ψ` — is the
content formalised here. -/

theorem renorm_iterate_of_recurrence {K : ℕ} (Ψ : RenormMap K)
    {y : ℕ → (Fin K → ℝ)} {x : Fin K → ℝ}
    (h0 : y 0 = x) (hrec : ∀ n, y (n + 1) = Ψ.apply (y n)) (n : ℕ) :
    y n = Ψ.apply^[n] x := by
  induction n <;> simp +decide [ *, Function.iterate_succ_apply' ]

/-
A positive sequence with multiplicative increments `seq (n+1) = seq n * f n`,
where the factors `f n > 0` approach `1` geometrically (`|f n - 1| ≤ C ηⁿ` with
`0 ≤ η < 1`), converges to a positive limit.  This is the analytic core behind the
convergence of `Ψⁿ(1)/ρⁿ` in Corollary 2.8.
-/
theorem geometric_ratio_product_converges
    {seq f : ℕ → ℝ} {b₀ C η : ℝ}
    (hb₀ : 0 < b₀) (hseq0 : seq 0 = b₀)
    (hf_pos : ∀ n, 0 < f n)
    (hrec : ∀ n, seq (n + 1) = seq n * f n)
    (hC : 0 ≤ C) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hbound : ∀ n, |f n - 1| ≤ C * η ^ n) :
    ∃ L : ℝ, 0 < L ∧ Tendsto seq atTop (nhds L) := by
  -- Taking logarithms, we define $g k := \log(f k)$.
  set g : ℕ → ℝ := fun k => Real.log (f k);
  -- Then $\log(\text{seq } n) = \log(b₀) + \sum_{k=0}^{n-1} g k$.
  have h_log_seq : ∀ n, Real.log (seq n) = Real.log b₀ + ∑ k ∈ Finset.range n, g k := by
    intro n; induction n <;> simp_all +decide [ Finset.sum_range_succ, mul_div_cancel₀ ] ;
    rw [ Real.log_mul ( ne_of_gt <| by rename_i n ih; exact Nat.recOn n ( by linarith ) fun n ihn => by rw [ hrec ] ; exact mul_pos ihn ( hf_pos _ ) ) ( ne_of_gt <| hf_pos _ ), ← add_assoc, ‹Real.log ( seq _ ) = Real.log b₀ + _› ];
  -- We need to show that the series $\sum_{k=0}^{\infty} g k$ converges.
  have h_summable : Summable g := by
    -- We bound $|g k|$ by $2Cη^k$ for large enough $k$.
    have h_bound_g : ∃ N, ∀ k ≥ N, |g k| ≤ 2 * C * η ^ k := by
      -- Since $|f k - 1| \leq C * η^k$ and $η < 1$, for large enough $k$, $C * η^k$ will be less than $1/2$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, C * η ^ k < 1 / 2 := by
        simpa using ( summable_geometric_of_lt_one hη0 hη1 ) |> fun h => h.mul_left C |> fun h => h.tendsto_atTop_zero.eventually ( gt_mem_nhds <| by norm_num );
      use N; intro k hk; specialize hN k hk; specialize hbound k; norm_num [ abs_le ] at *;
      constructor <;> nlinarith [ Real.log_le_sub_one_of_pos ( hf_pos k ), Real.log_inv ( f k ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( hf_pos k ) ), mul_inv_cancel₀ ( ne_of_gt ( hf_pos k ) ) ];
    obtain ⟨ N, hN ⟩ := h_bound_g;
    rw [ ← summable_nat_add_iff N ];
    exact Summable.of_norm <| Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => hN _ <| Nat.le_add_left _ _ ) <| Summable.mul_left _ <| summable_geometric_of_lt_one hη0 hη1 |> Summable.comp_injective <| add_left_injective N;
  -- Let $S := \sum_{k=0}^{\infty} g k$.
  obtain ⟨S, hS⟩ : ∃ S, Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, g k) Filter.atTop (nhds S) := by
    exact ⟨ _, h_summable.hasSum.tendsto_sum_nat ⟩;
  -- Set $L := \exp(\log(b₀) + S)$.
  use Real.exp (Real.log b₀ + S);
  exact ⟨ Real.exp_pos _, by rw [ show seq = fun n => Real.exp ( Real.log ( seq n ) ) by ext n; rw [ Real.exp_log ( show 0 < seq n from Nat.recOn n ( by linarith ) fun n ihn => by rw [ hrec ] ; exact mul_pos ihn ( hf_pos n ) ) ] ] ; simpa only [ h_log_seq ] using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) ( tendsto_const_nhds.add hS ) ⟩

namespace RenormMap

variable {K : ℕ} (Ψ : RenormMap K)

/-! ### Lemma 2.6 (eigenvalue existence and uniqueness)

The paper proves that the renormalisation map `Ψ` of a distance-positive EIGS is
homogeneous of degree one, superadditive, power-bounded below, and
Nussbaum-irreducible, and then invokes Theorem 4.1 of [21] (a Nussbaum–
Perron–Frobenius theorem) to get a unique positive eigenvalue `ρ(Ψ) > 0` and a
unique-up-to-scalar positive eigenvector.

Existence of a positive eigenpair genuinely needs the deep input of [21]; we take
it as the hypothesis `hex`, exactly as the paper cites [21].  Given existence, the
*eigenvalue* is unique and positive — that half is proved here from monotonicity
and homogeneity alone (via `RenormMap.eigenvalue_unique`). -/

theorem lemma_2_6 (hK : 0 < K)
    (hex : ∃ (v : Fin K → ℝ) (ρ : ℝ), (∀ i, 0 < v i) ∧ 0 < ρ ∧ Ψ.apply v = ρ • v) :
    ∃! ρ : ℝ, 0 < ρ ∧ ∃ v : Fin K → ℝ, (∀ i, 0 < v i) ∧ Ψ.apply v = ρ • v := by
  obtain ⟨v, ρ, hv, hρ, h⟩ := hex
  refine ⟨ρ, ⟨hρ, v, hv, h⟩, ?_⟩
  rintro y ⟨hy, w, hw, hwy⟩
  exact (eigenvalue_unique Ψ hK hw hv hy hρ hwy h)

/-! ### Lemma 2.9 (resistance growth for a single edge)

With `Ξ⁰` a single edge of colour `ι`, one has
`ℛ_{Ξⁿ}(𝔳₊,𝔳₋) = [Ψⁿ(1)]_ι` (Lemma 2.4 specialised to the single-edge functional),
so the two-sided growth is exactly Corollary 2.7 read off in coordinate `ι`. -/

theorem single_edge_resistance_growth {v : Fin K → ℝ} {ρ : ℝ}
    (hvpos : ∀ i, 0 < v i) (hρpos : 0 < ρ) (heig : Ψ.apply v = ρ • v) (ι : Fin K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      c * ρ ^ n ≤ (Ψ.apply^[n] (fun _ => 1)) ι ∧
        (Ψ.apply^[n] (fun _ => 1)) ι ≤ C * ρ ^ n := by
  have := @RenormMap.iterate_one_two_sided;
  exact this Ψ hvpos hρpos heig |> fun ⟨ c, C, hc, hC, h ⟩ => ⟨ c, C, hc, hC, fun n => h n ι ⟩

/-! ### Corollary 2.8 (normalised iterates converge to the eigenvector)

`xₙ := Ψⁿ(1)/‖Ψⁿ(1)‖₁` converges geometrically to the normalised eigenvector `v`
in Hilbert's projective metric (Theorem 4.2 of [21]); on the compact positive set
where the `xₙ` live this metric is equivalent to the Euclidean norm, giving
`‖xₙ - v‖₁ ≤ C ηⁿ`.  We take this geometric convergence as the hypothesis `hconv`
(the [21] input).  From it, together with continuity of `𝐱 ↦ ‖Ψ(𝐱)‖₁` near `v`
(`hLip`, the part of Lemma 2.3(3) needing the finite linear system), the paper
concludes `Ψⁿ(1)/ρⁿ → c* v` for some `c* > 0`. -/

theorem iterate_normalised_limit {v : Fin K → ℝ} {ρ : ℝ}
    (hvpos : ∀ i, 0 < v i) (hρpos : 0 < ρ) (heig : Ψ.apply v = ρ • v)
    (hnorm : ∑ i, v i = 1)
    (hconv : ∃ (C η : ℝ), 0 < C ∧ 0 ≤ η ∧ η < 1 ∧ ∀ n : ℕ,
      ‖(fun i => (Ψ.apply^[n] (fun _ => 1)) i / ∑ j, (Ψ.apply^[n] (fun _ => 1)) j)
        - v‖ ≤ C * η ^ n)
    (hLip : ∃ L : ℝ, ∀ n : ℕ,
      |(∑ i, (Ψ.apply (fun i => (Ψ.apply^[n] (fun _ => 1)) i
              / ∑ j, (Ψ.apply^[n] (fun _ => 1)) j)) i) - ρ|
        ≤ L * ‖(fun i => (Ψ.apply^[n] (fun _ => 1)) i
              / ∑ j, (Ψ.apply^[n] (fun _ => 1)) j) - v‖) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n => (fun i => (Ψ.apply^[n] (fun _ => 1)) i / ρ ^ n)) atTop
        (nhds (c • v)) := by
  obtain ⟨C, η, hC_pos, hη_nonneg, hη_lt_one, hconv_bound⟩ := hconv
  obtain ⟨L, hLip_bound⟩ := hLip
  set s : ℕ → ℝ := fun n => ∑ j, Ψ.apply^[n] (fun _ => 1) j
  set x : ℕ → (Fin K → ℝ) := fun n => fun i => Ψ.apply^[n] (fun _ => 1) i / s n
  set b : ℕ → ℝ := fun n => s n / ρ^n
  set r : ℕ → ℝ := fun n => ∑ j, Ψ.apply (x n) j
  set f : ℕ → ℝ := fun n => r n / ρ;
  -- By definition of $b$, we know that $b_{n+1} = b_n * f_n$.
  have hb_recurrence : ∀ n, b (n + 1) = b n * f n := by
    intro n
    simp [b, f, r, s];
    erw [ Function.iterate_succ_apply' ];
    have h_sum : ∑ j, Ψ.apply (s n • x n) j = s n * ∑ j, Ψ.apply (x n) j := by
      rw [ Finset.mul_sum _ _ _ ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ Ψ.apply_smul _ ( show 0 ≤ s n from Finset.sum_nonneg fun _ _ => by
                                                                      induction' n with n ih <;> simp_all +decide [ Function.iterate_succ_apply' ];
                                                                      exact Ψ.apply_nonneg ( show 0 ≤ Ψ.apply^[n] ( fun _ => 1 ) from Nat.recOn n ( fun _ => by norm_num ) fun n ihn => by rw [ Function.iterate_succ_apply' ] ; exact Ψ.apply_nonneg ihn ) _ ) ] ; rfl;
    convert congr_arg ( fun x : ℝ => x / ρ ^ ( n + 1 ) ) h_sum using 1 <;> ring;
    rw [ show s n • x n = Ψ.apply^[n] ( fun _ => 1 ) from funext fun i => by rw [ Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ ( ne_of_gt <| Finset.sum_pos ( fun _ _ => by
          have := Ψ.iterate_one_two_sided hvpos hρpos heig;
          exact lt_of_lt_of_le ( mul_pos this.choose_spec.choose_spec.1 ( pow_pos hρpos _ ) ) ( this.choose_spec.choose_spec.2.2 _ _ |>.1 ) ) ⟨ i, Finset.mem_univ _ ⟩ ) ] ] ; ring;
  -- By definition of $f$, we know that $|f_n - 1| \leq C' \eta^n$ for some $C' > 0$.
  obtain ⟨C', hC'_pos, hC'_bound⟩ : ∃ C' > 0, ∀ n, |f n - 1| ≤ C' * η^n := by
    use ( Max.max L 1 * C ) / ρ, div_pos ( mul_pos ( lt_max_of_lt_right zero_lt_one ) hC_pos ) hρpos, fun n => ?_;
    rw [ div_sub_one, abs_div ] <;> try positivity;
    rw [ abs_of_pos hρpos, div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
    exact mul_le_mul_of_nonneg_right ( le_trans ( hLip_bound n ) ( by nlinarith [ hconv_bound n, le_max_left L 1, le_max_right L 1, show 0 ≤ ‖ ( fun i => Ψ.apply^[n] ( fun x => 1 ) i / ∑ j, Ψ.apply^[n] ( fun x => 1 ) j ) - v‖ from norm_nonneg _ ] ) ) hρpos.le;
  -- By definition of $b$, we know that $b_n$ converges to some limit $L₀ > 0$.
  obtain ⟨L₀, hL₀_pos, hL₀⟩ : ∃ L₀ > 0, Filter.Tendsto b Filter.atTop (nhds L₀) := by
    have hb_pos : ∀ n, 0 < b n := by
      intro n
      have h_pos : ∀ i, 0 < Ψ.apply^[n] (fun _ => 1) i := by
        have := Ψ.single_edge_resistance_growth hvpos hρpos heig;
        exact fun i => by obtain ⟨ c, C, hc, hC, h ⟩ := this i; exact lt_of_lt_of_le ( mul_pos hc ( pow_pos hρpos _ ) ) ( h n |>.1 ) ;
      exact div_pos ( Finset.sum_pos ( fun _ _ => h_pos _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ) ( pow_pos hρpos _ );
    convert geometric_ratio_product_converges ( hb_pos 0 ) ( show b 0 = b 0 from rfl ) ( fun n => show 0 < f n from div_pos ( show 0 < r n from ?_ ) hρpos ) ( fun n => hb_recurrence n ) ( show 0 ≤ C' by positivity ) ( show 0 ≤ η by positivity ) hη_lt_one hC'_bound using 1;
    have := hb_recurrence n;
    exact lt_of_not_ge fun h => by nlinarith [ hb_pos n, hb_pos ( n + 1 ), show 0 < b n from hb_pos n, show 0 < b ( n + 1 ) from hb_pos ( n + 1 ), div_nonpos_of_nonpos_of_nonneg h hρpos.le ] ;
  -- By definition of $x$, we know that $x_n$ converges to $v$.
  have hx_converges : Filter.Tendsto x Filter.atTop (nhds v) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => norm_nonneg _ ) hconv_bound <| by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hη_nonneg hη_lt_one ) ;
  use L₀;
  refine' ⟨ hL₀_pos, _ ⟩;
  rw [ tendsto_pi_nhds ] at *;
  intro i; specialize hx_converges i; convert hL₀.mul hx_converges using 2 ; ring;
  rw [ div_mul_div_comm, div_eq_mul_inv ] ; ring;
  rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt <| Finset.sum_pos ( fun _ _ => by
    have := Ψ.iterate_one_two_sided hvpos hρpos heig; obtain ⟨ c, C, hc, hC, h ⟩ := this; exact h _ _ |>.1.trans_lt' ( mul_pos hc ( pow_pos hρpos _ ) ) ; ) ⟨ i, Finset.mem_univ i ⟩ ), mul_one ]

end RenormMap

/-! ### Definition 2.10 / Theorem 2.11 (resistance dimension)

The resistance dimension is the limit `lim_n log ℛ_{Gⁿ}(u,v) / log d_{Gⁿ}(u,v)`.
The analytic heart of Theorem 2.11 is the following limit: if both the resistance
sequence `R n` and the distance sequence `D n` grow geometrically with bases
`ρ, σ > 1` (up to multiplicative constants), the ratio of their logarithms tends to
`log ρ / log σ`. -/

theorem resistance_dimension_limit
    {R D : ℕ → ℝ} {ρ σ c₁ c₂ c₃ c₄ : ℝ}
    (hρ : 1 < ρ) (hσ : 1 < σ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hR : ∀ n, c₁ * ρ ^ n ≤ R n ∧ R n ≤ c₂ * ρ ^ n)
    (hD : ∀ n, c₃ * σ ^ n ≤ D n ∧ D n ≤ c₄ * σ ^ n) :
    Tendsto (fun n => Real.log (R n) / Real.log (D n)) atTop
      (nhds (Real.log ρ / Real.log σ)) := by
  -- By dividing both the numerator and the denominator by $n$, we can simplify the expression.
  suffices h_simplified : Filter.Tendsto (fun n => (Real.log (R n) / n) / (Real.log (D n) / n)) Filter.atTop (nhds ((Real.log ρ) / (Real.log σ))) by
    refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_div_div_cancel_right₀ ( by positivity ) ] );
  -- We'll use the fact that $\log(R_n) / n$ and $\log(D_n) / n$ converge to $\log(\rho)$ and $\log(\sigma)$ respectively.
  have h_log_div_n : Filter.Tendsto (fun n => Real.log (R n) / n) Filter.atTop (nhds (Real.log ρ)) ∧ Filter.Tendsto (fun n => Real.log (D n) / n) Filter.atTop (nhds (Real.log σ)) := by
    constructor;
    · have hR_log : ∀ n : ℕ, n > 0 → Real.log c₁ + n * Real.log ρ ≤ Real.log (R n) ∧ Real.log (R n) ≤ Real.log c₂ + n * Real.log ρ := by
        intro n hn; exact ⟨ by simpa [ Real.log_mul ( ne_of_gt hc₁ ) ( ne_of_gt ( pow_pos ( zero_lt_one.trans hρ ) _ ) ), Real.log_pow ] using Real.log_le_log ( by positivity ) ( hR n |>.1 ), by simpa [ Real.log_mul ( ne_of_gt hc₂ ) ( ne_of_gt ( pow_pos ( zero_lt_one.trans hρ ) _ ) ), Real.log_pow ] using Real.log_le_log ( by exact lt_of_lt_of_le ( by positivity ) ( hR n |>.1 ) ) ( hR n |>.2 ) ⟩ ;
      rw [ Metric.tendsto_nhds ];
      intro ε hε; refine' Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹ * ( |Real.log c₁| + |Real.log c₂| ) ⌉₊ + 1, fun n hn => abs_lt.mpr ⟨ _, _ ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( |Real.log c₁| + |Real.log c₂| ) ), mul_inv_cancel₀ ( ne_of_gt hε ), abs_le.mp ( show |Real.log c₁| ≤ |Real.log c₁| + |Real.log c₂| by linarith [ abs_nonneg ( Real.log c₁ ), abs_nonneg ( Real.log c₂ ) ] ), abs_le.mp ( show |Real.log c₂| ≤ |Real.log c₁| + |Real.log c₂| by linarith [ abs_nonneg ( Real.log c₁ ), abs_nonneg ( Real.log c₂ ) ] ), show ( n : ℝ ) ≥ ⌈ε⁻¹ * ( |Real.log c₁| + |Real.log c₂| ) ⌉₊ + 1 by exact_mod_cast hn, hR_log n ( by linarith ), mul_div_cancel₀ ( Real.log ( R n ) ) ( show ( n : ℝ ) ≠ 0 by norm_cast; linarith ) ] ;
    · -- By the properties of logarithms and the bounds on $D_n$, we can show that $\frac{\log(D_n)}{n}$ is squeezed between two sequences that both converge to $\log(\sigma)$.
      have h_squeeze : ∀ n : ℕ, n > 0 → (Real.log c₃ + n * Real.log σ) / n ≤ Real.log (D n) / n ∧ Real.log (D n) / n ≤ (Real.log c₄ + n * Real.log σ) / n := by
        intro n hn; constructor <;> gcongr;
        · rw [ ← Real.log_pow, ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( hD n |>.1 );
        · rw [ ← Real.log_pow, ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by nlinarith [ hD n, pow_pos ( zero_lt_one.trans hσ ) n ] ) ( by nlinarith [ hD n, pow_pos ( zero_lt_one.trans hσ ) n ] );
      -- As $n$ tends to infinity, the terms $\frac{\log c₃}{n}$ and $\frac{\log c₄}{n}$ tend to $0$.
      have h_zero : Filter.Tendsto (fun n : ℕ => Real.log c₃ / (n : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => Real.log c₄ / (n : ℝ)) Filter.atTop (nhds 0) := by
        exact ⟨ tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop, tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ⟩;
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' ( by simpa using h_zero.1.add_const ( Real.log σ ) ) ( by simpa using h_zero.2.add_const ( Real.log σ ) ) _ _;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by simpa [ add_div, hn.ne' ] using h_squeeze n hn |>.1;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by simpa [ add_div, hn.ne' ] using h_squeeze n hn |>.2;
  exact h_log_div_n.1.div h_log_div_n.2 ( ne_of_gt ( Real.log_pos hσ ) )

/-- **Definition 2.10 (resistance dimension).**  When the limit exists, the
resistance dimension of the combinatorial limit is
`lim_n log ℛ_{Gⁿ}(u,v) / log d_{Gⁿ}(u,v)`. -/
noncomputable def resistanceDimension (R D : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun n => Real.log (R n) / Real.log (D n))

/-
**Theorem 2.11 (resistance dimension of an EIGS).**  Combining the geometric
resistance growth (Corollary 2.7, base `ρ = ρ(Ψ)`) with the geometric distance
growth (base `ρ_min = ρ_min(𝒟)`, Theorem 3.3 of [38], taken as the hypothesis
`hD`), the resistance dimension equals `log ρ(Ψ) / log ρ_min(𝒟)`.
-/
theorem resistance_dimension_eq
    {R D : ℕ → ℝ} {ρ ρmin : ℝ}
    (hρ : 1 < ρ) (hρmin : 1 < ρmin)
    (hR : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * ρ ^ n ≤ R n ∧ R n ≤ c₂ * ρ ^ n)
    (hD : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * ρmin ^ n ≤ D n ∧ D n ≤ c₄ * ρmin ^ n) :
    resistanceDimension R D = Real.log ρ / Real.log ρmin := by
  -- Apply `resistance_dimension_limit` to obtain the limit of the ratio of logarithms.
  obtain ⟨c₁, c₂, hc₁, hc₂, hR⟩ := hR
  obtain ⟨c₃, c₄, hc₃, hc₄, hD⟩ := hD
  have h_limit : Filter.Tendsto (fun n => Real.log (R n) / Real.log (D n)) Filter.atTop (nhds (Real.log ρ / Real.log ρmin)) := by
    convert resistance_dimension_limit ?_ ?_ ?_ ?_ ?_ ?_ hR hD using 1 <;> ( first | positivity | aesop ) ;
  exact h_limit.limUnder_eq

/-! ### Example 2.2 and Example 2.12 (the two-colour EIGS of Figure 3)

The explicit resistance renormalisation map of the two-colour EIGS in Figure 3
(`example22Psi`) and the polynomial computation of its Perron eigenpair. -/

/-- **Example 2.2.**  The explicit resistance renormalisation map `Ψ` of the
two-colour EIGS of Figure 3 (colour `0` = red, colour `1` = blue):
`Ψ(x₀,x₁) = ((x₀²+4x₀x₁+x₁²)/(3(x₀+x₁)), (x₀+2x₁)(x₀+x₁)/(2x₀+3x₁))`. -/
noncomputable def example22Psi (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ (x 0 ^ 2 + 4 * x 0 * x 1 + x 1 ^ 2) / (3 * (x 0 + x 1)),
     (x 0 + 2 * x 1) * (x 0 + x 1) / (2 * x 0 + 3 * x 1) ]

/-
The explicit map of Example 2.2 is homogeneous of degree one (Lemma 2.3(2)).
With Lean's `a / 0 = 0` convention the identity holds for every scalar `t` and
every `x` (the positivity hypotheses of the paper turn out to be unnecessary for
the explicit rational formula).
-/
theorem example22Psi_homogeneous (t : ℝ) (x : Fin 2 → ℝ) :
    example22Psi (t • x) = t • example22Psi x := by
  ext i
  fin_cases i <;> simp +decide [ example22Psi ] <;> ring_nf <;> grind

/-
**Example 2.12 (eigen-relation ⟺ quartic).**  For `t > 0`, the vector `(t,1)`
is an eigenvector of the Example-2.2 map with eigenvalue `(t+2)(t+1)/(2t+3)` iff `t`
is a root of `3t⁴+10t³+4t²-8t-3`.
-/
theorem example212_eigen_iff_quartic {t : ℝ} (ht : 0 < t) :
    example22Psi ![t, 1] = ((t + 2) * (t + 1) / (2 * t + 3)) • ![t, 1]
      ↔ 3 * t ^ 4 + 10 * t ^ 3 + 4 * t ^ 2 - 8 * t - 3 = 0 := by
  constructor;
  · intro h; have h₁ := congr_fun h 0; have h₂ := congr_fun h 1; norm_num [ example22Psi ] at h₁ h₂;
    rw [ div_mul_eq_mul_div, div_eq_div_iff ] at h₁ <;> nlinarith;
  · intro h
    unfold example22Psi
    simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.cons_val_zero,
      Matrix.cons_val_one, funext_iff, Fin.forall_fin_two]
    refine ⟨?_, by ring⟩
    rw [ div_mul_eq_mul_div, div_eq_div_iff ] <;> nlinarith

/-
**Example 2.12 (unique positive eigenvector).**  The eigenvector equation has a
unique positive solution `t`: the polynomial `3t⁴+10t³+4t²-8t-3` has a unique
positive root.
-/
theorem example212_unique_positive_root :
    ∃! t : ℝ, 0 < t ∧ 3 * t ^ 4 + 10 * t ^ 3 + 4 * t ^ 2 - 8 * t - 3 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 < t ∧ 3 * t ^ 4 + 10 * t ^ 3 + 4 * t ^ 2 - 8 * t - 3 = 0 := by
    -- By the Intermediate Value Theorem, since $f(0) < 0$ and $f(1) > 0$, there exists $t \in (0, 1)$ such that $f(t) = 0$.
    have h_ivt : ∃ t ∈ Set.Ioo (0 : ℝ) 1, 3 * t ^ 4 + 10 * t ^ 3 + 4 * t ^ 2 - 8 * t - 3 = 0 := by
      apply_rules [ intermediate_value_Ioo ] <;> norm_num;
      fun_prop;
    aesop;
  refine' ⟨ t, ht, fun x hx => _ ⟩;
  by_contra h_neq;
  -- Without loss of generality, assume $t < x$.
  wlog h_wlog : t < x generalizing t x;
  · exact this x hx t ht ( Ne.symm h_neq ) ( lt_of_le_of_ne ( le_of_not_gt h_wlog ) h_neq );
  · nlinarith [ mul_pos ht.1 ( sub_pos.2 h_wlog ), mul_pos ht.1 ( sq_pos_of_pos ( sub_pos.2 h_wlog ) ), mul_pos hx.1 ( sub_pos.2 h_wlog ), mul_pos hx.1 ( sq_pos_of_pos ( sub_pos.2 h_wlog ) ) ]

/-
**Example 2.12 (unique eigenvalue).**  The eigenvalue `ρ(Ψ)` is the unique root
in `(1,∞)` of `27λ⁴+6λ³-50λ²+6λ+6`.
-/
theorem example212_unique_eigenvalue_root :
    ∃! l : ℝ, 1 < l ∧ 27 * l ^ 4 + 6 * l ^ 3 - 50 * l ^ 2 + 6 * l + 6 = 0 := by
  obtain ⟨l, hl⟩ : ∃ l : ℝ, 1 < l ∧ 27 * l ^ 4 + 6 * l ^ 3 - 50 * l ^ 2 + 6 * l + 6 = 0 := by
    -- By the Intermediate Value Theorem, since $g(1) < 0$ and $g(2) > 0$, there exists some $l \in (1, 2)$ such that $g(l) = 0$.
    have h_ivt : ∃ l ∈ Set.Ioo 1 2, (fun l : ℝ => 27 * l ^ 4 + 6 * l ^ 3 - 50 * l ^ 2 + 6 * l + 6) l = 0 := by
      apply_rules [ intermediate_value_Ioo ] <;> norm_num;
      fun_prop;
    grind;
  refine' ⟨ l, hl, _ ⟩;
  intros y hy; nlinarith [ mul_le_mul_of_nonneg_left hy.1.le ( sq_nonneg ( y - l ) ), mul_le_mul_of_nonneg_left hl.1.le ( sq_nonneg ( y - l ) ) ] ;

end EIGS