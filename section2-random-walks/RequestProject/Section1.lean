import Mathlib
import RequestProject.Section2
import RequestProject.Section2Network
import RequestProject.Section21
import RequestProject.Section22

/-!
# Formalisation of Section 1 of arXiv:2603.13798
  *Iterated Graph Systems (I): random walks and diffusion limits*

This file formalises the combinatorial backbone of **Section 1** of the paper —
the precise definition of an **Edge Iterated Graph System (EIGS)** (Definition 1.1),
its growth matrices (`mass matrix M`, `degree matrix N`), and the **geometric
growth** of the substitution networks `Ξⁿ`.  It also packages the *exit-time* and
*walk-dimension* consequences (combining the now-proven mass growth with the
resistance growth of Section 2.1 and the cited distance growth) by discharging the
geometric hypotheses that `Section22.lean` had taken as inputs.

## What is built concretely and proved

* **Definition 1.1.**  `ColGraph` (a finite edge-coloured directed multigraph),
  `EIGSData` (an EIGS: a single-edge initial graph of colour `ι`, a family of rule
  graphs `R_i` with two distinct planting vertices `β_i^±`).  By Assumption 1.2(3)
  the initial graph is a single directed edge, which we build in directly.
* **The substitution networks `Ξⁿ` at the level of edges and colours.**  An edge of
  `Ξⁿ⁺¹` is a pair `(e, e')` with `e ∈ E(Ξⁿ)` and `e' ∈ E(R_{𝒞(e)})`; its colour is
  `𝒞_{R}(e')`.  This is exactly the edge-substitution rule of Definition 1.1, and it
  determines the colour-count vector `χ(Ξⁿ)` (the only datum the mass matrix sees).
* **Mass matrix `M`** (`massMatrix`) and the **mass recursion**
  `χ(Ξⁿ⁺¹) = χ(Ξⁿ) · M`, hence `χ(Ξⁿ) = χ(Ξ⁰) · Mⁿ` (`chiCount_vecMul_pow`).
* **Geometric mass growth** `|E(Ξⁿ)| ≍ ρ(M)ⁿ` (`mass_geometric_growth`), proved from
  the Perron–Frobenius eigenpair of `M` (existence of the positive eigenvector is
  the classical PF input cited by the paper, taken here as a hypothesis exactly as
  in `Section21.lean`).
* **Reusable analytic core** `vecMul_pow_geometric` / `vecMul_recursion_geometric`:
  for a nonnegative matrix `A` with a positive right eigenvector `u` (eigenvalue `ρ`),
  the row-iterate sum `∑ⱼ (w · Aⁿ)ⱼ` is squeezed between `c·ρⁿ` and `C·ρⁿ`.  Applied
  to `M` it gives mass growth; applied to the **degree matrix `N`** (with the cited
  substitution recursion `κ_{Ξⁿ⁺¹}(v) = κ_{Ξⁿ}(v)·N`) it gives degree growth.
* **Exit time / walk dimension.**  `eigs_commute_time` (Proposition 2.24: commute
  time `≍ (ρ(M)ρ(Ψ))ⁿ`) and `eigs_walk_dimension` (Theorem 2.23/2.26) follow by
  feeding the proved mass growth, the resistance growth of `Section21.lean`, and the
  cited distance growth into the analytic results of `Section22.lean`.

## What is cited (as in the rest of the project)

The genuinely deep Section-1 inputs of [36, 38] — the **distance growth**
`diam(Ξⁿ) ≍ ρ_min(𝒟)ⁿ`, and the **degree substitution recursion**
`κ_{Ξⁿ}(v) = κ_{Ξᵐ}(v)·N^{n-m}` (which requires the full vertex-identification
quotient) — and the **Perron–Frobenius existence** of positive eigenvectors are
taken as hypotheses, exactly as the paper cites them.  Everything else (the
edge-substitution combinatorics, the mass recursion, and all geometric-growth
estimates) is proved.
-/

namespace EIGS

open scoped BigOperators
open Filter Topology

/-! ### Definition 1.1: edge-coloured directed multigraphs and EIGS -/

/-- A finite **edge-coloured directed multigraph** with `K` edge colours: a finite
vertex type `V`, a finite edge type `E`, tail/head maps, and a colour map
`𝒞 : E → Fin K`.  (Definition 1.1, the data of `Ξ⁰` and of each rule graph `R_i`.) -/
structure ColGraph (K : ℕ) where
  /-- vertex type. -/
  V : Type
  /-- edge type. -/
  E : Type
  [vFin : Fintype V]
  [eFin : Fintype E]
  [vDec : DecidableEq V]
  [eDec : DecidableEq E]
  /-- tail of a directed edge. -/
  tail : E → V
  /-- head of a directed edge. -/
  head : E → V
  /-- colour of an edge. -/
  col : E → Fin K

attribute [instance] ColGraph.vFin ColGraph.eFin ColGraph.vDec ColGraph.eDec

/-- An **Edge Iterated Graph System** (Definition 1.1, under Assumption 1.2(3) that
the initial graph is a single directed edge).  `initCol` is the colour `ι` of that
single initial edge; `rule i` is the rule graph `R_i`; `plantPlus i`, `plantMinus i`
are the two distinct planting vertices `β_i^+ ≠ β_i^-`. -/
structure EIGSData (K : ℕ) where
  /-- colour `ι` of the single initial edge `Ξ⁰`. -/
  initCol : Fin K
  /-- the rule graph `R_i` for each colour `i`. -/
  rule : Fin K → ColGraph K
  /-- the planting vertex `β_i^+`. -/
  plantPlus : (i : Fin K) → (rule i).V
  /-- the planting vertex `β_i^-`. -/
  plantMinus : (i : Fin K) → (rule i).V
  /-- the two planting vertices are distinct. -/
  plant_ne : ∀ i, plantPlus i ≠ plantMinus i

/-- The **edge data** of an EIGS that the substitution combinatorics depends on:
the initial colour `ι`, the rule-edge types `E(R_i)`, and the rule colour maps. -/
structure RuleData (K : ℕ) where
  /-- colour of the single initial edge. -/
  ι : Fin K
  /-- edge type of rule graph `R_i`. -/
  RE : Fin K → Type
  [REfin : ∀ i, Fintype (RE i)]
  [REdec : ∀ i, DecidableEq (RE i)]
  /-- colour map of rule graph `R_i`. -/
  rcol : (i : Fin K) → RE i → Fin K

attribute [instance] RuleData.REfin RuleData.REdec

variable {K : ℕ}

/-- The edge data extracted from a full EIGS. -/
def EIGSData.toRuleData (𝓘 : EIGSData K) : RuleData K where
  ι := 𝓘.initCol
  RE := fun i => (𝓘.rule i).E
  REfin := fun i => (𝓘.rule i).eFin
  REdec := fun i => (𝓘.rule i).eDec
  rcol := fun i e => (𝓘.rule i).col e

/-! ### The substitution networks `Ξⁿ` (edges and colours)

We define the edges of `Ξⁿ` together with their colours.  An edge of `Ξⁿ⁺¹` is a
pair `(e, e')` with `e` an edge of `Ξⁿ` (of colour `i = 𝒞(e)`) and `e'` an edge of
the rule graph `R_i`; its colour is the colour of `e'` in `R_i`.  This is exactly
the simultaneous parallel edge substitution of Definition 1.1. -/

/-- Level data: the edge type of `Ξⁿ` packaged with its colour map. -/
def XiLvl (D : RuleData K) : ℕ → Σ T : Type, T → Fin K
  | 0 => ⟨Unit, fun _ => D.ι⟩
  | (n+1) => ⟨Σ e : (XiLvl D n).1, D.RE ((XiLvl D n).2 e),
              fun p => D.rcol ((XiLvl D n).2 p.1) p.2⟩

/-- The edge type of `Ξⁿ`. -/
def XiEdge (D : RuleData K) (n : ℕ) : Type := (XiLvl D n).1

/-- The colour map `𝒞 : E(Ξⁿ) → Fin K`. -/
def XiCol (D : RuleData K) (n : ℕ) : XiEdge D n → Fin K := (XiLvl D n).2

instance XiEdgeFintype (D : RuleData K) : (n : ℕ) → Fintype (XiEdge D n)
  | 0 => inferInstanceAs (Fintype Unit)
  | (n+1) => by
      letI := XiEdgeFintype D n
      exact inferInstanceAs (Fintype (Σ e : XiEdge D n, D.RE (XiCol D n e)))

instance XiEdgeDecEq (D : RuleData K) : (n : ℕ) → DecidableEq (XiEdge D n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | (n+1) => by
      letI := XiEdgeDecEq D n
      exact inferInstanceAs (DecidableEq (Σ e : XiEdge D n, D.RE (XiCol D n e)))

/-- The number of colour-`j` edges of `Ξⁿ` (the `j`-th coordinate of `χ(Ξⁿ)`). -/
def chiCount (D : RuleData K) (n : ℕ) (j : Fin K) : ℕ :=
  (Finset.univ.filter (fun e : XiEdge D n => XiCol D n e = j)).card

/-! ### The mass matrix `M` (Definition 1.1, growth matrices) -/

/-- The **mass matrix** `M`: `M i j` is the number of colour-`j` edges of the rule
graph `R_i`.  (Definition 1.1: `[M]_{ij} = |{e ∈ E(R_i) : 𝒞(e) = j}|`.) -/
def massMatrix (D : RuleData K) : Matrix (Fin K) (Fin K) ℕ :=
  fun i j => (Finset.univ.filter (fun e' : D.RE i => D.rcol i e' = j)).card

/-- The mass matrix as a real matrix (for spectral computations). -/
def massMatrixR (D : RuleData K) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => ((massMatrix D i j : ℕ) : ℝ)

@[simp] lemma massMatrixR_nonneg (D : RuleData K) (i j : Fin K) : 0 ≤ massMatrixR D i j := by
  unfold massMatrixR; positivity

/-
**Mass recursion (one step).**  The colour-count vector satisfies
`χ(Ξⁿ⁺¹)_j = ∑_i χ(Ξⁿ)_i · M_{ij}`.
-/
theorem chiCount_succ (D : RuleData K) (n : ℕ) (j : Fin K) :
    chiCount D (n+1) j = ∑ i, chiCount D n i * massMatrix D i j := by
  -- We can expand the left-hand side using the definition of `chiCount`.
  have h_expand : (Finset.univ.filter (fun e : XiEdge D (n + 1) => XiCol D (n + 1) e = j)).card = ∑ e : XiEdge D n, (Finset.univ.filter (fun e' : D.RE (XiCol D n e) => D.rcol (XiCol D n e) e' = j)).card := by
    simp +decide only [XiCol, Finset.card_filter];
    erw [ Finset.sum_sigma ];
    rfl;
  convert h_expand using 1;
  simp +decide only [chiCount, Finset.card_filter, massMatrix];
  simp +decide only [Finset.sum_mul];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-
Base case of the colour count: `Ξ⁰` is a single edge of colour `ι`.
-/
theorem chiCount_zero (D : RuleData K) (j : Fin K) :
    chiCount D 0 j = (if j = D.ι then 1 else 0) := by
  unfold chiCount; split_ifs <;> simp_all +decide [ Finset.card_univ ] ;
  · rw [ Finset.card_eq_one ] ; use ⟨ ⟩ ; ext ; aesop;
  · exact fun x => by rw [ show XiCol D 0 = fun _ => D.ι from rfl ] ; aesop;

/-- The real colour-count (row) vector `χ(Ξⁿ) : Fin K → ℝ`. -/
def chiVec (D : RuleData K) (n : ℕ) : Fin K → ℝ := fun j => (chiCount D n j : ℝ)

/-
The mass recursion as a `vecMul`: `χ(Ξⁿ⁺¹) = χ(Ξⁿ) ·ᵥ M`.
-/
theorem chiVec_succ (D : RuleData K) (n : ℕ) :
    chiVec D (n+1) = Matrix.vecMul (chiVec D n) (massMatrixR D) := by
  ext j; exact (by
  convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( chiCount_succ D n j ) using 1 ; norm_num [ Matrix.vecMul, dotProduct, massMatrixR ] ; ring!;)

/-
The closed form `χ(Ξⁿ) = χ(Ξ⁰) ·ᵥ Mⁿ`.
-/
theorem chiVec_vecMul_pow (D : RuleData K) (n : ℕ) :
    chiVec D n = Matrix.vecMul (chiVec D 0) (massMatrixR D ^ n) := by
  induction' n with n ih;
  · norm_num [ Matrix.vecMul, Matrix.one_apply ];
  · rw [ pow_succ, ← Matrix.vecMul_vecMul, ← ih, chiVec_succ ]

/-- The total number of edges of `Ξⁿ`. -/
def totalEdges (D : RuleData K) (n : ℕ) : ℕ := Fintype.card (XiEdge D n)

/-
`|E(Ξⁿ)| = ∑_j χ(Ξⁿ)_j`.
-/
theorem totalEdges_eq_sum (D : RuleData K) (n : ℕ) :
    (totalEdges D n : ℝ) = ∑ j, chiVec D n j := by
  unfold totalEdges;
  unfold chiVec;
  unfold chiCount;
  rw_mod_cast [ Fintype.card_eq_sum_ones, Finset.sum_congr rfl fun x hx => Finset.card_filter _ _ ];
  rw [ Finset.sum_comm ] ; aesop

/-! ### Geometric growth: the reusable analytic core

For a nonnegative matrix `A` with a positive right eigenvector `u` (`A u = ρ u`),
the sum of the entries of the row-iterate `w ·ᵥ Aⁿ` grows like `ρⁿ`, up to two
constants.  The key identity is `(w ·ᵥ Aⁿ) ⬝ᵥ u = ρⁿ (w ⬝ᵥ u)`, and the entrywise
nonnegativity of `w ·ᵥ Aⁿ` lets us compare its sum with this weighted sum. -/

/-
Entrywise nonnegativity of matrix powers of a nonnegative matrix.
-/
theorem matrix_pow_nonneg {A : Matrix (Fin K) (Fin K) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) (i j : Fin K) : 0 ≤ (A ^ n) i j := by
  induction' n with n ih generalizing i j;
  · by_cases hij : i = j <;> aesop;
  · simpa only [ pow_succ, Matrix.mul_apply ] using Finset.sum_nonneg fun k _ => mul_nonneg ( ih i k ) ( hA k j )

/-
A right eigenvector of `A` is a right eigenvector of `Aⁿ` with eigenvalue `ρⁿ`.
-/
theorem matrix_pow_mulVec_eigen {A : Matrix (Fin K) (Fin K) ℝ}
    {u : Fin K → ℝ} {ρ : ℝ} (heig : A.mulVec u = ρ • u) (n : ℕ) :
    (A ^ n).mulVec u = ρ ^ n • u := by
  induction n <;> simp_all +decide [ pow_succ', Matrix.mulVec_smul ];
  simp_all +decide [ ← Matrix.mulVec_mulVec, mul_assoc ];
  rw [ Matrix.mulVec_smul, heig, smul_smul, mul_comm ]

/-
**Geometric growth core.**  If `A ≥ 0` entrywise has a positive right
eigenvector `u` with eigenvalue `ρ > 0`, and `w ≥ 0` with `∑ᵢ wᵢ uᵢ > 0`, then
`∑ⱼ (w ·ᵥ Aⁿ)ⱼ ≍ ρⁿ`.
-/
theorem vecMul_pow_geometric {A : Matrix (Fin K) (Fin K) ℝ} {w u : Fin K → ℝ} {ρ : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 < u i) (hw : ∀ i, 0 ≤ w i)
    (hwu : 0 < ∑ i, w i * u i)
    (heig : A.mulVec u = ρ • u) (hρ : 0 < ρ) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * ρ ^ n ≤ ∑ j, (Matrix.vecMul w (A ^ n)) j
        ∧ ∑ j, (Matrix.vecMul w (A ^ n)) j ≤ C * ρ ^ n := by
  -- Let $S := \sum_{i} w_i u_i$.
  set S : ℝ := ∑ i, w i * u i;
  -- By definition of $S$, we know that $\sum_{j} (vecMul w (A^n)) j * u j = S * ρ^n$.
  have h_sum : ∀ n, ∑ j, (Matrix.vecMul w (A ^ n)) j * u j = S * ρ ^ n := by
    intro n
    have h_dot : ∑ j, (Matrix.vecMul w (A ^ n)) j * u j = ∑ i, w i * ((A ^ n).mulVec u) i := by
      simp +decide only [Matrix.vecMul, Matrix.mulVec, dotProduct];
      simp +decide only [Finset.sum_mul, mul_assoc, Finset.mul_sum _ _ _] ; exact Finset.sum_comm;
    have h_eigen : (A ^ n).mulVec u = ρ ^ n • u := by
      convert matrix_pow_mulVec_eigen heig n using 1;
    simp_all +decide [ mul_comm, Finset.mul_sum _ _ _ ];
    simp +decide only [← mul_assoc, mul_comm, ← Finset.sum_mul, S];
  -- Let $umin := \min_{i} u_i$ and $umax := \max_{i} u_i$.
  obtain ⟨umin, humin⟩ : ∃ umin, 0 < umin ∧ ∀ i, umin ≤ u i := by
    rcases K with ( _ | K ) <;> norm_num at *;
    exact ⟨ Finset.min' ( Finset.univ.image u ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ 0 ) ⟩, by have := Finset.min'_mem ( Finset.univ.image u ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ 0 ) ⟩ ; aesop, fun i => Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ _ ⟩
  obtain ⟨umax, humax⟩ : ∃ umax, 0 < umax ∧ ∀ i, u i ≤ umax := by
    exact ⟨ ∑ i, u i + 1, add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => le_of_lt ( hu _ ) ) zero_lt_one, fun i => by linarith [ Finset.single_le_sum ( fun i _ => le_of_lt ( hu i ) ) ( Finset.mem_univ i ) ] ⟩;
  -- Using the bounds on $u$, we can bound the sum $\sum_{j} (vecMul w (A^n)) j$.
  have h_bound : ∀ n, umin * ∑ j, (Matrix.vecMul w (A ^ n)) j ≤ S * ρ ^ n ∧ S * ρ ^ n ≤ umax * ∑ j, (Matrix.vecMul w (A ^ n)) j := by
    intros n
    have h_nonneg : ∀ j, 0 ≤ (Matrix.vecMul w (A ^ n)) j := by
      intro j
      simp [Matrix.vecMul];
      exact Finset.sum_nonneg fun i _ => mul_nonneg ( hw i ) ( matrix_pow_nonneg hA n i j );
    exact ⟨ by rw [ ← h_sum n, Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by nlinarith [ h_nonneg i, humin.2 i ], by rw [ ← h_sum n, Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by nlinarith [ h_nonneg i, humax.2 i ] ⟩;
  use S / umax, S / umin;
  exact ⟨ div_pos hwu humax.1, div_pos hwu humin.1, fun n => ⟨ by rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ h_bound n, pow_pos hρ n ], by rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ h_bound n, pow_pos hρ n ] ⟩ ⟩

/-
**Geometric growth from a `vecMul` recursion.**  If a nonnegative sequence of
row vectors satisfies `seq (n+1) = seq n ·ᵥ A`, the matrix `A` is nonnegative with a
positive right eigenvector `u` (eigenvalue `ρ > 0`), and `∑ᵢ (seq 0)ᵢ uᵢ > 0`, then
`∑ⱼ (seq n)ⱼ ≍ ρⁿ`.  (Used for the mass matrix `M` and the degree matrix `N`.)
-/
theorem vecMul_recursion_geometric {A : Matrix (Fin K) (Fin K) ℝ}
    {seq : ℕ → Fin K → ℝ} {u : Fin K → ℝ} {ρ : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 < u i)
    (hseq0 : ∀ i, 0 ≤ seq 0 i) (hwu : 0 < ∑ i, seq 0 i * u i)
    (hrec : ∀ n, seq (n+1) = Matrix.vecMul (seq n) A)
    (heig : A.mulVec u = ρ • u) (hρ : 0 < ρ) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * ρ ^ n ≤ ∑ j, seq n j ∧ ∑ j, seq n j ≤ C * ρ ^ n := by
  convert vecMul_pow_geometric hA hu hseq0 hwu heig hρ using 1;
  congr! 7;
  · congr! 2;
    induction ‹ℕ› <;> simp_all +decide [ pow_succ, Matrix.vecMul_mulVec ];
    rename_i n ih; rw [ show seq n = Matrix.vecMul ( seq 0 ) ( A ^ n ) from Nat.recOn n ( by aesop ) fun n ihn => by aesop ] ; simp +decide [ Matrix.vecMul_mulVec ] ;
  · congr! 2;
    rename_i n _;
    rename_i k _;
    induction' k with k ih generalizing n <;> simp_all +decide [ pow_succ ];
    simp +decide [ funext ih ]

/-! ### Geometric mass growth (Lemma 2.13 / Section 1)

`|E(Ξⁿ)| ≍ ρ(M)ⁿ`, where `ρ(M)` is the Perron eigenvalue of the mass matrix.  The
existence of a positive eigenvector is the Perron–Frobenius input (cited), here a
hypothesis; the geometric two-sided bound is then proved. -/

/-
**Geometric mass growth.**  Given a positive right Perron eigenvector `u` of the
mass matrix with eigenvalue `ρM > 0` and a nontrivial initial colour weighting
(`u (ι) > 0`, automatic since `u > 0`), the edge count satisfies
`c · ρMⁿ ≤ |E(Ξⁿ)| ≤ C · ρMⁿ`.
-/
theorem mass_geometric_growth (𝓘 : EIGSData K) {u : Fin K → ℝ} {ρM : ℝ}
    (hu : ∀ i, 0 < u i) (heig : (massMatrixR 𝓘.toRuleData).mulVec u = ρM • u)
    (hρM : 0 < ρM) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * ρM ^ n ≤ (totalEdges 𝓘.toRuleData n : ℝ)
        ∧ (totalEdges 𝓘.toRuleData n : ℝ) ≤ C * ρM ^ n := by
  have := @vecMul_recursion_geometric K;
  contrapose! this;
  refine' ⟨ massMatrixR 𝓘.toRuleData, fun n => chiVec 𝓘.toRuleData n, u, ρM, _, _, _, _, _, _ ⟩ <;> norm_num [ massMatrixR_nonneg, hu, heig, hρM ];
  · exact fun i => Nat.cast_nonneg _;
  · unfold chiVec; simp +decide [ chiCount_zero ] ;
    exact hu _;
  · grind +suggestions;
  · intro c C hc hC; obtain ⟨ n, hn ⟩ := this c C hc hC; use n; simp_all +decide [ totalEdges_eq_sum ] ;

/-! ### Geometric degree growth (Section 1, degree matrix `N`)

The degree-amplification recursion `κ_{Ξⁿ⁺¹}(v) = κ_{Ξⁿ}(v) ·ᵥ N` (Definition 1.1;
its proof uses the full vertex-identification structure of the substitution and is
the cited [36] input) yields, via the same analytic core, the geometric growth
`κ_{Ξⁿ}(v) ≍ ρ(N)ⁿ` of coloured degrees of a finite-born vertex. -/

/-- **Geometric degree growth.**  For a coloured-degree sequence `κ` of a
finite-born vertex obeying the substitution recursion `κ (n+1) = κ n ·ᵥ N`, with `N`
nonnegative and possessing a positive right Perron eigenvector `u` (eigenvalue
`ρN > 0`) and a nontrivial initial degree (`∑ᵢ (κ 0)ᵢ uᵢ > 0`), the total degree
grows geometrically: `c · ρNⁿ ≤ ∑ⱼ κ(n)ⱼ ≤ C · ρNⁿ`. -/
theorem degree_geometric_growth {L : ℕ} {N : Matrix (Fin L) (Fin L) ℝ}
    {kappa : ℕ → Fin L → ℝ} {u : Fin L → ℝ} {ρN : ℝ}
    (hN : ∀ i j, 0 ≤ N i j) (hu : ∀ i, 0 < u i)
    (hk0 : ∀ i, 0 ≤ kappa 0 i) (hwu : 0 < ∑ i, kappa 0 i * u i)
    (hrec : ∀ n, kappa (n+1) = Matrix.vecMul (kappa n) N)
    (heig : N.mulVec u = ρN • u) (hρN : 0 < ρN) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * ρN ^ n ≤ ∑ j, kappa n j ∧ ∑ j, kappa n j ≤ C * ρN ^ n :=
  vecMul_recursion_geometric hN hu hk0 hwu hrec heig hρN

/-! ### Exit time and walk dimension (Section 2.2, now with mass growth discharged)

With geometric mass growth proved, the exit-time / walk-dimension results of
`Section22.lean` no longer need `|E(Ξⁿ)| ≍ ρ(M)ⁿ` as a hypothesis: it is now a
theorem.  We record the two consequences. -/

/-
**Proposition 2.24 (commute / exit time scaling) for an EIGS.**  Using the proved
mass growth `|E(Ξⁿ)| ≍ ρ(M)ⁿ` and the resistance growth `ℛ_{Ξⁿ} ≍ ρ(Ψ)ⁿ` (Corollary
2.7), the commute time `T_n = 2|E(Ξⁿ)| ℛ_{Ξⁿ}(𝔳₊,𝔳₋)` satisfies
`c·(ρ(M)ρ(Ψ))ⁿ ≤ T_n ≤ C·(ρ(M)ρ(Ψ))ⁿ`.
-/
theorem eigs_commute_time (𝓘 : EIGSData K)
    {u : Fin K → ℝ} {ρM : ℝ}
    (hu : ∀ i, 0 < u i) (heig : (massMatrixR 𝓘.toRuleData).mulVec u = ρM • u) (hρM : 0 < ρM)
    (Ψ : RenormMap K) {vΨ : Fin K → ℝ} {ρPsi : ℝ}
    (hvΨ : ∀ i, 0 < vΨ i) (hρPsi : 0 < ρPsi) (heigΨ : Ψ.apply vΨ = ρPsi • vΨ) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * (ρM * ρPsi) ^ n
        ≤ 2 * (totalEdges 𝓘.toRuleData n : ℝ) * (Ψ.apply^[n] (fun _ => 1)) 𝓘.initCol
      ∧ 2 * (totalEdges 𝓘.toRuleData n : ℝ) * (Ψ.apply^[n] (fun _ => 1)) 𝓘.initCol
        ≤ C * (ρM * ρPsi) ^ n := by
  obtain ⟨ cE, CE, hcE, hCE, hE ⟩ := mass_geometric_growth 𝓘 hu heig hρM;
  obtain ⟨ cΨ, CΨ, hcΨ, hCΨ, hR ⟩ := EIGS.RenormMap.single_edge_resistance_growth Ψ hvΨ hρPsi heigΨ 𝓘.initCol; use 2 * cE * cΨ, 2 * CE * CΨ; simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ] ;
  intro n; constructor <;> nlinarith [ hE n, hR n, show 0 ≤ cE * ρM ^ n by positivity, show 0 ≤ cΨ * ρPsi ^ n by positivity, show 0 ≤ CE * ρM ^ n by positivity, show 0 ≤ CΨ * ρPsi ^ n by positivity ] ;

/-- **Theorem 2.23 / 2.26 (walk dimension) for an EIGS.**  Combining the proved mass
growth, the resistance growth (Corollary 2.7), and the cited distance growth
`diam(Ξⁿ) ≍ ρ_min(𝒟)ⁿ`, the walk dimension of `Ξ` (as the exit-time-vs-radius
scaling exponent) equals `dim_B + dim_R = log ρ(M)/log ρ_min + log ρ(Ψ)/log ρ_min`. -/
theorem eigs_walk_dimension
    {Exit Rad : ℕ → ℝ} {ρM ρPsi ρmin : ℝ} {m : ℕ → ℕ}
    (hρM : 0 < ρM) (hρPsi : 0 < ρPsi) (hρmin : 1 < ρmin) (hm : Tendsto m atTop atTop)
    (hExit : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n, c₁ * (ρM * ρPsi) ^ (m n) ≤ Exit n ∧ Exit n ≤ c₂ * (ρM * ρPsi) ^ (m n))
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
      ∀ n, c₃ * ρmin ^ (m n) ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ (m n)) :
    resistanceDimension Exit Rad
      = Real.log ρM / Real.log ρmin + Real.log ρPsi / Real.log ρmin :=
  walk_dimension_einstein hρM hρPsi hρmin hm hExit hRad

end EIGS