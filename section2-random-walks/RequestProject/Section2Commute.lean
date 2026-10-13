import Mathlib
import RequestProject.Section2Network

/-!
# Random walks, hitting times and the commute-time identity `C = 2|E|·R`

This file builds the **random-walk / hitting-time / commute-time** layer of
Section 2 directly from the **linear systems** that characterise them, and proves
the commute-time identity

  `C(a, b) = 2 |E| · R(a, b)`

self-contained from finite linear algebra (the Chandra–Raghavan–Ruzzo–Smolensky–
Tiwari identity).  In `Section1.lean` / `Section22.lean` this identity was taken as
a cited hypothesis (`commute_time_bounds` assumed `T = 2|E|ℛ`); here it is a
theorem, available as the middleware that turns the geometric mass × resistance
growth into a genuine commute-time scaling.

## The linear-system characterisations

Work on a finite connected simple graph `G` with graph Laplacian `L = D − A`
(`SimpleGraph.lapMatrix ℝ G`).

* **Hitting times.**  The expected hitting time `h_z` of the simple random walk to a
  target `z` is characterised by the linear system
  `h_z z = 0` and `∀ x ≠ z, (L ·ᵥ h_z) x = deg x`
  (the recurrence `deg(x) h(x) = deg(x) + ∑_{y∼x} h(y)`).  We take a solution as
  given (`HittingSystem`); on a connected graph it is unique up to the value at
  `z`, which is pinned by `h_z z = 0`.
* **Commute time.**  `C(a,b) = h_b a + h_a b`.
* **Effective resistance.**  The potential `φ` of a unit current from `a` to `b`
  solves `L ·ᵥ φ = e_a − e_b`; the effective resistance is the potential drop
  `R(a,b) = φ a − φ b` (the standard electrical-network characterisation).

## Main result

`commute_eq_two_card_edges_mul_resistance`:
`h_b a + h_a b = 2 |E| · (φ a − φ b)`, i.e. `C = 2|E|·R`.

The proof is pure linear algebra: the global column-sum-zero of `L` pins
`(L ·ᵥ h_z) z = deg z − 2|E|`, so `L ·ᵥ (h_a − h_b + 2|E|·φ) = 0`; since the kernel
of the Laplacian of a connected graph is the constants, `h_a − h_b + 2|E|·φ` is
constant, and evaluating at `a` and `b` gives the identity.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The "twice the number of edges" weight `2|E| = ∑_v deg(v)`, as a real number. -/
def twoCardEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ v, (G.degree v : ℝ)

omit [DecidableEq V] in
lemma twoCardEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    twoCardEdges G = 2 * (G.edgeFinset.card : ℝ) := by
  unfold twoCardEdges
  rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  push_cast; ring

/-
The columns of the Laplacian sum to zero, hence so do the entries of any
Laplacian image `L ·ᵥ h`.
-/
lemma lapMatrix_mulVec_sum_zero (G : SimpleGraph V) [DecidableRel G.Adj] (h : V → ℝ) :
    ∑ x, (G.lapMatrix ℝ *ᵥ h) x = 0 := by
  unfold lapMatrix;
  simp +decide [ Matrix.mulVec, dotProduct, degMatrix, adjMatrix ];
  simp +decide [ sub_mul, Finset.sum_ite, SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
  simp +decide [ Finset.sum_filter, Matrix.diagonal ];
  rw [ sub_eq_zero, Finset.sum_comm ];
  simp +decide [ Finset.sum_ite, SimpleGraph.adj_comm ]

/-- The linear system characterising the expected hitting time `h` of the random
walk to the target `z`: value `0` at `z`, and the Laplacian recurrence off `z`. -/
def HittingSystem (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (h : V → ℝ) : Prop :=
  h z = 0 ∧ ∀ x, x ≠ z → (G.lapMatrix ℝ *ᵥ h) x = (G.degree x : ℝ)

/-
From the off-target hitting recurrence, the global column-sum-zero pins the
value of `L ·ᵥ h` at the target: `(L ·ᵥ h) z = deg z − 2|E|`.
-/
lemma HittingSystem.lapMatrix_mulVec_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {z : V} {h : V → ℝ} (hh : HittingSystem G z h) :
    (G.lapMatrix ℝ *ᵥ h) = fun x => (G.degree x : ℝ) - twoCardEdges G * (if x = z then 1 else 0) := by
  -- By definition of $H$, we know that $(G.lapMatrix ℝ *ᵥ h) x = G.degree x$ for $x ≠ z$.
  have h_off_target (x : V) (hx : x ≠ z) : (G.lapMatrix ℝ *ᵥ h) x = (G.degree x : ℝ) := by
    exact hh.2 x hx;
  -- By definition of $H$, we know that $(G.lapMatrix ℝ *ᵥ h) z = G.degree z - twoCardEdges G$.
  have h_on_target : (G.lapMatrix ℝ *ᵥ h) z = (G.degree z : ℝ) - twoCardEdges G := by
    have h_on_target : ∑ x ∈ Finset.univ.erase z, (G.lapMatrix ℝ *ᵥ h) x = ∑ x ∈ Finset.univ.erase z, (G.degree x : ℝ) := by
      exact Finset.sum_congr rfl fun x hx => h_off_target x <| Finset.ne_of_mem_erase hx;
    have := lapMatrix_mulVec_sum_zero G h; simp_all +decide [ twoCardEdges ] ;
    linarith;
  grind +qlia

/-
**The commute-time identity `C = 2|E|·R`.**  On a connected simple graph,
if `hA`, `hB` solve the hitting-time systems to `a`, `b`, and `φ` is the unit-current
potential from `a` to `b` (`L ·ᵥ φ = e_a − e_b`), then the commute time
`hB a + hA b` equals `2|E|` times the effective resistance `φ a − φ b`.
-/
theorem commute_eq_two_card_edges_mul_resistance
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {a b : V} {hA hB φ : V → ℝ}
    (hHa : HittingSystem G a hA) (hHb : HittingSystem G b hB)
    (hφ : (G.lapMatrix ℝ *ᵥ φ)
        = fun x => (if x = a then (1 : ℝ) else 0) - (if x = b then 1 else 0)) :
    hB a + hA b = 2 * (G.edgeFinset.card : ℝ) * (φ a - φ b) := by
  -- By `HittingSystem.lapMatrix_mulVec_eq`, `(L ·ᵥ hA) = fun x => (G.degree x : ℝ) - M * (if x = a then 1 else 0)` and `(L ·ᵥ hB) = fun x => (G.degree x : ℝ) - M * (if x = b then 1 else 0)`.
  set M := twoCardEdges G with hM
  have hA_eq : G.lapMatrix ℝ *ᵥ hA = fun x => (G.degree x : ℝ) - M * (if x = a then 1 else 0) :=
    HittingSystem.lapMatrix_mulVec_eq G hHa
  have hB_eq : G.lapMatrix ℝ *ᵥ hB = fun x => (G.degree x : ℝ) - M * (if x = b then 1 else 0) :=
    HittingSystem.lapMatrix_mulVec_eq G hHb
  -- By `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`, `L ·ᵥ g = 0 ↔ ∀ i j, G.Reachable i j → g i = g j`. Since `G` is connected (`hG.preconnected a b : G.Reachable a b`), `g a = g b`.
  have h_const : ∀ i j, G.Reachable i j → (hA i - hB i + M * φ i) = (hA j - hB j + M * φ j) := by
    have h_const : G.lapMatrix ℝ *ᵥ (hA - hB + M • φ) = 0 := by
      simp_all +decide [ funext_iff, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul ];
      intro x; split_ifs <;> ring;
    have := SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable ( G := G ) ( x := hA - hB + M • φ ) ; aesop;
  have := h_const a b ( hG a b ) ; simp_all +decide [ HittingSystem ] ;
  rw [ twoCardEdges_eq ] at this; linarith;

end EIGS