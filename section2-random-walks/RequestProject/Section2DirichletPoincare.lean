import RequestProject.Section2RandomWalk
import RequestProject.Section2Green

/-! Dirichlet Poincaré from the actual finite Green inverse and reversibility.
Our energy counts each unoriented edge once, so the constant is the maximum
actual expected exit time, with no additional factor of two. -/

namespace EIGS

open scoped BigOperators Classical
open Matrix

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]

theorem green_weighted_quadratic_le_exit_upper (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (values : domain → ℝ) (upper : ℝ)
    (exit_bound : ∀ vertex : domain, expExit graph domain vertex ≤ upper) :
    (∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex *
      (greenFn graph domain *ᵥ (fun point : domain => (graph.degree point : ℝ) * values point)) vertex) ≤
      upper * ∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2 := by
  have symmetry_sum :
      (∑ first : domain, ∑ second : domain,
        (graph.degree first : ℝ) * greenFn graph domain first second *
          (graph.degree second : ℝ) * values second ^ 2) =
      ∑ first : domain, ∑ second : domain,
        (graph.degree first : ℝ) * greenFn graph domain first second *
          (graph.degree second : ℝ) * values first ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [green_symm graph domain second first]
    ring
  have pairwise_bound :
      (∑ first : domain, ∑ second : domain,
        2 * ((graph.degree first : ℝ) * values first *
          (greenFn graph domain first second * ((graph.degree second : ℝ) * values second)))) ≤
      ∑ first : domain, ∑ second : domain,
        ((graph.degree first : ℝ) * greenFn graph domain first second *
          (graph.degree second : ℝ) * values first ^ 2 +
        (graph.degree first : ℝ) * greenFn graph domain first second *
          (graph.degree second : ℝ) * values second ^ 2) := by
    apply Finset.sum_le_sum
    intro first _
    apply Finset.sum_le_sum
    intro second _
    have coefficient_nonnegative : 0 ≤ (graph.degree first : ℝ) * greenFn graph domain first second *
        (graph.degree second : ℝ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (greenFn_nonneg graph connected proper first second)) (Nat.cast_nonneg _)
    have square_bound := mul_nonneg coefficient_nonnegative (sq_nonneg (values first - values second))
    nlinarith
  have row_bound :
      (∑ first : domain, ∑ second : domain,
        (graph.degree first : ℝ) * greenFn graph domain first second *
          (graph.degree second : ℝ) * values first ^ 2) ≤
      upper * ∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro first _
    have row_identity := exit_eq_green_weighted graph connected proper (exitSystem_expExit connected proper) first.property
    calc
      _ = ((graph.degree first : ℝ) * values first ^ 2) * expExit graph domain first := by
        rw [row_identity, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left (exit_bound first)
          (mul_nonneg (Nat.cast_nonneg (graph.degree first)) (sq_nonneg (values first)))]
  simp only [Finset.sum_add_distrib] at pairwise_bound
  rw [symmetry_sum] at pairwise_bound
  have expanded :
      (∑ first : domain, ∑ second : domain,
        2 * ((graph.degree first : ℝ) * values first *
          (greenFn graph domain first second * ((graph.degree second : ℝ) * values second)))) =
      2 * ∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex *
        (greenFn graph domain *ᵥ (fun point : domain => (graph.degree point : ℝ) * values point)) vertex := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [expanded] at pairwise_bound
  linarith

theorem dirichlet_poincare_subtype_of_exit_upper (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (values : domain → ℝ) (upper : ℝ) (upper_positive : 0 < upper)
    (exit_bound : ∀ vertex : domain, expExit graph domain vertex ≤ upper) :
    (∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2) ≤
      upper * ∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ values) vertex := by
  let forcing : domain → ℝ := fun vertex => (graph.degree vertex : ℝ) * values vertex
  let green_potential : domain → ℝ := greenFn graph domain *ᵥ forcing
  have potential_equation : dirichletLap graph domain *ᵥ green_potential = forcing := by
    dsimp [green_potential]
    rw [Matrix.mulVec_mulVec, dirichletLap_mul_greenFn graph connected proper, Matrix.one_mulVec]
  have cross_identity :
      (∑ vertex : domain, green_potential vertex * (dirichletLap graph domain *ᵥ values) vertex) =
      ∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2 := by
    have symmetric_pairing :
        (∑ vertex : domain, green_potential vertex * (dirichletLap graph domain *ᵥ values) vertex) =
        ∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ green_potential) vertex := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      have symmetric_entry : dirichletLap graph domain second first = dirichletLap graph domain first second :=
        congrArg (fun matrix => matrix first second) (dirichletLap_isSymm graph domain)
      rw [symmetric_entry]
      ring
    rw [symmetric_pairing, potential_equation]
    apply Finset.sum_congr rfl
    intro vertex _
    dsimp [forcing]
    ring
  have linearity : dirichletLap graph domain *ᵥ (fun vertex => upper * values vertex - green_potential vertex) =
      fun vertex => upper * (dirichletLap graph domain *ᵥ values) vertex - forcing vertex := by
    change dirichletLap graph domain *ᵥ (upper • values - green_potential) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, potential_equation]
    rfl
  have energy_nonnegative := (dirichletLap_posDef graph connected proper).posSemidef.dotProduct_mulVec_nonneg
    (fun vertex => upper * values vertex - green_potential vertex)
  simp only [Pi.star_apply, star_trivial, dotProduct, linearity] at energy_nonnegative
  have expansion :
      (∑ vertex : domain, (upper * values vertex - green_potential vertex) *
        (upper * (dirichletLap graph domain *ᵥ values) vertex - forcing vertex)) =
      upper ^ 2 * (∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ values) vertex) -
      2 * upper * (∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2) +
      ∑ vertex : domain, forcing vertex * green_potential vertex := by
    calc
      _ = upper ^ 2 * (∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ values) vertex) -
          upper * (∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2) -
          upper * (∑ vertex : domain, green_potential vertex * (dirichletLap graph domain *ᵥ values) vertex) +
          ∑ vertex : domain, forcing vertex * green_potential vertex := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro vertex _
        dsimp [forcing]
        ring
      _ = _ := by rw [cross_identity]; ring
  rw [expansion] at energy_nonnegative
  have green_bound := green_weighted_quadratic_le_exit_upper graph connected proper values upper exit_bound
  change (∑ vertex : domain, forcing vertex * green_potential vertex) ≤ _ at green_bound
  have product_nonnegative : 0 ≤ upper *
      (upper * (∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ values) vertex) -
        ∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2) := by
    nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left upper_positive).mp product_nonnegative)

theorem dirichlet_poincare_of_exit_upper (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (values : Vertex → ℝ)
    (boundary_zero : ∀ vertex, vertex ∉ domain → values vertex = 0)
    (upper : ℝ) (upper_positive : 0 < upper)
    (exit_bound : ∀ vertex ∈ domain, expExit graph domain vertex ≤ upper) :
    (∑ vertex : Vertex, (graph.degree vertex : ℝ) * values vertex ^ 2) ≤
      upper * dirichletEnergy graph values := by
  have mass_restriction :
      (∑ vertex : domain, (graph.degree vertex : ℝ) * values vertex ^ 2) =
        ∑ vertex : Vertex, (graph.degree vertex : ℝ) * values vertex ^ 2 := by
    rw [Finset.sum_coe_sort domain (fun vertex : Vertex => (graph.degree vertex : ℝ) * values vertex ^ 2)]
    apply Finset.sum_subset (Finset.subset_univ domain)
    intro vertex _ outside
    rw [boundary_zero vertex outside]
    simp
  have energy_restriction :
      (∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ (fun point : domain => values point)) vertex) =
        dirichletEnergy graph values := by
    rw [dirichletEnergy_eq_quad]
    have restriction :
        (∑ vertex : domain, values vertex * (graph.lapMatrix ℝ *ᵥ values) vertex) =
        ∑ vertex : domain, values vertex * (dirichletLap graph domain *ᵥ (fun point : domain => values point)) vertex := by
      apply Finset.sum_congr rfl
      intro vertex _
      rw [lapMatrix_mulVec_restrict graph domain values boundary_zero vertex vertex.property]
    rw [← restriction, Finset.sum_coe_sort domain
      (fun vertex : Vertex => values vertex * (graph.lapMatrix ℝ *ᵥ values) vertex)]
    apply Finset.sum_subset (Finset.subset_univ domain)
    intro vertex _ outside
    rw [boundary_zero vertex outside, zero_mul]
  have inequality := dirichlet_poincare_subtype_of_exit_upper graph connected proper
    (fun vertex : domain => values vertex) upper upper_positive (fun vertex => exit_bound vertex vertex.property)
  rw [mass_restriction, energy_restriction] at inequality
  exact inequality

theorem dirichlet_poincare_max_expExit (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (nonempty : domain.Nonempty) (values : Vertex → ℝ)
    (boundary_zero : ∀ vertex, vertex ∉ domain → values vertex = 0) :
    (∑ vertex : Vertex, (graph.degree vertex : ℝ) * values vertex ^ 2) ≤
      domain.sup' nonempty (expExit graph domain) * dirichletEnergy graph values := by
  apply dirichlet_poincare_of_exit_upper graph connected proper values boundary_zero
  · obtain ⟨vertex, inside⟩ := nonempty
    have exit_positive : 0 < expExit graph domain vertex := by
      rw [expExit_recurrence connected proper inside]
      have nonnegative : 0 ≤ ∑ point : Vertex, transProb graph vertex point * expExit graph domain point :=
        Finset.sum_nonneg (fun point _ => mul_nonneg (transProb_nonneg _ _) (expExit_nonneg _))
      linarith
    exact exit_positive.trans_le (Finset.le_sup' (expExit graph domain) inside)
  · intro vertex inside
    exact Finset.le_sup' (expExit graph domain) inside

end EIGS

#print axioms EIGS.green_weighted_quadratic_le_exit_upper
#print axioms EIGS.dirichlet_poincare_subtype_of_exit_upper
#print axioms EIGS.dirichlet_poincare_of_exit_upper
#print axioms EIGS.dirichlet_poincare_max_expExit
