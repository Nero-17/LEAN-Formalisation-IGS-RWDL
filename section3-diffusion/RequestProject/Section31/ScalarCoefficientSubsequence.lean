import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact

/-! One common subsequence for every scalar coefficient. Countable products
of compact real intervals provide the extraction; no convergence of derivatives
or analyticity of a limiting function is an input. Candidate source, awaiting
whole-file compilation. -/

namespace IGS.Sec31

open Filter Topology

theorem exists_scalar_coefficient_subsequence
    (coefficients : ℕ → ℕ → ℝ) (bounds : ℕ → ℝ)
    (bounded : ∀ index power, |coefficients index power| ≤ bounds power) :
    ∃ indices : ℕ → ℕ, StrictMono indices ∧ ∃ limit : ℕ → ℝ,
      (∀ power, |limit power| ≤ bounds power) ∧
      ∀ power, Tendsto (fun index => coefficients (indices index) power) atTop (𝓝 (limit power)) := by
  have compact : IsCompact {values : ℕ → ℝ | ∀ power, values power ∈ Set.Icc (-(bounds power)) (bounds power)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨limit, limitBounded, indices, indicesStrictMono, convergence⟩ :=
    compact.tendsto_subseq (fun index power => abs_le.mp (bounded index power))
  refine ⟨indices, indicesStrictMono, limit, ?_, ?_⟩
  · intro power
    exact abs_le.mpr (limitBounded power)
  · intro power
    exact (tendsto_pi_nhds.mp convergence) power

end IGS.Sec31

#print axioms IGS.Sec31.exists_scalar_coefficient_subsequence
