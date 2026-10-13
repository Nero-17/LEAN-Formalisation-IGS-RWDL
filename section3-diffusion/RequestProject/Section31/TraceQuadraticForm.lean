import RequestProject.Section31.ExtendedTraceEnergy
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Constructing the quadratic form on the finite-energy domain

For increasing finite-network energies, this file constructs a mathlib
`QuadraticForm` on the submodule constructed in `ExtendedTraceEnergy`.  The
quadratic identities are proved for the edge sums and passed to their limits;
they are not extra fields of a purported limit-form structure.

The required monotonicity is the consequence of trace minimisation that must
be connected to the EIGS networks.  No claim about closedness in L², regularity,
or a Hunt process is made by this construction.
-/

namespace IGS.Sec31

open Filter Topology

namespace FiniteNetwork

variable {Vertex : Type*}

/-- The actual edge-sum energy is a quadratic form. -/
noncomputable def energyQuadraticForm (network : FiniteNetwork Vertex) :
    QuadraticForm ℝ (Vertex → ℝ) :=
  QuadraticMap.ofPolar network.energy
    (by
      intro scalar values
      simpa only [smul_eq_mul, pow_two] using network.energy_smul scalar values)
    (by
      intro first second third
      simp only [QuadraticMap.polar, energy, Pi.add_apply]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      ring)
    (by
      intro scalar first second
      simp only [QuadraticMap.polar, energy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp only [← Finset.sum_sub_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      ring)

end FiniteNetwork

variable {Vertex : Type*}

/-- The finite value of the extended energy on its constructed domain. -/
noncomputable def traceEnergyValue (networks : ℕ → FiniteNetwork Vertex)
    (values : traceEnergyDomain networks) : ℝ :=
  (extendedTraceEnergy networks values).toReal

theorem traceEnergyValue_eq_iSup (networks : ℕ → FiniteNetwork Vertex)
    (values : traceEnergyDomain networks) :
    traceEnergyValue networks values = ⨆ level, (networks level).energy values := by
  simp only [traceEnergyValue, extendedTraceEnergy,
    ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (FiniteNetwork.energy_nonneg _ _)]

theorem finite_energy_tendsto_traceEnergyValue (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (values : traceEnergyDomain networks) :
    Tendsto (fun level => (networks level).energy values) atTop
      (𝓝 (traceEnergyValue networks values)) := by
  rw [traceEnergyValue_eq_iSup]
  obtain ⟨bound, boundValid⟩ := values.property
  exact tendsto_atTop_ciSup (energyIncreasing values) ⟨bound, by
    rintro _ ⟨level, rfl⟩
    exact boundValid level⟩

/-- Increasing compatible finite quadratic energies construct a quadratic form.
The domain is the concrete bounded-energy submodule, with infinity outside it. -/
noncomputable def limitTraceQuadraticForm (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values)) :
    QuadraticForm ℝ (traceEnergyDomain networks) :=
  QuadraticMap.ofPolar (traceEnergyValue networks)
    (by
      intro scalar values
      have scaledLimit := finite_energy_tendsto_traceEnergyValue networks energyIncreasing
        (scalar • values)
      have originalLimit := finite_energy_tendsto_traceEnergyValue networks energyIncreasing values
      apply tendsto_nhds_unique scaledLimit
      simpa only [Submodule.coe_smul, FiniteNetwork.energy_smul, smul_eq_mul, pow_two]
        using originalLimit.const_mul (scalar * scalar))
    (by
      intro first second third
      have finitePolarLimit (left right : traceEnergyDomain networks) :
          Tendsto (fun level => QuadraticMap.polar (networks level).energy
            (left : Vertex → ℝ) (right : Vertex → ℝ)) atTop
            (𝓝 (QuadraticMap.polar (traceEnergyValue networks) left right)) := by
        exact ((finite_energy_tendsto_traceEnergyValue networks energyIncreasing (left + right)).sub
          (finite_energy_tendsto_traceEnergyValue networks energyIncreasing left)).sub
          (finite_energy_tendsto_traceEnergyValue networks energyIncreasing right)
      apply tendsto_nhds_unique (finitePolarLimit (first + second) third)
      have sumLimit := (finitePolarLimit first third).add (finitePolarLimit second third)
      apply sumLimit.congr
      intro level
      exact ((networks level).energyQuadraticForm.polar_add_left
        (first : Vertex → ℝ) (second : Vertex → ℝ) (third : Vertex → ℝ)).symm)
    (by
      intro scalar first second
      have finitePolarLimit (left right : traceEnergyDomain networks) :
          Tendsto (fun level => QuadraticMap.polar (networks level).energy
            (left : Vertex → ℝ) (right : Vertex → ℝ)) atTop
            (𝓝 (QuadraticMap.polar (traceEnergyValue networks) left right)) := by
        exact ((finite_energy_tendsto_traceEnergyValue networks energyIncreasing (left + right)).sub
          (finite_energy_tendsto_traceEnergyValue networks energyIncreasing left)).sub
          (finite_energy_tendsto_traceEnergyValue networks energyIncreasing right)
      apply tendsto_nhds_unique (finitePolarLimit (scalar • first) second)
      have scaledLimit := (finitePolarLimit first second).const_mul scalar
      apply scaledLimit.congr
      intro level
      exact ((networks level).energyQuadraticForm.polar_smul_left scalar
        (first : Vertex → ℝ) (second : Vertex → ℝ)).symm)

theorem limitTraceQuadraticForm_nonneg (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (values : traceEnergyDomain networks) :
    0 ≤ limitTraceQuadraticForm networks energyIncreasing values :=
  ENNReal.toReal_nonneg

end IGS.Sec31
