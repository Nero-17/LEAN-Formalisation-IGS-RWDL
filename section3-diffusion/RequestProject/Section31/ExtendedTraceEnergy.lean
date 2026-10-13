import RequestProject.Section31.MarkovProperty
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Extended-valued energy and its domain from finite networks

The energy here is constructed from the edge sums of `FiniteNetwork`, rather
than supplied as a field with its desired properties.  Edges retain their
identity, so parallel edges are counted with their multiplicity.  Vertex types
may be infinite: each individual network still has finitely many edges.

The domain is exactly the functions with uniformly bounded finite-level
energies; the energy is infinity outside that domain.  We prove that this
domain is a real vector subspace, normal contractions preserve it and decrease
the extended energy, and the extended energy is lower semicontinuous in the
topology of pointwise convergence.  The final theorem derives an actual
liminf inequality from eventual coarse-energy domination and pointwise
convergence, with no assumed liminf inequality.

These constructions apply to the countable vertex union once the EIGS finite
networks have been embedded into it.  They do not identify the product topology
with weak convergence in the varying L² spaces, construct the EIGS embeddings,
or assert the Hunt-process correspondence.
-/

namespace IGS.Sec31

open Filter Topology
open scoped ENNReal

namespace FiniteNetwork

variable {Vertex : Type*}

/-- Push the endpoints into a common vertex set without losing edge identity. -/
def mapVertices {OtherVertex : Type*} (network : FiniteNetwork Vertex)
    (vertexMap : Vertex → OtherVertex) : FiniteNetwork OtherVertex where
  Edge := network.Edge
  fintypeEdge := network.fintypeEdge
  decEqEdge := network.decEqEdge
  ends := fun edge => (vertexMap (network.ends edge).1, vertexMap (network.ends edge).2)
  cond := network.cond
  cond_pos := network.cond_pos

theorem energy_mapVertices {OtherVertex : Type*} (network : FiniteNetwork Vertex)
    (vertexMap : Vertex → OtherVertex) (values : OtherVertex → ℝ) :
    (network.mapVertices vertexMap).energy values = network.energy (values ∘ vertexMap) := rfl

/-- Finite edge sums are continuous even on an infinite vertex set. -/
theorem energy_continuous_pointwise (network : FiniteNetwork Vertex) :
    Continuous network.energy := by
  unfold energy
  fun_prop

theorem energy_add_le (network : FiniteNetwork Vertex) (first second : Vertex → ℝ) :
    network.energy (first + second) ≤ 2 * network.energy first + 2 * network.energy second := by
  simp only [energy, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun edge _ => ?_
  have conductanceNonnegative := (network.cond_pos edge).le
  nlinarith [sq_nonneg
    (first (network.ends edge).1 - first (network.ends edge).2 -
      (second (network.ends edge).1 - second (network.ends edge).2))]

theorem energy_smul (network : FiniteNetwork Vertex) (scalar : ℝ) (values : Vertex → ℝ) :
    network.energy (scalar • values) = scalar ^ 2 * network.energy values := by
  simp only [energy, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun edge _ => ?_
  ring

end FiniteNetwork

variable {Vertex : Type*}

/-- The supremum in `[0,∞]` is meaningful whether or not the energies are bounded. -/
noncomputable def extendedTraceEnergy (networks : ℕ → FiniteNetwork Vertex)
    (values : Vertex → ℝ) : ℝ≥0∞ :=
  ⨆ level, ENNReal.ofReal ((networks level).energy values)

/-- Membership requires a bound on the actual finite-network quadratic sums. -/
def TraceEnergyFinite (networks : ℕ → FiniteNetwork Vertex) (values : Vertex → ℝ) : Prop :=
  ∃ bound : ℝ, ∀ level, (networks level).energy values ≤ bound

theorem traceEnergyFinite_zero (networks : ℕ → FiniteNetwork Vertex) :
    TraceEnergyFinite networks 0 := by
  refine ⟨0, fun level => ?_⟩
  simp [FiniteNetwork.energy]

theorem traceEnergyFinite_add (networks : ℕ → FiniteNetwork Vertex)
    {first second : Vertex → ℝ} (firstFinite : TraceEnergyFinite networks first)
    (secondFinite : TraceEnergyFinite networks second) :
    TraceEnergyFinite networks (first + second) := by
  obtain ⟨firstBound, firstBoundValid⟩ := firstFinite
  obtain ⟨secondBound, secondBoundValid⟩ := secondFinite
  refine ⟨2 * firstBound + 2 * secondBound, fun level => ?_⟩
  exact ((networks level).energy_add_le first second).trans
    (add_le_add (mul_le_mul_of_nonneg_left (firstBoundValid level) (by norm_num))
      (mul_le_mul_of_nonneg_left (secondBoundValid level) (by norm_num)))

theorem traceEnergyFinite_smul (networks : ℕ → FiniteNetwork Vertex) (scalar : ℝ)
    {values : Vertex → ℝ} (valuesFinite : TraceEnergyFinite networks values) :
    TraceEnergyFinite networks (scalar • values) := by
  obtain ⟨bound, boundValid⟩ := valuesFinite
  refine ⟨scalar ^ 2 * bound, fun level => ?_⟩
  rw [FiniteNetwork.energy_smul]
  exact mul_le_mul_of_nonneg_left (boundValid level) (sq_nonneg scalar)

/-- A constructed vector-space domain, not an assumption that all energies are finite. -/
def traceEnergyDomain (networks : ℕ → FiniteNetwork Vertex) : Submodule ℝ (Vertex → ℝ) where
  carrier := {values | TraceEnergyFinite networks values}
  zero_mem' := traceEnergyFinite_zero networks
  add_mem' := traceEnergyFinite_add networks
  smul_mem' := traceEnergyFinite_smul networks

theorem extendedTraceEnergy_le_of_bound (networks : ℕ → FiniteNetwork Vertex)
    (values : Vertex → ℝ) (bound : ℝ)
    (boundValid : ∀ level, (networks level).energy values ≤ bound) :
    extendedTraceEnergy networks values ≤ ENNReal.ofReal bound :=
  iSup_le fun level => ENNReal.ofReal_le_ofReal (boundValid level)

theorem traceEnergyFinite_iff_extendedTraceEnergy_ne_top
    (networks : ℕ → FiniteNetwork Vertex) (values : Vertex → ℝ) :
    TraceEnergyFinite networks values ↔ extendedTraceEnergy networks values ≠ ∞ := by
  constructor
  · rintro ⟨bound, boundValid⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (extendedTraceEnergy_le_of_bound networks values bound boundValid)
  · intro energyFinite
    refine ⟨(extendedTraceEnergy networks values).toReal, fun level => ?_⟩
    have finiteLevelBound : ENNReal.ofReal ((networks level).energy values) ≤
        extendedTraceEnergy networks values :=
      le_iSup (fun coarseLevel => ENNReal.ofReal ((networks coarseLevel).energy values)) level
    have realBound := ENNReal.toReal_mono energyFinite finiteLevelBound
    simpa [ENNReal.toReal_ofReal (FiniteNetwork.energy_nonneg _ _)] using realBound

theorem extendedTraceEnergy_eq_top_iff (networks : ℕ → FiniteNetwork Vertex)
    (values : Vertex → ℝ) :
    extendedTraceEnergy networks values = ∞ ↔ values ∉ traceEnergyDomain networks := by
  change extendedTraceEnergy networks values = ∞ ↔ ¬ TraceEnergyFinite networks values
  rw [traceEnergyFinite_iff_extendedTraceEnergy_ne_top]
  simp

theorem extendedTraceEnergy_comp_le (networks : ℕ → FiniteNetwork Vertex)
    (contraction : ℝ → ℝ)
    (contractionBound : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (values : Vertex → ℝ) :
    extendedTraceEnergy networks (contraction ∘ values) ≤ extendedTraceEnergy networks values := by
  refine iSup_le fun level => ?_
  exact (ENNReal.ofReal_le_ofReal
    ((networks level).energy_comp_le_of_lipschitz contraction contractionBound values)).trans
    (le_iSup (fun coarseLevel => ENNReal.ofReal ((networks coarseLevel).energy values)) level)

theorem traceEnergyDomain_comp (networks : ℕ → FiniteNetwork Vertex)
    (contraction : ℝ → ℝ)
    (contractionBound : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    {values : Vertex → ℝ} (valuesFinite : values ∈ traceEnergyDomain networks) :
    contraction ∘ values ∈ traceEnergyDomain networks := by
  obtain ⟨bound, boundValid⟩ := valuesFinite
  refine ⟨bound, fun level => ?_⟩
  exact ((networks level).energy_comp_le_of_lipschitz contraction contractionBound values).trans
    (boundValid level)

theorem extendedTraceEnergy_lowerSemicontinuous (networks : ℕ → FiniteNetwork Vertex) :
    LowerSemicontinuous (extendedTraceEnergy networks) := by
  apply lowerSemicontinuous_iSup
  intro level
  exact (ENNReal.continuous_ofReal.comp
    (networks level).energy_continuous_pointwise).lowerSemicontinuous

theorem extendedTraceEnergy_isClosed_sublevel (networks : ℕ → FiniteNetwork Vertex)
    (bound : ℝ≥0∞) :
    IsClosed {values | extendedTraceEnergy networks values ≤ bound} :=
  (extendedTraceEnergy_lowerSemicontinuous networks).isClosed_preimage bound

/-- The coarse finite energies determine a liminf bound without assuming that bound.
The domination can be established from trace minimisation.  The convergence here
is genuinely pointwise, and is not silently substituted for varying-space weak L² convergence. -/
theorem extendedTraceEnergy_le_liminf
    (networks : ℕ → FiniteNetwork Vertex) (discreteEnergy : ℕ → (Vertex → ℝ) → ℝ≥0∞)
    (approximation : ℕ → Vertex → ℝ) (values : Vertex → ℝ)
    (pointwiseConvergence : ∀ vertex,
      Tendsto (fun index => approximation index vertex) atTop (𝓝 (values vertex)))
    (coarseDomination : ∀ level, ∀ᶠ index in atTop,
      ENNReal.ofReal ((networks level).energy (approximation index)) ≤
        discreteEnergy index (approximation index)) :
    extendedTraceEnergy networks values ≤
      liminf (fun index => discreteEnergy index (approximation index)) atTop := by
  refine iSup_le fun level => ?_
  have energyConvergence : Tendsto
      (fun index => ENNReal.ofReal ((networks level).energy (approximation index)))
      atTop (𝓝 (ENNReal.ofReal ((networks level).energy values))) :=
    (ENNReal.continuous_ofReal.comp
      (networks level).energy_continuous_pointwise).continuousAt.tendsto.comp
      (tendsto_pi_nhds.2 pointwiseConvergence)
  rw [← energyConvergence.liminf_eq]
  exact liminf_le_liminf (coarseDomination level)

/-- For an increasing family, coarse domination is proved directly from the
level ordering; it is not another liminf hypothesis. -/
theorem extendedTraceEnergy_le_liminf_of_increasing
    (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (approximation : ℕ → Vertex → ℝ) (values : Vertex → ℝ)
    (pointwiseConvergence : ∀ vertex,
      Tendsto (fun index => approximation index vertex) atTop (𝓝 (values vertex))) :
    extendedTraceEnergy networks values ≤
      liminf (fun index => ENNReal.ofReal ((networks index).energy (approximation index))) atTop := by
  apply extendedTraceEnergy_le_liminf networks
    (fun index values => ENNReal.ofReal ((networks index).energy values))
    approximation values pointwiseConvergence
  intro level
  filter_upwards [eventually_ge_atTop level] with index indexAfterLevel
  exact ENNReal.ofReal_le_ofReal (energyIncreasing (approximation index) indexAfterLevel)

/-- A finite liminf forces membership in the constructed energy domain. -/
theorem traceEnergyDomain_mem_of_finite_liminf
    (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (approximation : ℕ → Vertex → ℝ) (values : Vertex → ℝ)
    (pointwiseConvergence : ∀ vertex,
      Tendsto (fun index => approximation index vertex) atTop (𝓝 (values vertex)))
    (finiteLiminf :
      liminf (fun index => ENNReal.ofReal ((networks index).energy (approximation index))) atTop ≠ ∞) :
    values ∈ traceEnergyDomain networks := by
  apply (traceEnergyFinite_iff_extendedTraceEnergy_ne_top networks values).2
  exact ne_top_of_le_ne_top finiteLiminf
    (extendedTraceEnergy_le_liminf_of_increasing networks energyIncreasing
      approximation values pointwiseConvergence)

end IGS.Sec31
