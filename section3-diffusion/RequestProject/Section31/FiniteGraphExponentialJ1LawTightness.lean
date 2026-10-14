import RequestProject.Section31.FiniteGraphExponentialJ1PathLaw
import RequestProject.Section31.J1FiniteJumpCompactCover

/-! Each actual finite graph exponential-clock law is tight in the genuine
J1 metric. The proof uses its explicit finite-jump representation and a
countable family of compact parameter images, without completeness of D. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology
set_option maxHeartbeats 5000000

abbrev FiniteJumpVertexParameters (Vertex : Type) :=
  Σ count : ℕ, (Fin (count + 1) → Vertex) × Vertex × ℕ

def finiteJumpVertexCompactSet {Vertex : Type} {State : Type*}
    [MetricSpace State] (embedding : Vertex → State) (parameters : FiniteJumpVertexParameters Vertex) :
    Set (UnitCadlagJ1Path State) :=
  Set.range (fun knots : separatedJumpKnots parameters.1 (1 / (parameters.2.2.2 + 1 : ℝ)) =>
    finiteEndpointCadlagJ1Path knots.val (fun index => embedding (parameters.2.1 index))
      (embedding parameters.2.2.1))

theorem finiteJumpVertexCompactSet_isCompact {Vertex : Type} {State : Type*}
    [MetricSpace State] [BoundedSpace State] (embedding : Vertex → State)
    (parameters : FiniteJumpVertexParameters Vertex) :
    IsCompact (finiteJumpVertexCompactSet embedding parameters) :=
  finiteEndpointCadlagJ1Path_separated_range_isCompact _ _ _ _ (by positivity)

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance exponentialJ1TightStateBoundedSpace : BoundedSpace State :=
  ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteGraphExponentialJ1Law_isTight
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (horizon : ℝ) (horizonPositive : 0 < horizon) :
    IsTightMeasureSet {(finiteGraphExponentialJ1Law graph degreePositive initial embedding horizon horizonPositive :
      Measure (UnitCadlagJ1Path State))} := by
  classical
  let family : Set (Set (UnitCadlagJ1Path State)) := Set.range (finiteJumpVertexCompactSet embedding)
  have familyCountable : family.Countable := Set.countable_range _
  have compact : ∀ set ∈ family, IsCompact set := by
    rintro _ ⟨parameters, rfl⟩
    exact finiteJumpVertexCompactSet_isCompact embedding parameters
  have sampleCapture : ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial,
      ∃ set ∈ family, exponentialHoldingJ1Sample embedding horizon horizonPositive sample ∈ set := by
    filter_upwards [finiteGraphExponentialSampleLaw_clock_regular graph degreePositive initial]
      with sample regular
    obtain ⟨count, knots, increasing, interior, representation⟩ :=
      holdingTimePath_finite_interior_jump_representation (fun index => embedding (sample.1 index))
        sample.2 regular.1 regular.2 horizon horizonPositive
    obtain ⟨grid, separated⟩ := interiorOrderedKnots_mem_some_separated count ⟨knots, increasing, interior⟩
    let parameters : FiniteJumpVertexParameters Vertex :=
      ⟨count, (fun index => sample.1 index.val), sample.1 (holdingJumpIndex sample.2 horizon), grid⟩
    refine ⟨finiteJumpVertexCompactSet embedding parameters, Set.mem_range_self parameters, ?_⟩
    refine ⟨⟨knots, separated⟩, ?_⟩
    apply Subtype.ext
    have functions :
        (finiteEndpointCadlagJ1Path knots (fun index : Fin (count + 1) => embedding (sample.1 index.val))
          (embedding (sample.1 (holdingJumpIndex sample.2 horizon)))).val.toFun =
            (exponentialHoldingJ1Sample embedding horizon horizonPositive sample).val.toFun := by
      funext point
      simp only [exponentialHoldingJ1Sample, dif_pos regular, unitHoldingCadlagPath,
        finiteEndpointCadlagJ1Path]
      change finiteEndpointJumpFunction knots (fun index : Fin (count + 1) => embedding (sample.1 index.val))
        (embedding (sample.1 (holdingJumpIndex sample.2 horizon))) point =
          holdingTimePath (fun index => embedding (sample.1 index)) sample.2 (horizon * point.val)
      by_cases terminal : point.val = 1
      · simp only [finiteEndpointJumpFunction, if_pos terminal, terminal, mul_one, holdingTimePath]
      · simp only [finiteEndpointJumpFunction, if_neg terminal]
        exact (representation point (lt_of_le_of_ne point.property.2 terminal)).symm
    have reconstruct (path : J1Function UnitJ1Time State) : J1Function.mk path.toFun = path := by
      cases path
      rfl
    exact (reconstruct _).symm.trans ((congrArg J1Function.mk functions).trans (reconstruct _))
  have captureMeasurable : MeasurableSet {path : UnitCadlagJ1Path State | ∃ set ∈ family, path ∈ set} := by
    have equality : {path : UnitCadlagJ1Path State | ∃ set ∈ family, path ∈ set} =
        ⋃ parameters : FiniteJumpVertexParameters Vertex, finiteJumpVertexCompactSet embedding parameters := by
      ext path
      simp only [family, Set.mem_setOf_eq, Set.mem_range, Set.mem_iUnion]
      aesop
    rw [equality]
    exact MeasurableSet.iUnion (fun parameters => (finiteJumpVertexCompactSet_isCompact embedding parameters).isClosed.measurableSet)
  apply isTight_singleton_of_countable_compact_capture _ family familyCountable compact
  change ∀ᵐ path ∂(finiteGraphExponentialSampleLaw graph degreePositive initial).map
      (exponentialHoldingJ1Sample embedding horizon horizonPositive), ∃ set ∈ family, path ∈ set
  exact (ae_map_iff (exponentialHoldingJ1Sample_aemeasurable graph degreePositive initial embedding horizon horizonPositive)
    captureMeasurable).mpr sampleCapture

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.finiteJumpVertexCompactSet_isCompact
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law_isTight
