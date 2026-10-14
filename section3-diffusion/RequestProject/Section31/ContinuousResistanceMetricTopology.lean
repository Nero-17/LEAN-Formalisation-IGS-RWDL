import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

/-! A continuous separating resistance function on a compact space has the
original topology as its ball topology. The proof takes a positive minimum
on the compact complement of an open neighborhood. Combined with the actual
triangle inequality, this constructs a metric with exactly that topology.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31
open Set Filter Topology
variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]

theorem continuous_positive_resistance_open_iff
    (resistance : Space → Space → ℝ)
    (continuous : ∀ first, Continuous (resistance first))
    (self : ∀ point, resistance point point = 0)
    (positive : ∀ first second, first ≠ second → 0 < resistance first second)
    (set : Set Space) :
    IsOpen set ↔ ∀ point ∈ set, ∃ radius > 0, ∀ nearby, resistance point nearby < radius → nearby ∈ set := by
  constructor
  · intro setOpen point pointInSet
    by_cases complementNonempty : setᶜ.Nonempty
    · obtain ⟨minimumPoint, minimumInComplement, minimum⟩ :=
        setOpen.isClosed_compl.isCompact.exists_isMinOn complementNonempty (continuous point).continuousOn
      have distinct : point ≠ minimumPoint := by
        intro equality
        exact minimumInComplement (equality ▸ pointInSet)
      refine ⟨resistance point minimumPoint, positive point minimumPoint distinct, ?_⟩
      intro nearby nearbyClose
      by_contra outside
      exact (not_lt_of_ge (minimum outside)) nearbyClose
    · refine ⟨1, zero_lt_one, fun nearby _ => ?_⟩
      by_contra outside
      exact complementNonempty ⟨nearby, outside⟩
  · intro balls
    rw [isOpen_iff_mem_nhds]
    intro point pointInSet
    obtain ⟨radius, radiusPositive, within⟩ := balls point pointInSet
    have ballOpen : IsOpen {nearby | resistance point nearby < radius} :=
      isOpen_lt (continuous point) continuous_const
    have pointInBall : point ∈ {nearby | resistance point nearby < radius} := by
      change resistance point point < radius
      rw [self]
      exact radiusPositive
    exact Filter.mem_of_superset (ballOpen.mem_nhds pointInBall) (fun nearby membership => within nearby membership)

def continuousResistanceMetric
    (resistance : Space → Space → ℝ)
    (continuous : ∀ first, Continuous (resistance first))
    (self : ∀ point, resistance point point = 0)
    (symmetric : ∀ first second, resistance first second = resistance second first)
    (triangle : ∀ first middle last, resistance first last ≤ resistance first middle + resistance middle last)
    (positive : ∀ first second, first ≠ second → 0 < resistance first second) : MetricSpace Space :=
  MetricSpace.ofDistTopology resistance self symmetric triangle
    (continuous_positive_resistance_open_iff resistance continuous self positive)
    (fun first second zero => by
      by_contra distinct
      exact (ne_of_gt (positive first second distinct)) zero)

end IGS.Sec31

#print axioms IGS.Sec31.continuous_positive_resistance_open_iff
#print axioms IGS.Sec31.continuousResistanceMetric
