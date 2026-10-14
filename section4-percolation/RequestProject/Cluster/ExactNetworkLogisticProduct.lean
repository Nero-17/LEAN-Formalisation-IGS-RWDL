import RequestProject.Cluster.InfiniteConsequences
import RequestProject.Reduced.ExactLogisticProduct

/-! The displayed rational logistic inequality concerns the actual
compatible independent-tree electrical networks at every generation.
The second moment is transported through the proved resistance law,
along with the already identified first and inverse moments. -/

open MeasureTheory
noncomputable section
namespace Cluster
open Reduced
variable {pd ps : ℝ}

theorem nested_network_mean_square_resistance
    (diamondNonnegative : 0 ≤ pd) (seriesNonnegative : 0 ≤ ps)
    (sumOne : ps + pd = 1) (generation : ℕ) :
    (∫ tree, ((treeNetwork generation (nestedTree generation tree)).effRes.toReal) ^ 2
      ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) =
        E2 pd ps generation := by
  unfold E2
  rw [← nested_network_resistance_law diamondNonnegative seriesNonnegative sumOne generation,
    integral_map (measurable_nested_network_resistance generation).aemeasurable (by fun_prop)]

theorem nested_network_logistic_product_exact_rational
    (diamondNonnegative : 0 ≤ pd) (seriesNonnegative : 0 ≤ ps)
    (sumOne : ps + pd = 1) (generation : ℕ) :
    (∫ tree, (treeNetwork (generation + 1) (nestedTree (generation + 1) tree)).effRes.toReal
      ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) *
      (∫ tree, ((treeNetwork (generation + 1) (nestedTree (generation + 1) tree)).effRes.toReal)⁻¹
        ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) ≤
    ((2 - pd) * (1 + pd) / 2) *
      ((∫ tree, (treeNetwork generation (nestedTree generation tree)).effRes.toReal
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) *
        (∫ tree, ((treeNetwork generation (nestedTree generation tree)).effRes.toReal)⁻¹
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne)) -
    ((2 - pd) * (1 + pd) / 2) *
      ((∫ tree, (treeNetwork generation (nestedTree generation tree)).effRes.toReal
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) *
        (∫ tree, ((treeNetwork generation (nestedTree generation tree)).effRes.toReal)⁻¹
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) - 1) ^ 2 /
      ((∫ tree, ((treeNetwork generation (nestedTree generation tree)).effRes.toReal) ^ 2
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) *
        (∫ tree, ((treeNetwork generation (nestedTree generation tree)).effRes.toReal)⁻¹
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) /
        (∫ tree, (treeNetwork generation (nestedTree generation tree)).effRes.toReal
          ∂nestedTreeMeasure pd ps diamondNonnegative seriesNonnegative sumOne) - 1) := by
  simpa only [nested_network_mean_resistance, nested_network_mean_inverse_resistance,
    nested_network_mean_square_resistance] using
      logistic_product_exact_rational diamondNonnegative seriesNonnegative sumOne generation

end Cluster
end

#print axioms Cluster.nested_network_mean_square_resistance
#print axioms Cluster.nested_network_logistic_product_exact_rational
