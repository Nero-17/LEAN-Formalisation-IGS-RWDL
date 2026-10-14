import RequestProject.Section31.EIGSActualRecurrenceCriterion
import RequestProject.Section31.EIGSFlowerCanonicalRates

/-! Recurrence of the actual flower graphs, using the original fractional
 eccentricity-ball resistance definition. -/

namespace EIGS
noncomputable section
open scoped Classical

 theorem flowerSystem_actualRecurrent_iff (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    xiActualRecurrent (flowerSystem branches segments) ↔ branches < segments := by
  rw [xiActualRecurrent_iff_resistanceSpectralRadius_gt_one
    (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments),
    flowerSystem_resistanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo]
  have branchesPositive : (0 : ℝ) < branches := by exact_mod_cast (show 0 < branches by omega)
  rw [one_lt_div branchesPositive]
  exact Nat.cast_lt

end
end EIGS

#print axioms EIGS.flowerSystem_actualRecurrent_iff
