import RequestProject.NonlinearPerronAudit
import RequestProject.Section2ExtendedResistance
import RequestProject.Section31.EIGSResistanceClosedOrthantContinuity
import RequestProject.Section31.EIGSUniformGeometricBounds
import RequestProject.Section31.EIGSBasicPropertiesOfRules
import RequestProject.Section31.EIGSUniformBirthDegreeGrowth
import RequestProject.Section31.EIGSLocalDimensions
import RequestProject.Section31.EIGSFiniteBornNoAtomsOfRules
import RequestProject.Section31.EIGSPhysicalClosedCell
import RequestProject.Section31.EIGSPhysicalClosedCellBoundsOfRules
import RequestProject.Section31.EIGSPointBoundaryResistance
import RequestProject.Section31.EIGSContinuousProjectionPythagoras
import RequestProject.Section31.IndependentWordBlocks
import RequestProject.Section31.EIGSAddressMeasureUniqueness
import RequestProject.Section31.RenewalPhaseEndpointCost
import RequestProject.Outlook.FourColourMeanSpectrum
import RequestProject.Section2MesoscopicVolume
import RequestProject.Section2MesoscopicResistance
import RequestProject.Section2FixedRadiusResistance
import RequestProject.Section2WalkDimension
import RequestProject.Section2SpectralScaleInequality
import RequestProject.Section31.EIGSActualTerminalResistanceDimension
import RequestProject.Section31.EIGSFixedPairResistanceDimension
import RequestProject.Section31.EIGSActualTerminalCommuteGrowth
import RequestProject.Section31.EIGSActualEinsteinRelationOfRules
import RequestProject.Section31.EIGSOriginalDiameterEinsteinRelationOfRules
import RequestProject.Section31.EIGSActualRecurrenceCriterion
import RequestProject.Section31.EIGSActualRecurrenceSpectralThreshold
import RequestProject.Section31.EIGSCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSDiameterCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSHausdorffDimensionOfRules
import RequestProject.Section31.EIGSDiameterHausdorffDimensionOfRules
import RequestProject.Section31.EIGSOriginalMeasuredGHPSOfRules
import RequestProject.Section31.EIGSOriginalDiameterSubGaussianExitTail
import RequestProject.Section31.ExponentialPoissonProcessCertificate
import RequestProject.Section31.ExponentialPoissonJointIncrements
import RequestProject.Section31.ExponentialPoissonFiniteObservations
import RequestProject.Section31.PoissonCountingProcessTimeScaling
import RequestProject.Section31.FiniteGraphPoissonClockIdentification
import RequestProject.Section31.EIGSOriginalExponentialPhysicalJ1TightnessOfRules
import RequestProject.Section31.EIGSSameNativeNormalizedTrueExitSurvivalOfRules
import RequestProject.Section31.EIGSSameNativeNormalizedMeanExitOfRules
import RequestProject.Section31.EIGSTypicalBallMassUpperAllRadiiOfRules
import RequestProject.Section31.EIGSContinuousKernelGeneralLowerOfRules
import RequestProject.Section31.EIGSResistanceFormSameClosedHunt
import RequestProject.Section31.EIGSOriginalDegreeFullHeatPhysicalOfRules
import RequestProject.Section31.EIGSOriginalFullHeatExitPhysicalTight
import RequestProject.Section31.EIGSTwoColourOriginalDegreeFullHeatPhysical
import RequestProject.Section31.EIGSLocallyFiniteTableDimensions
import RequestProject.Section31.EIGSLocallyFiniteNumericalPowerHeatExitPhysicalTight
import RequestProject.Section31.LogarithmicHeatLowerOfPurePower
import RequestProject.Section31.EIGSFlowerOriginalDegreeDimension
import RequestProject.Section31.EIGSFlowerCoveringNumberDimension
import RequestProject.Section31.EIGSFlowerHausdorffDimension
import RequestProject.Section31.EIGSFlowerWalkDimension
import RequestProject.Section31.EIGSFlowerSameKernelFullHeatExit
import RequestProject.Section31.EIGSUVFlowerOriginalDegreeDimension
import RequestProject.Section31.EIGSUVFlowerCoveringNumberDimension
import RequestProject.Section31.EIGSUVFlowerHausdorffDimension
import RequestProject.Section31.EIGSUVFlowerWalkDimension
import RequestProject.Section31.EIGSUVFlowerSameKernelFullHeatPhysicalTight
import RequestProject.Cluster.NestedReduction
import RequestProject.Cluster.ExactNetworkLogisticProduct
import RequestProject.Reduced.NoLimitAudit
import RequestProject.Reduced.OriginalParametersAudit
import RequestProject.Cluster.TreeBoundsAudit
import RequestProject.Cluster.InfiniteConsequencesAudit
import RequestProject.Cluster.FullProcessLawAudit
import RequestProject.Outlook.FourColourRuleAudit
import RequestProject.Outlook.FourColourTerminalAudit
import RequestProject.Section31.EIGSTwoColourDistanceChoices
import RequestProject.Section31.EIGSTwoColourDisplayedNumerics
import RequestProject.Section31.EIGSTwoColourPsiIterationLimits
import RequestProject.Section31.EIGSActualWalkDimensionLowerBound
import RequestProject.Section31.EIGSFlowerDHL23WalkContrast
import RequestProject.Section31.EIGSDHLAddressLetters
import RequestProject.Section31.EIGSDHLRetentionWords
import RequestProject.Section31.EIGSDHLRetentionWordMass
import RequestProject.Section31.EIGSDHLLetterAddressLaw
import RequestProject.Section31.EIGSDHLRetentionBlockGeometry
import RequestProject.Section31.EIGSDHLRetainedStarBallMass
import RequestProject.Section31.EIGSDHLInfiniteGeometricVolumeLower
import RequestProject.Section31.InfiniteGeometricLogarithmicVolumeLower
import RequestProject.Section31.LogarithmicVolumeExponentOptimality
import RequestProject.Section31.CommonAELogarithmicVolumeLower
import RequestProject.Section31.EIGSDHLLogarithmicVolumeFluctuation
import RequestProject.Section31.EIGSDHLVolumeLogExponentOptimality
import RequestProject.Section31.EIGSDHLCommonAEVolumeOptimality

/-!
# Actual RWDL manuscript integration

This file places the already proved actual-rule consumers in one import
environment. It adds no mathematical hypothesis or replacement process.
Its own whole-file compilation is required to certify compatibility of
the graph families, measure instances and public endpoint declarations.

The label map below follows `paper-corrections/AIM.corrected.tex` after
the adopted flower/DHL definition correction. Legacy `flowerSystem`
means the equal-length, many-branch DHL. `uvFlowerSystem` means the true
two-path flower. The locally finite Boolean selects the literal Laakso
or Canonical Xi rule. None is identified with another family by name.

General main theorems retain their standing assumptions. The explicit
Figure3 and two bounded-degree examples have separate actual consumers;
there is no assertion for every nonprimitive or degree-rate-one system.
The graph recurrence endpoint uses the manuscript's fractional-ball
resistance definition. RF Brownian identification requires resistance
rate greater than one. The true (2,2) flower remains critical.

Section4 random-cluster geometry, natural diffusion and Brownian/spectral
predictions remain conjectural. Only the proved coding, electrical laws,
quenched exponent, rational moment estimates and finite matrix audit are
imported here; the matrix calculations are not a random-geometric theorem.
-/

/- Section2: psi-props, renorm, sdprimitive_eigenpair, Psi_range and
Psi_strong_convergence. Actual rule eigenpairs/iterate limits do not take
their target asymptotic conclusions as assumptions. -/
#print axioms EIGS.RuleSystem.distance_positive_normalized_eigenpair_exists_unique
#print axioms EIGS.RuleSystem.distance_positive_normalized_iterate_limit

/- Definition psi_Psi on its full finite-network domain, including self
resistance and disconnected terminals; the closed-orthant regularization
is the same effective-resistance function, not an unspecified extension. -/
#print axioms EIGS.Network.flow_nonempty_iff_reachable
#print axioms EIGS.Network.extendedEffRes_self
#print axioms EIGS.Network.extendedEffRes_eq_ofReal
#print axioms EIGS.Network.extendedEffRes_eq_top_iff_not_reachable
#print axioms EIGS.RuleSystem.extendedEffRes_eq_toRenormMap
#print axioms EIGS.EIGSData.Psi_regularization_tendsto

/- basic_prop: uniform constants across every initial colour and every
generation, including the finite prefix and the original graph diameter. -/
#print axioms EIGS.xiReplanted_edge_card_spectral_bounds_all_generations
#print axioms EIGS.xiReplanted_vertex_card_spectral_bounds_all_generations
#print axioms EIGS.xiSimpleGraph_terminal_distance_spectral_bounds_all_generations
#print axioms EIGS.xiSimpleGraph_terminal_distance_le_originalDiameter
#print axioms EIGS.xiReplanted_distance_diameter_spectral_bounds_all_generations
#print axioms EIGS.xiSimpleGraph_uniform_birth_degree_spectral_growth

/- Fixed-radius local dimensions are actual simple-graph conclusions.
These previously verified consumers now occur in the public integration. -/
#print axioms EIGS.xiSimpleGraph_fixed_radius_local_mass_dimension_limit
#print axioms EIGS.xiSimpleGraph_fixed_radius_local_resistance_dimension_limit

/- Section2: Reff-asymp-rho and resistance_dimension_formula, including
every fixed distinct pair at any coarse generation (paper1356-1360). -/
#print axioms EIGS.xiSimpleGraph_terminal_resistance_canonical_bounds
#print axioms EIGS.xiSimpleGraph_terminal_resistance_dimension_limit
#print axioms EIGS.xiSimpleGraph_terminal_resistance_original_diameter_limit
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistance_dimension_limit
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistanceDimension_eq

/- Section2: ball_volume_k_born, mesoscopic_Reff_k_born, star/ball exit
scales, commute-time-eigs-asymp, Einstein, MPsiD and walk_dimension_ge_2.
Finite-born/admissible radius windows are retained in these declarations. -/
#check EIGS.xiSimpleGraph_mesoscopic_ball_birth_spectral_volume
#check EIGS.xiSimpleGraph_mesoscopic_ball_birth_spectral_resistance
#check EIGS.xiSimpleGraph_fixed_radius_resistance_spectral_bounds
#print axioms EIGS.xiSimpleGraph_admissible_walk_dimension_limit
#print axioms EIGS.xiSimpleGraph_commute_eq_mass_mul_resistance
#print axioms EIGS.xiSimpleGraph_terminal_commute_canonical_bounds
#print axioms EIGS.xiSimpleGraph_actual_Einstein_relation_of_rules
#print axioms EIGS.xiSimpleGraph_original_diameter_Einstein_relation_of_rules
#print axioms EIGS.EIGSData.distanceSpectralRadius_sq_le_mass_mul_resistance
#print axioms EIGS.xiActualRecurrent_iff_resistanceSpectralRadius_gt_one
#print axioms EIGS.xiActualRecurrent_iff_globalSpectralFormula_lt_two

/- Sections1/3 metric completion, Box/Minkowski and Hausdorff dimensions,
GH_limit_metric, GHP_convergence and sec31_ghps. -/
#print axioms EIGS.xiCompletion_coveringNumber_dimension_of_rules
#print axioms EIGS.xiDiameterCompletion_coveringNumber_dimension_of_rules
#print axioms EIGS.xiCompletion_hausdorff_dimension_of_rules
#print axioms EIGS.xiDiameterCompletion_hausdorff_dimension_of_rules
#print axioms EIGS.exists_xiIdentifiedOriginalMeasuredGHPSPaperClock_of_rules

/- The skeleton is null for the actual limiting measure. Physical cells
are closures of actual descendant vertices; their equality with cylinder
images and their endpoint-only overlap give the complete mass identity. -/
#print axioms EIGS.xiFiniteBorn_singleton_mass_zero_of_rules
#print axioms EIGS.xiFiniteBornSkeleton_mass_zero_of_rules
#print axioms EIGS.xiPhysicalClosedCell_mass_ge_cylinder
#print axioms EIGS.xiPhysicalClosedCell_mass_eq_cylinder_of_rules
#print axioms EIGS.exists_xiPhysicalClosedCell_mass_bounds_of_rules

/- Section3: sec31_one_step_stay, discrete_eld_tightness, genuine whole
Poisson clock (all ordered increments, not merely one-time marginals),
actual independent graph-walk product, literal physical weak laws/tightness. -/
#print axioms EIGS.exists_xiOriginalDiameterSubGaussianExitTail_of_rules
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_poisson_process
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increments_iIndepFun
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_finite_increment_joint_law
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_scaled_poisson_process
#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_independent_walk
#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_scaled_process_laws
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingPhysicalJ1Sample_is_poissonized_walk
#print axioms EIGS.exists_xiOriginalExponentialPhysicalJ1Tightness_of_rules

/- Section3: continuous_stay means true first-exit survival. heat-exit
means a genuine exit-time expectation. heat-volume uses all radii, and
general-lower uses a continuous time-dependent radius. -/
#print axioms EIGS.exists_xiIdentifiedNormalizedTrueExitGlobalRestriction_of_rules
#print axioms EIGS.exists_xiIdentifiedMeanExitGlobalRestriction_of_rules
#print axioms EIGS.xiTypicalBallMassUpperAllRadii_of_rules
#print axioms EIGS.exists_xiContinuousKernelGeneralLower_of_rules

/- Sections3.1-3.3: original closed-form/Hunt identification, actual
original degree statistics, diffusion/Brownian heat and spectral limits,
same kernel/globalLaws/true exits/physical laws, and same-ambient tightness. -/
#print axioms EIGS.exists_xiResistanceForm_same_closed_Hunt_of_rules
#print axioms EIGS.exists_xiPhysicalClosedCell_point_boundary_resistance_bound
#print axioms EIGS.xiContinuousHarmonicProjection_energy_pythagoras
#print axioms EIGS.exists_xiSameNativeOriginalDegreeCorrectedFullHeatPhysical_of_rules
#print axioms EIGS.xiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties_of_physical

/- Actual Figure3 example: Psi_two_colours, two_colour_1 and
two-colour-spectral, including its original Pell degree statistics. -/
#print axioms EIGS.exists_twoColour_original_degree_corrected_same_kernel_Brownian_full_heat_physical

/- Actual Table Laakso/Canonical Xi: bounded degree is the non-scale-free
infinity convention. No real expression log(mu)/log(1) is substituted. -/
#print axioms EIGS.locallyFiniteRuleSystem_table_geometric_dimensions
#print axioms EIGS.locallyFiniteRuleSystem_table_walk_dimension
#print axioms EIGS.exists_locallyFiniteRuleSystem_numerical_same_kernel_power_heat_exit_physical_tight_Brownian

/- Adopted uvDHL example and the unlabelled DHL heat example. The legacy
Flower module names denote the actual equal-length DHL replacement. -/
#print axioms EIGS.flowerSystem_original_degree_dimension
#print axioms EIGS.flowerSystem_native_coveringNumber_dimension
#print axioms EIGS.flowerSystem_diameter_hausdorff_dimension
#print axioms EIGS.flowerSystem_admissible_walk_dimension_limit
#print axioms EIGS.exists_flowerSystem_sameKernel_fullHeat_exit

/- True unequal-path flower: both lengths at least2 for the metric
standing regime, exact numerical dimensions and the original full family.
The actual consumer supplies RF identification exactly when u+v<u*v. -/
#print axioms EIGS.uvFlowerSystem_original_degree_dimension
#print axioms EIGS.uvFlowerSystem_native_coveringNumber_dimension
#print axioms EIGS.uvFlowerSystem_diameter_hausdorff_dimension
#print axioms EIGS.uvFlowerSystem_admissible_walk_dimension_limit
#print axioms EIGS.exists_uvFlowerSystem_same_kernel_full_heat_physical_tight

/- Section4: dhl_reduction and the whole all-generation network coding,
annealed/quenched exponent, uniform_product, exact logistic_product,
alpha_pc_positive and no_deterministic_limit. The five Audit wrappers
above also retain their original precise public endpoint audits. -/
#print axioms Cluster.nested_cluster_resistance_process
#print axioms Cluster.nested_reduced_full_process_law
#print axioms Cluster.nested_cluster_full_network_law
#print axioms Cluster.nested_network_original_observables_p
#print axioms Cluster.nested_network_logistic_product_exact_rational
#print axioms Cluster.nested_network_no_deterministic_limit
#print axioms Cluster.nested_critical_cluster_no_deterministic_limit
#print axioms Reduced.no_deterministic_limit

/- Section4 Outlook: actual finite colour coding and audited matrix
arithmetic only. These checks do not assert conjectural random diffusion. -/
#check Outlook.FourColourRuleAudit.ruleSystem
#check Outlook.FourColourRuleAudit.meanLiveMass_eq_EM
#check Outlook.FourColourRuleAudit.meanLiveBoundary_eq_correctedCriticalEN
#check Cluster.connected_actual_terminal_expectations_equal

/- These are spectra and rigorous numerical enclosures of actual expected
matrices. Their logarithmic ratio is not a random-geometric dimension. -/
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius_approx
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_boundary_spectralRadius
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratios_equal
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_enclosure
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_approx

/- Probability tools used by the actual DHL renewal-volume proof below.
The actual consumer also proves the coding law and geometric mass bridge. -/
#print axioms EIGS.independent_trials_failure_bound
#print axioms EIGS.ae_eventually_independent_renewal_phase_success
#print axioms EIGS.independent_word_blocks_joint_law
#print axioms EIGS.xiAddressMeasure_eq_of_marginals
#print axioms EIGS.independent_word_blocks_independent
#print axioms EIGS.ae_eventually_independent_word_block_success
#print axioms EIGS.renewal_word_endpoint_bounds
#print axioms EIGS.eventually_renewal_endpoint_power_cost

/- Completed literal Figure 3 displays and actual mean-exit comparisons.
The unequal-path flower and equal-length DHL remain distinct models. -/
#print axioms EIGS.twoColourSystem_actual_distance_choices_nat
#print axioms EIGS.twoColourSystem_actual_distance_choices_card
#print axioms EIGS.twoColourSystem_pathSelectionMatrix_from_actual_counts
#print axioms EIGS.twoColourSystem_actual_distance_choices
#print axioms EIGS.twoColourResistanceRatio_numeric
#print axioms EIGS.twoColourSystem_resistanceRate_numeric_precise
#print axioms EIGS.twoColourSystem_Psi_first_three_iterates
#print axioms EIGS.twoColourSystem_boxFormula_numeric
#print axioms EIGS.twoColourSystem_resistanceDimensionFormula_numeric
#print axioms EIGS.twoColourSystem_Psi_normalized_iteration_limit
#print axioms EIGS.twoColourSystem_Psi_consecutive_second_coordinate_ratio_limit
#print axioms EIGS.xiSimpleGraph_admissible_walk_dimension_limit_ge_two
#print axioms EIGS.uvFlower23_actual_walk_dimension_gt_two
#print axioms EIGS.dhl23_actual_walk_dimension_eq_two

/- Actual (2,2)-DHL renewal, original address measure, retained stars,
diameter-normalized ball-volume fluctuation and logarithmic optimality.
The last theorem supplies a single full-measure set for all positive
epsilon and every putative upper exponent below one. It asserts volume
upper-bound sharpness only, not heat-kernel logarithmic optimality. -/
#print axioms EIGS.dhlEdgeOfWord_injective
#print axioms EIGS.dhlEdgeOfWord_surjective
#print axioms EIGS.dhlAddressOfLetters_coordinate
#print axioms EIGS.measurable_dhlAddressOfLetters
#print axioms EIGS.dhlEndpointChild_preserves_vertex
#print axioms EIGS.dhlRetentionWord_branch
#print axioms EIGS.dhlRetentionWord_injective
#print axioms EIGS.dhlRetentionWord_preserves_terminal
#print axioms EIGS.dhlGoodRetentionWords_card
#print axioms EIGS.dhlUniformWordLaw
#print axioms EIGS.dhlGoodRetentionWords_mass
#print axioms EIGS.dhlLetters_ae_eventually_retention_phase
#print axioms EIGS.dhlUniformWord_map_edge
#print axioms EIGS.dhlMass_edgeLaw_uniform
#print axioms EIGS.dhlLetters_coordinate_law
#print axioms EIGS.dhlLetters_map_addressMeasure
#print axioms EIGS.dhlAddressOfLetters_block_descendant
#print axioms EIGS.dhlLetters_retention_block_incident
#print axioms EIGS.dhlVertexIncidence_forward
#print axioms EIGS.dhlVertexIncidence_forward_lower
#print axioms EIGS.exists_dhlRetainedStarBallMassLower
#print axioms EIGS.exists_dhl_ae_infinite_geometric_volume_lower
#print axioms IGS.Sec31.infinite_geometric_volume_lower_logarithmic
#print axioms IGS.Sec31.logarithmic_volume_lower_excludes_smaller_exponent
#print axioms IGS.Sec31.ae_all_logarithmic_volume_lower
#print axioms EIGS.dhl_actual_diameter_logarithmic_volume_fluctuation
#print axioms EIGS.dhl_actual_diameter_volume_log_exponent_optimal
#print axioms EIGS.dhl_actual_diameter_common_ae_volume_optimality
