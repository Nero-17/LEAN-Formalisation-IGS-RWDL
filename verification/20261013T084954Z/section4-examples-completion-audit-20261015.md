# Section 4, examples, tables and abstract: completion audit

Audit continuation observed by the parent at **2026-10-15 02:23:13 UTC**. This is the same continuous research round `20261013T084954Z`. The 02:19 cloud readback is a completed archival checkpoint, not a research-round termination or a user-away interval. No new round number, artificial gap or final end time is assigned here.

This audit reads the actual manuscript and Lean statements. No Lean compilation or mathematical-source changes were made during its initial inspection. Parent subsequently authorised the finite-matrix numerical bridge identified below; its compilation evidence will be appended separately. Historical conjectures remain conjectures.

## Evidence baseline

- Manuscript: `work/IGS-RWDL-LEAN/paper-corrections/AIM.corrected.tex`, including the adopted true-flower/DHL distinction and the true-flower example.
- Integrated required endpoint: `section3-diffusion/RequestProject/RWDLActualPaper.lean`, SHA256 `d61980ef514532a88cb0bcb06f0fb2f61a4ce7a209cc7dda4b87cb9726804bef`; whole-file exit 0, unchanged source, 58 standard-axiom audits, finished 02:00:28.368839 UTC, immutable log SHA256 `cda388fda6523b2c44ba6a28751cacd06ab9788fb5d635e620e975ef9391819f`.
- Final prior common closure: `verification/20261013T084954Z/integration-1150.json`, 1150 verified modules / 947 targets / changed sources `[]`; final verifier report SHA256 `29e7b078bbd36a0bcfae0d700bd26a3c371ba4627a342c2118de790a4737fd1a`.
- A file being present in the snapshot hash table is **not** proof it occurs in `verified_modules`. This distinction detects the genuine numerical closure gap below.

All paths below are relative to `work/IGS-RWDL-LEAN`, unless prefixed with `work/current-round`.

## Completion update at 02:38:09.992402 UTC

The finite numerical gap found in this audit is now **closed locally** by the new Outlook.FourColourMeanSpectrum actual-matrix bridge: whole-file exit0, source unchanged, six standard-axiom audits. Current source SHA256 60387ef6443f1b9e250ed0c0668e4abba825b69e650a684008e050ac9df7b07c; immutable log SHA256 407e5d231d17a225f328464a55516afe427832df2ac0cbd51f6eff07db23b6cb. The prior 1150 common closure is historical evidence; a new umbrella import/check and fresh common closure are still required to incorporate this module. Random-geometric interpretations remain conjectural. The main findings below record the state at initial inspection and explain why this work was necessary.

## Main findings

1. The actual all-generation Section 4 resistance-process reduction, quenched/annealed exponent, positive critical exponent, rational moment inequality and exclusion of nonzero deterministic normalised limits have actual network endpoints. They are not merely scalar recursion implications.
2. The required numerical assertion about the actual four-colour mass matrix has a **completion gap**: `Outlook.EigenM` and `Outlook.Dimensions` are present as source, but neither occurs in the prior 1150 verified-module closure. The latter also defines its degree ratio with old `EN`. A new bridge should compile unchanged `EigenM`, connect its spectrum to the accepted actual `meanLiveMass`, and combine it with the accepted **corrected** boundary spectrum. No old-EN theorem should be transferred to the corrected matrix.
3. The failed optional `Outlook.CorrectedSpectrumAudit` is not itself needed for the manuscript's matrix eigenvalues. Its extra trace differences, deletion of an old eigenvalue, two-step directional asymmetry and named formal ratio are mostly diagnostic consequences. The required corrected boundary spectral-radius theorem is already in `CorrectedSpectrum`, verified as a dependency of `FourColourOrientationSpectrum` in the 1150 closure. Repairing that optional wrapper alone would not establish a new random-geometric theorem.
4. The random-cluster row of `tab:dimensions` has a genuine status mismatch: **Box 1.8993, degree 1.8993 and resistance 0.8124 are not starred**, whereas the Outlook explicitly describes their geometric interpretation as suggested/formal scaling. The existing stars on walk/spectral/Brownian entries do not cover these first three cells.
5. The true flower is defined for `1 <= u <= v`, `u+v >= 3`, but the manuscript immediately restricts metric results to `2 <= u <= v`. The actual proved flower consumer requires both lengths at least 2. Thus there is **no current theorem asserting the transfractal u=1 case**, and no need to manufacture such a theorem to complete the stated fractal example. The broader sentence that a unified formula covers all EIGS needs its standing scope made explicit.

## Abstract and introduction

| Manuscript claim | Actual support and limit |
|---|---|
| Abstract lines 92-94: rescaled walks, limiting diffusion/Brownian, degree correction | Required umbrella imports actual same-family physical-Poisson weak-law/tightness, original degree correction, heat estimates and RF identification. General driver `EIGSOriginalDegreeFullHeatPhysicalOfRules.exists_xiSameNativeOriginalDegreeCorrectedFullHeatPhysical_of_rules` takes actual connected/loopless/unique/nonadjacent/distance-positive rules and primitive degree. Figure 3 and the two explicit degree-rate-one examples have separate actual consumers. This is a broad class under standing hypotheses, not every nonprimitive or degree-rate-one system. RF identification is conditional on resistance rate > 1. |
| Abstract line 95: solve DHL cluster open problem; suggests AO failure | Supported for existence/positivity of the actual unit-resistance quenched exponent. `suggests` correctly leaves natural random-cluster Brownian/spectral conclusions conjectural. It does not prove AO failure for the natural Brownian motion. |
| Abstract line 96: Sections 2-4 formalised | Needs to be read with the later explicit scope disclaimer, rather than as all source files compile or all Outlook conjectures are proved. The finite-matrix numerical gap identified here should be closed before repeating the numerical part as verified. |
| Introduction line 181-182 mentions Cayley F2, Vicsek and flowers as breadth examples | These are context/external examples, not entries in the actual-example endpoint table. No new actual F2 or Vicsek driver was found in the required umbrella, so their mention cannot support a claim that every named model received an actual Lean specialisation. |
| Lines 802-806: alpha approximately 0.5631, hence resistance dimension approximately 0.8124, cluster becomes Brownian type | The actual theorem gives alpha > 0 and logR/n convergence. No strict numerical enclosure for alpha=0.5631, natural graph-distance growth or random RF identification follows from that theorem alone. These sentences should say numerical estimate/formal prediction and motivate the subsequent Brownian conjecture, rather than announce a proved change of random-geometric regime. |
| Lines 708-714: infinity convention and unified formula | Degree-rate-one is represented by a bounded-degree convention, not a real expression log(mu)/log(1). Two actual bounded-degree rule families are proved. The text must retain the standing hypotheses; no theorem for arbitrary reducible degree matrices or every degree-rate-one EIGS is supplied by these examples. |

The separate `tab:lean` is stale in another direction: it lists GHP/GHPS, resistance-form theory, Azuma/Aldous etc. as inputs, whereas many actual bridges were subsequently proved internally. This is an exposition/scope-documentation inconsistency, not evidence of a failed current theorem. Its Section 4 phrase “the exponent 1.8993” must explicitly mean a **formal logarithmic ratio of finite mean-matrix spectral radii**, not actual random Box/degree dimension.

## Section 4 precise endpoint correspondence

| Paper label / claim | Lean endpoint | Scope checked |
|---|---|---|
| `prop:dhl_reduction`, whole resistance sequence | `Cluster.nested_reduced_full_process_law`, `Cluster.nested_cluster_full_network_law` in `Cluster/FullProcessLaw.lean:77,107`; `Cluster.nested_cluster_resistance_process` | Equality of measures on the whole sequence, derived from finite restrictions, not just one-time marginal equality. The critical cluster and reduced tree are separately constructed actual networks. |
| `lem:annealed_exponent`, `thm:reduced_quenched_exponent` | `Cluster.nested_network_original_observables_p` in `Cluster/InfiniteConsequences.lean:153` | Only original `0 < p < 1`; actual effRes of compatible nested networks; alpha in [0,log2]; AE logR/n, log expectation/n and expectation(logR)/n have the same limit. |
| critical cluster specialisation and `prop:alpha_pc_positive` | `Cluster.nested_critical_cluster_full_exponent` / `nestedCluster_original_observables` in `Cluster/InfiniteProcess.lean`; `Reduced.alpha_pc_pos` in `Reduced/Positivity.lean:107` | Actual critical-cluster sequence and exact lower bound log((14-4sqrt5)/3)>0. This does not identify alpha numerically to four decimal places. |
| `lem:logistic_product`, exact displayed rational inequality | `Reduced.logistic_product_exact_rational`; `Cluster.nested_network_logistic_product_exact_rational` in `Cluster/ExactNetworkLogisticProduct.lean:25` | Actual network moment, not an assumed moment bound. Zero denominators explicitly covered by the scalar lemma. |
| `lem:uniform_product` | `Cluster.nested_network_uniform_product` in `Cluster/InfiniteConsequences.lean:104` | Uniform expected-resistance/inverse-resistance product for the actual network law. |
| pathwise monotonicity/refinement | `Cluster.Rres_bounds`, `Rres_refinement_bounds`, `nested_network_refinement_bounds` in `Cluster/TreeBounds.lean:43,75,131` | Actual compatible realisations, not independent replacement of the law at each generation. |
| `prop:no_deterministic_limit` | `Cluster.nested_network_no_deterministic_limit`, `nested_critical_cluster_no_deterministic_limit` in `Cluster/InfiniteConsequences.lean:175,194`; `Reduced.no_deterministic_limit` | Distributional convergence against bounded continuous tests to a deterministic c>=0 implies c=0, for scaling>0. Does not rule out nondegenerate random limits or degenerate zero limits. |
| actual four-colour figure and expected matrices | `Outlook.FourColourRuleAudit.meanLiveMass_eq_EM`, `meanLiveBoundary_eq_correctedCriticalEN`; `FourColourTerminalAudit` | Finite PMF outcomes, actual colour/boundary counts and critical matrix identities. These are finite arithmetic/expectation identities, not random geometry. |
| corrected boundary eigenvalue 2 | `Outlook.correctedCriticalEN_usual_spectralRadius`, `correctedCriticalEN_realMatrixSpectralRadius`, `correctedCriticalEN_specRad` | Required corrected source is verified in the 1150 dependency closure. `FourColourOrientationCandidate.actual_orientedMeanBoundary_spectralRadius` also has its accepted four-audit receipt. |
| mass eigenvalue approximately 3.7303, formal exponent approximately 1.8993 | Existing `Outlook.EigenM.specRad_EM`, `lamM_approx`; old `Dimensions` code | **Not yet in the prior verified closure.** New actual-mean bridge authorised; compile and audit exact current source rather than citing source presence. Use corrected boundary matrix throughout. |

The five Section 4 Audit wrappers contribute 12 actual public axiom checks, but are not alone a substitute for the complete dependency closure. The 1150 closure supplies those dependencies. No current Section 4 theorem claims existence of the random natural Brownian motion or the conjectural random spectral dimensions.

## Every worked deterministic example and numerical table row

| Manuscript location | Actual current modules / endpoint | Restrictions and caveats |
|---|---|---|
| `ex:Psi_two_colours` (917), `example:two_colour_1` (1376) | `EIGSTwoColourRuleGraph`, `ResistanceFormula`, `MatrixSpectra`, `DistanceSpectrum`, `ActualSpectralParameters` | Actual graph, Ohm/unit-flow calculation, actual M/N/distance rates; N is demonstrably nonprimitive. Paper-index permutation agrees with displayed N. Canonical rho satisfies the actual quartic and strict (1.1061,1.1062) enclosure. |
| `ex:two-colour-spectral` (3890), Figure3 table row | `EIGSTwoColourOriginalDegreeFullHeatPhysical`; `EIGSTwoColourSameKernelBrownianFullHeat` / Exit; `EIGSTwoColourActualGeometricDimensions`, `ActualHausdorffDimension`; original degree distribution D9 | Actual original occupied-degree-support ordinary limit/limsup, not only log mass/log degree rate. Same actual kernel has finite spectral formula in (1.1159,1.1161) and typical formula in (1.8876,1.8878). These enclosures support approximate displayed numbers, not necessarily unique four-decimal rounding. |
| `ex:uvDHL` (2650), DHL and general DHL table rows | Legacy `EIGSFlower...` graph/rates/degree/cover/H/walk; `EIGSFlowerSameKernelFullHeatExit` | Actual object is u parallel branches each length v, u,v>=2. mu=uv, nu=u, lambda=v, rho=v/u, walk dimension2. Legacy file names are immutable but prose must call this DHL. Supercritical RF/Brownian only v>u; (2,2) DHL critical. |
| unlabelled DHL heat example (3736) | Same DHL actual full-kernel consumer, specialised u=v=2 | Finite-born t^-1/2 and typical t^-1 log^-1-epsilon on same kernel; no RF Brownian identification at rho1. |
| `ex:uvFlower` (2702) | `EIGSUVFlowerModel`, `RuleGeometry`, `RuleSimplicity`, `UnitFlow`, `Fraction`, `RuleResistance`, `MassSpectrum`, `DegreeSpectrum`, `RuleConnectivity`, `DistanceSpectrum`, `CanonicalResistance`, `OriginalDegreeDimension`, `CoveringNumberDimension`, `HausdorffDimension`, `WalkDimension`, `SameKernelFullHeatPhysicalTight` | Genuine two paths of possibly unequal lengths. Both lengths>=2; lambda=min(u,v), mu=u+v, nu2, rho=uv/(u+v), mu*rho=uv. Manuscript u<=v makes lambda=u. Actual fullheat/physical weak+tight/exit scope covers (2,2), while RF/Brownian is gated by u+v<uv. No u1 theorem. |
| Laakso table row | `EIGSLocallyFiniteTableDimensions`, `EIGSLocallyFiniteNumericalPowerHeatExitPhysicalTight`, Bool=false | Literal six-edge actual graph; mu6, nu1, lambda4, rho3, time rate18. Native/diameter standard covering and Hausdorff dimensions and actual admissible expected-exit walk dimension proved. Degree infinity is a locally finite convention, not a theorem that a real-valued degree statistic equals infinity. |
| canonical Xi table row | Same two modules, Bool=true | Literal actual graph; mu6, nu1, lambda3, rho11/4, time rate33/2. Same-kernel all-point pure-power estimates, every-point spectral limit, RF/Brownian, exits and physical Poisson laws/tightness. |
| percolation cluster table row (775) | Actual alpha existence/positivity plus finite mean matrices | **All geometric/spectral numbers remain conjectural interpretations; alpha approximately0.5631 is numerical support, not certified here.** Add stars to the first three cells. Do not promote them by proving a formal quotient only. |

The introductory class-comparison table (193) is contextual comparison with classical fractals, not a list of new formalised Sierpinski-gasket/carpet theorems. The Lean-scope table (837) is a scope statement and should distinguish current actual results from quoted literature and from formal numerical expressions.

## Exact minimum proposed declarations for the genuine required numerical gap

New file `Outlook/FourColourMeanSpectrum.lean`, with fresh namespace `Outlook.FourColourMeanSpectrum`:

1. `actual_mean_mass_spectralRadius`: actual `FourColourRuleAudit.meanLiveMass` has real matrix spectral radius `lamM`.
2. `actual_mean_mass_spectralRadius_approx`: its distance from 3.7303 is < 1e-4, optionally retaining the existing sharper enclosure.
3. `actual_mean_boundary_spectralRadius`: actual `FourColourRuleAudit.meanLiveBoundary` has real matrix spectral radius2, via the corrected matrix only.
4. `actual_mean_logarithmic_ratios_equal`: log(actual mass radius)/log(actual boundary radius) = log(actual mass radius)/log2.
5. `actual_mean_logarithmic_ratio_enclosure`: the latter lies strictly between1.89928 and1.89929 (hence approximately1.8993).

These are finite actual expectation/matrix/numerical theorems. Their statements must not use `Metric.coveringNumber`, Hausdorff dimension or actual random degree support and must not label the ratio as an established random geometry. Copying the elementary logarithm bounds into the new namespace avoids importing `Dimensions` and its old EN route.

## Minimal manuscript status correction (separate patch only)

The adjacent `.patch` changes only:

- three missing stars in the random cluster row: Box1.8993, degree1.8993, resistance0.8124;
- the introductory numerical alpha/formal resistance interpretation, retaining it as numerical prediction and Brownian conjecture;
- the Section4 scope-table phrase to say finite mean-matrix eigenvalues and **formal logarithmic ratio**, rather than actual random dimensions.

No conjecture is promoted to theorem, no previous valid endpoint is retracted, and no frozen manuscript is edited by this audit.

## Best next work

First close the **required finite mean-matrix numerical bridge** with strict whole-file receipts and then include it in the umbrella/fresh common closure. This is a narrow real formalisation gap. In parallel, adopt the status-only patch. Do not spend the next iteration merely repairing optional trace/asymmetry audits, and do not undertake the genuinely open random diffusion/geometric conjectures without a separate mathematical plan and explicit scope decision.

## Inspected-source fingerprints

`json
{
  "source_sha256": {
    "paper-corrections/AIM.corrected.tex": "ff993f6155a76699090ddde089b7b6e7f5c5c73daef24b5ac9713eab9f33dce4",
    "section3-diffusion/RequestProject/RWDLActualPaper.lean": "d61980ef514532a88cb0bcb06f0fb2f61a4ce7a209cc7dda4b87cb9726804bef",
    "section4-percolation/RequestProject/Outlook/CorrectedSpectrum.lean": "6c0927c5f4ebeb93df8db9e74c3f21cd46d7431148b45dd66e3350a97ad273c6",
    "section4-percolation/RequestProject/Outlook/CorrectedSpectrumAudit.lean": "93022812ff9d2a77e173a3ac54a35497522fa64be38757953711d6a0e621c71f",
    "section4-percolation/RequestProject/Outlook/EigenM.lean": "675e7f55e917bc68e436635a2c68302835b1ec738c9240a6248d1d2b349ae64a",
    "section4-percolation/RequestProject/Outlook/Dimensions.lean": "559185e7889ea1be8485a079be2cf702e4352ef712649ce6270ebf0dbd323680",
    "section4-percolation/RequestProject/Outlook/FourColourRuleAudit.lean": "1da16cc99ec9d377fd23be4ae88bf1ef46a949b0ccab76701eac405f2f796255"
  }
}
`

## Required numerical bridge: actual execution

Unchanged legacy Outlook.EigenM was genuinely compiled with whole-file exit 0 at 2026-10-15T02:34:35.371813+00:00 (source SHA256675e7f55e917bc68e436635a2c68302835b1ec738c9240a6248d1d2b349ae64a). As it has no print audits, its receipt remains ccepted=false, udit_lines=[]; this is successful legacy dependency compilation, not ordinary audited acceptance. Its immutable empty diagnostic log SHA256 is e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855. The separate new actual-matrix bridge is being compiled and will only be accepted after whole-file exit0, unchanged source and its own six standard-axiom audits.

## New numerical bridge receipt (verified against actual source and immutable log)

`json
{
  "module": "RequestProject.Outlook.FourColourMeanSpectrum",
  "source": "C:\\Users\\lzysh\\Documents\\Codex\\2026-09-21\\new-chat\\work\\IGS-RWDL-LEAN\\section4-percolation\\RequestProject\\Outlook\\FourColourMeanSpectrum.lean",
  "source_sha256": "60387ef6443f1b9e250ed0c0668e4abba825b69e650a684008e050ac9df7b07c",
  "source_unchanged": true,
  "started_utc": "2026-10-15T02:37:16.533579+00:00",
  "finished_utc": "2026-10-15T02:38:09.992402+00:00",
  "exit_code": 0,
  "accepted": true,
  "log": "C:\\Users\\lzysh\\Documents\\Codex\\2026-09-21\\new-chat\\work\\current-round\\RequestProject_Outlook_FourColourMeanSpectrum-2026-10-15T023716.533579_0000.log",
  "log_sha256": "407e5d231d17a225f328464a55516afe427832df2ac0cbd51f6eff07db23b6cb",
  "latest_log": "C:\\Users\\lzysh\\Documents\\Codex\\2026-09-21\\new-chat\\work\\current-round\\RequestProject_Outlook_FourColourMeanSpectrum.log",
  "audit_lines": [
    "Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius: [propext, Classical.choice, Quot.sound]",
    "Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius_approx: [propext, Classical.choice, Quot.sound]",
    "Outlook.FourColourMeanSpectrum.actual_mean_boundary_spectralRadius: [propext, Classical.choice, Quot.sound]",
    "Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratios_equal: [propext, Classical.choice, Quot.sound]",
    "Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_enclosure: [propext, Classical.choice, Quot.sound]",
    "Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_approx: [propext, Classical.choice, Quot.sound]"
  ]
}
`

The first candidate genuinely failed on a single ENNReal/NNReal coercion in the lower spectral bound; its unaccepted receipt and sorryAx propagation remain preserved. The repair used the actual ENNReal.ofReal_eq_coe_nnreal API and did not change the matrix, spectrum, real logarithm estimates, random model or any prior PASS source. Warnings concern unused trailing tactics in a finite matrix equality; they do not change the successful six-audit result. No optional CorrectedSpectrumAudit repair or new random-geometric claim was made.

## Status patch adopted by parent

The parent applied the three-hunk status correction to the actual manuscript while preserving CRLF, and reported current AIM.corrected.tex SHA256 50debefcb3117414795a4bf77e5b994d3241558c5d285fd497daeb08eb231685. The ff993f fingerprint above is the initial inspected version, not the current manuscript. Adoption JSON and the authoritative minimal patch reside under paper-corrections; this subagent did not apply a second copy. Subsequent archive/publication should record the current50de source.

## Cross-audit definition gap closed: extended resistance

Parent subsequently assigned the full-domain def:psi_Psi interface. New RequestProject.Section2ExtendedResistance now has whole-file exit0/sourceunchanged/9 standard-axiom audits, finished2026-10-15T02:44:45.757004+00:00. Source SHA256b523aebae14c2dc28b3bdcca3e497a1eb806b23471d4c261de7bfc534f933eff; immutable log4a1e142e8b9b43c1cbd27fb98e47827bfe310381575d5dd53892d93fe60f0b6b. The ENNReal definition is zero on the diagonal and the actual unit-flow energy infimum off the diagonal. Actual graph reachability iff existence of unit flow is proved using the reachable-component cut/Kirchhoff divergence, hence top iff disconnected and the finite branch equals ofReal of the prior effRes. It bridges the old RuleSystem renormalisation coordinate without changing prior PASS sources. This is a real full-domain definition repair, not an arbitrary predicate extension; a new umbrella/common closure must still incorporate it. The existing Cluster.TTN extended resistance already served distinct-terminal monochrome networks but did not supply this general coloured, same-point interface.

## Later completion checks in the same active round

The physical closed-cell chain has now passed eight modules/eighteen audits including its finite-born nonatomicity prerequisite. Its current-source and immutable-log table is independently checked in `physical-closed-cell-current-accepted-summary.json` and the sole round REPORT. It establishes the actual descendant closure/address-cylinder image equality, boundary overlap only at coarse terminals, exact Perron cell mass, and uniform all-level mass bounds. No desired mass identity or nonatomicity is assumed in the final actual-rule consumer.

Two further minimal manuscript corrections were adopted by the parent after the status patch: whole-graph terminal resistance is bounded above by the single-cell terminal resistance through Rayleigh comparison, rather than asserted equal; the two-colour resistance-dimension expression uses exact `log rho(Psi) / log 2`, rather than an equality with the rounded value1.1061. Current parent-reported manuscript SHA256 is `52826c4ca2fc15190271973d6e5bc8d13f90a906f30f967445ed7ff357879065`; archive capture must compute the actual current bytes. The preceding fingerprints remain historical inspection checkpoints.

The displayed six-member Figure3 path-selection family requires an actual graph enumeration, independently of the optional failed corrected-spectrum diagnostic. The new `EIGSTwoColourDistanceChoices` candidate source `c441d63f577e5400cd4d9e4248a2fb47bc0182556f902ede4d95d128ecae8b11` enumerates actual simple terminal paths, proves the natural count matrices form exactly the displayed set, and bridges to the established real pathSelectionMatrix. It is currently being compiled; no PASS claim is made before a whole-file unchanged-source receipt.

The actual DHL logarithmic fluctuation/sharpness claim is still a separate open completion item. Four-letter address coding has passed, but retention words, product address law, retained-star geometry, and the final almost-everywhere small-radius consumer must each pass before that claim is marked proved. Generic independent-block and endpoint-cost lemmas do not substitute for the actual geometric endpoint. Whether the original phrase "cannot be improved" additionally requires a sharp heat lower estimate is awaiting the parent's user clarification; this audit does not silently reduce that scope to volume alone. Random-cluster geometric claims retain their conjectural status.
