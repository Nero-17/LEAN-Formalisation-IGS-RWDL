# Current Overleaf / Lean correspondence audit — 2026-10-16

## Verdict

**Do not describe the current Overleaf manuscript as completely, literally, unconditionally formalized.** The major graph, diffusion and percolation conclusions have actual-model Lean support under the explicit rule hypotheses and separately proved example scopes. That is stronger than generic conditional ingredients, but it is not a certificate for every assertion and every newly written proof step in the current manuscript.

The present audit identifies a rule-connectivity ambiguity, an overbroad “all EIGS” sentence, an example invoking an inapplicable general theorem despite having its own specialized proof, and four groups of explicit statement/proof bridges not located in the inspected formal interfaces. Several rewritten arguments have a different formal proof of the same conclusion. These distinctions supersede any reading of the previous “no remaining gaps” wording as a literal full-text certificate. The connectivity ambiguity also occurs in the earlier manuscript; it is not solely a consequence of the latest rewrite.

## Delivery and exact comparison boundary

- GitHub `main` was fast-forwarded, without force, from `85bf1f7ab10c795d1ae56afd7fa235544a0dc546` to **`02543484699750a3ebf13bdc739a4f665c248d88`**, then read back from the remote. This publishes the previously separate progress branch's results on the default branch.
- Current Overleaf project: <https://www.overleaf.com/project/693c20f05de81e2189bdd159>, fetched commit **`6367f7e0e6f1d4454182fdd9d97ca0081c110896`**. The audit did not overwrite its online edits. The initial audit used `3d5c73a`; a final fetch found two wording changes in §1.4 only, reviewed in [the incremental diff](overleaf-during-audit.diff). Mathematical statements/proofs and line numbering are unchanged; the initial snapshot is retained as `CMP.initial.tex`.
- Current `CMP.tex` SHA256: `f96f3277e0e5649fb364de6f6a67834046ec8308ba7832159648634a2fb9f750`; frozen as [CMP.current.tex](CMP.current.tex).
- Previous audited manuscript SHA256: `b5628096487efaba69cf1244f1f806bde2b3878f08c2626903919d2ac88dc240`; frozen as [CMP.audited-baseline.tex](CMP.audited-baseline.tex). The [diff](manuscript.diff) has 2579 lines.
- All **1272** local Lean source files were compared with GitHub commit `0254348`, ignoring only CRLF/LF differences: **no differences**. See [comparison receipt](published-source-comparison.json).
- `verify_published_snapshot.py` passed the source/log hash and axiom-receipt checks: **1190 shared modules, 815 independently accepted whole files, 1272 inventoried source files**. These counts overlap and are not a percentage of mathematical completion. This check is not a fresh dependency rebuild.
- The newest four-colour graph-law/branching/projective-consistency files are in the recorded passing shared batch, even where they do not have separate whole-file receipts. They are not rejected merely because an older partial audit says a bridge was absent.
- A separate fresh umbrella elaboration passed (exit 0, unchanged source, 135 audits using only the three standard axioms), finishing at 01:30:30 UTC. Its precise outcome is recorded in [umbrella-fresh.json](umbrella-fresh.json); its dependencies are existing compiled dependencies, not a fresh rebuild of all 1190 modules.

## Outstanding literal correspondences

“Not located” below means that this audit did not find a formal declaration/composition with the exact stated domain, object and quantifiers. It is not a proof that no equivalent result can be derived from the library, and it is not a counterexample to the mathematical assertion.

| ID | Current manuscript | What is already formalized | Remaining work before claiming literal coverage |
|---|---|---|---|
| B1 | `lem:sec31_uniform_resolvent`, lines 3332–3396: every `λ>0` | Actual uniform normalized-resolvent convergence for `0<h≤1`, hence directly `λ≥1`; actual uniform semigroup convergence at all times | Export the all-positive-λ extension, for example using semigroup convergence, contraction and a Laplace-tail split. No analytic obstruction was found. |
| B2 | Closed-form proof, lines 3034–3041: exact harmonic trace/Pythagoras for every closed-domain function | Continuous finite-energy Pythagoras, bounded closed-domain finite-born point evaluations, and the closed form | Compose the extended evaluations and harmonic projections to export the exact closed-domain identity/trace minimization. The continuous-core equality alone has a smaller domain. |
| B3 | New `lem:sec33_two_star_cover`, lines 3767–3786 | Finite-vertex two-star separation; arbitrary address-limit separation; physical cell equals cylinder image; actual physical ball-mass bound | Export the set inclusion for every completion point in any specified physical closed cell, with its two closed physical stars and the manuscript metric. The required mass consequence is already proved. |
| B4 | Added uniform birth-factor and spatial collar argument, lines 3828–3910 | Per-vertex finite-born volume theorem; uniform recent-vertex incidence; actual address-collar logarithmic volume theorem | The per-vertex endpoint does not itself export constants uniform over all birth levels. Locate or add that uniform-volume composition and the exact spatial `E_{m,L}` estimate if retaining this literal proof route. The actual typical-volume conclusion has an independent formal address-collar proof. |

Details and exact Lean file/declaration references: [complete 79-entry crosswalk](coverage-map.md), [§3.1 audit](audit-s31.md), [§3.2–3.3 audit](audit-s32-s33.md).

## Manuscript scope and applicability corrections

1. **Explicit rule connectedness.** Lines 406–415 specify finite directed rules and edge uniqueness. Edge canonicality at 590 does not exclude isolated vertices. The general convention for a graph denoted `G` may have intended connectedness for all rules, but the actual Lean consumers explicitly require `∀ colour, (ruleSG system colour).Connected`. A one-colour directed four-cycle with opposite terminals, plus one isolated internal vertex, satisfies the literal edge-canonicality, terminal-distance-two, and primitive degree conditions: its endpoint degree matrix is `[[1,1],[1,1]]`. Yet the rule is disconnected and harmonic minimization is nonunique on the isolated vertex. Explicitly require connected underlying rule graphs. This is an ambiguity/countermodel to the literal hypothesis list, not a disproof under the intended connected-rule interpretation.
2. **“All EIGS” at line 717.** The general theorem assumes the stated rule hypotheses and primitive degree; separate consumers handle the actual nonprimitive two-colour and locally finite examples. These do not establish every reducible/nonprimitive system, or the flower `u=1` metric regime. Restrict the sentence to the proved families.
3. **Figure 3 example at line 4447.** Its degree matrix is formally proved nonprimitive (`twoColourSystem_degree_not_primitive`). The example nevertheless has a specialized actual full-heat/process consumer. Replace the unsupported application of the primitive general theorem by that separate argument; the example's final numerical spectral conclusion is not missing.
4. **Broad background prose.** The random expected-matrix statement at 576 needs the assumptions of the cited random model; it is not an unrestricted theorem of this Lean development. The “most exponents are unchanged without canonicality” sentence at 609 does not specify a mathematical claim precise enough to certify. Qualify these or exclude them explicitly from a formal-completeness statement.

Two minor proof-writing details also remain: use a strict buffer where the recurrence proof places an entire cell inside an open ball; insert the common-realization metric-error margin in the continuous-stay passage. They do not invalidate the independently formalized endpoints. See the section audits for locations.

## Rewritten proof routes versus formalized conclusions

The following new derivations were not found as literal Lean proof routes. Their resulting estimates/theorems do have actual-model formal proofs; calling all their conclusions “unformalized” would be misleading.

| New manuscript route | Located formal route |
|---|---|
| Erlang/gamma-time resolvent powers and Chebyshev for semigroup convergence | Bounded Yosida generation and generator comparison |
| The displayed Azuma chaining presentation | Actual finite exit-tail and physical path-tightness constructions |
| Harmonic-spline `L²` orthogonal projection, Gram bounds and duality for Nash | Address-cell averages, energy errors, and closed-domain two-scale Nash |
| Heat-kernel construction by Hilbert–Schmidt eigenbasis and a uniformly convergent spectral series | Compact continuous semigroup smoothing and Riesz kernel rows |
| The displayed `q(t)-q(2t)` integral identity and an intermediate-time choice | Closed point-evaluation estimates, energy smoothing and Riesz diagonal recurrence |
| Arbitrary-network conditional Jensen for annealed submultiplicativity | Increasing-concave order of the actual recursive resistance laws |
| Shortened direct Markov proof of the quenched exponent; derivative presentation of one product estimate | Expected-log centering and comparison with log-mean; a polynomial closing inequality |

A different formal proof is sufficient to establish a theorem. It is not sufficient to claim that every newly inserted proof line has itself been formalized. The shortest completion strategy is usually to align exposition with the existing formal proof, or add the specific small exports B1–B4, rather than duplicate every alternative argument.

## Confirmed substantive coverage

- The new finite-born point estimate and the nonprimitive incidence/resistance divergence argument both have exact actual-rule Lean counterparts; they are not missing.
- Actual regular closed form, full varying-space Mosco, all-time uniform semigroup convergence, moving-start own-diameter measured GHPS, physical Poisson clocks and the same continuous Hunt family have actual-model consumers.
- Arbitrary-centre true mean exit bounds, strictly positive jointly continuous same-semigroup kernels, finite-born/typical heat exponents, physical cell mass/noatom facts, resistance-form identification in the strict resistance-rate regime, and DHL volume-only logarithmic optimality have corresponding actual results.
- The newer active-terminal four-colour chain covers conditional probabilities, orientation, child independence, full retained/source graph isomorphisms, finite graph laws, projective consistency and the full coupled process law. It goes beyond resistance marginals and offspring counts.
- Section 4's quenched exponent, critical positivity and failure of nonzero deterministic normalization have actual-cluster endpoints. The numerical estimate of the exponent is still numerical evidence, not a rigorous Lean enclosure.
- True two-path flowers and many-parallel-path DHL are distinct supported models. The new table row agrees with the flower rates under `2≤u≤v`. The separate Laakso/canonical-Xi bounded-degree consumers also exist.
- The current §1.4 list of outstanding primitive degree-multiplicity and two locally finite heat examples is stale relative to `0254348`: `primitive_rules_original_degree_dimension` and `exists_locallyFiniteRuleSystem_numerical_same_kernel_power_heat_exit_physical_tight_Brownian` are in the accepted source inventory. Replace that old list with the actual current boundary above; do not replace it by an unqualified “whole paper complete”.

The complete environment inventory contains **79 entries, 71 labelled**, including definitions, assumptions, restatements and the historical conjecture. Three genuinely new named lemmas occur: point evaluation, uniform resolvent, and two-star cover. The two shifted unlabelled entries are not new mathematical results. [inventory.json](inventory.json) contains statement/proof text and change flags; [inventory.txt](inventory.txt) is the compact index. Unchanged statements were compared against the previous actual-endpoint mapping and unchanged source evidence; rewritten proofs received the focused comparisons in the three section reports. This is a whole-manuscript correspondence audit, not an independent reconstruction of every dependency proof.

The rule diagrams and added flower/DHL and reduced-series/diamond TikZ descriptions were inspected for the model distinction and topology. A drawing/rendering pipeline is not a Lean-certified theorem, and no automatic pixel-to-Lean equivalence is claimed.

## Still genuinely open / deliberately outside theorem coverage

The Outlook's random natural-metric dimensions, random diffusion/Brownian construction and spectral-dimension predictions remain conjectural. Heat-kernel logarithmic optimality is not asserted; the proved sharpness concerns the volume exponent. Arbitrary nonprimitive and arbitrary degree-rate-one extensions, and `u=1` transfractal metric results, are not obtained from the supported examples. Classical-fractal comparison tables and external citations are background, not Lean specializations of every cited model. Exploratory files outside the accepted closure are not certified merely by being present in the repository.

## Work record and next actions

Round identifier: `20261016T011112Z`. Source: this Codex RWDL conversation, user authorization to merge latest results to `main` and audit the current Overleaf manuscript. Start: **2026-10-16 01:11:12 UTC / 09:11:12 Asia/Shanghai**. Final time is in `state.json`.

No manuscript or mathematical Lean source was changed during this audit. Publication changes comprise this evidence and current-scope notices. The shared development checkout/index was preserved; the main merge used the already-published branch. Three focused read-only audits were delegated with the requested GPT-6.1 Sol / high settings. Their preliminary four-colour and missing-recursion suspicions were explicitly withdrawn after checking newer sources and focused untruncated text; they are not final findings.

Recommended sequence: explicitly settle connected-rule scope and correct the general-theorem application; export B1–B3 and either export or replace the B4 prose route; align remaining alternate proof routes if literal proof-level coverage is desired; then update §1.4 against the resulting exact snapshot. This audit does not silently modify the paper to make a completion claim true.

Google Drive remains deferred under the user's instruction. All audit evidence is local and published with the GitHub audit; no Drive-upload success is claimed.
