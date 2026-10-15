# Adopted Section 4 corrections

The original arXiv manuscript remains untouched at `work/paper/AIM.tex`; the original rule raster remains `work/paper/figure/random_DHL.png`.

`AIM.matrix-only.tex` preserves the previously adopted three-entry green boundary correction, SHA256 365455de0d99316eab851d3d4eb10091459231d14c8539962aa0cd352a7d5874. Its original patch is `green-degree.patch`.

The user subsequently explicitly adopted the verified endpoint-orientation correction. The active `AIM.corrected.tex` now also applies four boundary entries (moving the red-minus and blue-minus green coefficients into the green-plus column), replaces the old raster reference with the native vector rule figure `figure/random_DHL.oriented.tex`, and explicitly states that a green arrow points from its active to its inactive terminal. `endpoint-orientation.patch` records the exact change from the preserved matrix-only manuscript. `orientation-adoption.json` records exact artifact hashes and paths.

The vector figure is generated from the exhaustively checked 21-outcome table. It reverses eight green arrows in seven red/blue outcomes and keeps every colour, probability and green-parent outcome. The figure source is copied to `work/paper/figure/random_DHL.oriented.tex` so the active manuscript can be compiled from the existing original asset directory. A standalone `figure/random_DHL.oriented.preview.tex` compiled successfully with the desktop editor's built-in compiler after adoption. No claim of whole-manuscript compilation is made by that figure check.

The adopted local theorem source retains its historical name `FourColourOrientationCandidate.lean` and its frozen SHA256 076FF9FC7C4C7F40DB053E9BCB1922F71AA35D1C83007B0360DF563191176B04. Whole-file Lean exit0 and nine standard-only audits verify actual finite Reachable classification, the state table under actual conditional measures, and actual graph means. The earlier `Outlook.correctedCriticalEN` and its spectral proof describe the matrix-only version and remain frozen for traceability; they must not be silently treated as the new orientation matrix. The adopted matrix is `Outlook.FourColourOrientationCandidate.candidateBoundaryMatrix Reduced.pc`.

The original-rule conditional probability audit and literal-forward two-generation labelled-terminal law obstruction remain valid in their scopes. Full-generation identification of the now-adopted oriented coding with the actual retained cluster, the new matrix's spectrum and downstream dimension claims remain separate proof tasks. The manuscript's unchanged mathematical claims are not automatically certified by this local edit.

## Flower and DHL terminology (user adopted, 2026-10-15)

The active manuscript now defines both families immediately after the EIGS definition. A `(u,v)`-flower replaces each edge by **two** internally vertex-disjoint paths of lengths `u` and `v`. In this paper, a `(u,v)`-DHL replaces each edge by **u** internally vertex-disjoint paths, **each of length v**. The dimension table, worked example, regime illustration and relevant captions now use DHL for the latter model; their calculations are unchanged. Historical asset names and internal labels are retained. See `flower-dhl-definition.patch` and `flower-dhl-definition-adoption.json` for the exact edit and primary sources.

Existing audited Lean modules whose identifiers contain `Flower` construct the equal-length **DHL** family. Their proofs remain valid for that mathematical object, with original hashes preserved; they are not a formalization of unequal-length flowers. The latter requires its own actual rule graph and consumers.
