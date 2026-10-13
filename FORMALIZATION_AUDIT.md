# Current formalization audit

Snapshot UTC: 2026-10-13T23:27:39.497737+00:00

Full-paper completion is **not** claimed. A clean axiom list establishes the stated theorem, not the realization of unproved hypotheses. Generic criteria and draft consumers are not substitutes for an actual-model proof.

## Verification scope

The last completed shared-dependency batch passed 545 modules, with no source changes. Its immutable report SHA256 is `c75281dbb70120997bf6d5a5de2e1f03d14d6f9bb7a62390de27d240c20c0210`. The published copies of all 545 checked source files match that report. Later independent receipts are separate; no full-source green build is claimed.

The portable independent manifest contains 220 whole-file receipts and 804 printed audits. Counts are evidence inventory, not a completion percentage.

## Accepted later milestones

| File | Source SHA256 | Log SHA256 | Audits |
| --- | --- | --- | --- |
| [EIGSFiniteHorizonPathTightnessOfRules](section3-diffusion/RequestProject/Section31/EIGSFiniteHorizonPathTightnessOfRules.lean) | `87b8f489cf02c0ef5ef0e9a85585773cebe74d5b7d714257fefe86200f775f13` | `ac2842002ae15055e2256b6da180c5b65762896169143a4729e37dba07a1c014` | 1 |
| [EIGSFiniteHorizonContinuousSubsequenceOfRules](section3-diffusion/RequestProject/Section31/EIGSFiniteHorizonContinuousSubsequenceOfRules.lean) | `39edbe2cc340f1ba01120e76c602769c83f907e0ed165f38660ba4843574c34d` | `ce16570ae154a5d50b7fd643a5a2f8c600df9dce13a942a43f708c83ce2b8793` | 1 |
| [EIGSContinuousSemigroupOfRules](section3-diffusion/RequestProject/Section31/EIGSContinuousSemigroupOfRules.lean) | `39c10a3a04116311063de6f474bac9ab91f0d63a7a9c95628c02ff73c8947829` | `e6b4aee6c8011e267f2d29ee4ea58d63bf6c9be520bacbb1091bdb76b8dd6de6` | 3 |
| [EIGSContinuousSemigroupMarkovOfRules](section3-diffusion/RequestProject/Section31/EIGSContinuousSemigroupMarkovOfRules.lean) | `38f3132ad590663a44fd2403dd60df35ecb98d59f83b25e386c41e73f9ab5c62` | `33bca4fa8bd2edf9376efa3c442f1706146d3f1799145ebc46e232ed1ffedebd` | 2 |
| [EIGSContinuousMarkovKernelOfRules](section3-diffusion/RequestProject/Section31/EIGSContinuousMarkovKernelOfRules.lean) | `b527451c55c17f9aba459d513373763b8f6af9c0feb20faec99c888c2c582ca5` | `b48ffbe47a4c75849de24a04abc268b631f88c9f556827af1ca52c0db4968dd3` | 2 |
| [EIGSNativeSupSemigroupConvergence](section3-diffusion/RequestProject/Section31/EIGSNativeSupSemigroupConvergence.lean) | `3a2424485a99c80447ccfc06c776b50da3d5c6972f5eb8429e6afea6e5eaa733` | `59bae059a9b81296488227a973d84ff81eb7032b1f81e5e6e7d637e7dccd1cfd` | 3 |
| [EIGSNativeSupDePoissonization](section3-diffusion/RequestProject/Section31/EIGSNativeSupDePoissonization.lean) | `7fbbf519bc85e879f51ff120d0c38a601278d05c7ac6f4c5ce5874f99889ce4e` | `fc8018c0b9d6da2af80bdf4dec37f81c7da53d26f626c902d1aedca9f43754c0` | 3 |
| [FiniteSupportPathFullConvergence](section3-diffusion/RequestProject/Section31/FiniteSupportPathFullConvergence.lean) | `201c6b72c1f37e522ec8a22f107412ebfe2ac99cc3b569d101dd4b6d2f0297a6` | `ca246c3b106ab45f24cb5244ea6355ef79004733ef3dba2eed829246960d3c9e` | 2 |
| [FiniteHorizonPathRestriction](section3-diffusion/RequestProject/Section31/FiniteHorizonPathRestriction.lean) | `047b22bada006c52cbaf7352db83dd5cdb69734b12c6fa4d0a854c13adbb9a6c` | `fed7e21c7904faf84d82fa2bac7d871931b7e7c19f99a68c53df6757dd580c6e` | 4 |
| [EIGSMovingStartApproximation](section3-diffusion/RequestProject/Section31/EIGSMovingStartApproximation.lean) | `0c0cc60ae1ce53351df5a6d0a6bd073ac1faa05cd40bec375d4ea4b35ca4276a` | `955e0f02fa232455014d9b2322a1a36ca88f4a0ade5a6aeafc4c28debb62fe52` | 2 |
| [GeometricBackwardIteration](section3-diffusion/RequestProject/Section31/GeometricBackwardIteration.lean) | `5fe04a7e51537d41122b421bd4f4698230d6102404e6db1d1f52d14b58acc3a4` | `1d5616de9dd76d8b9eb9f326753232385e5227a22dfeca723e517a3c8f332da6` | 2 |
| [DependentCoherentPrefixPathLaw](section3-diffusion/RequestProject/Section31/DependentCoherentPrefixPathLaw.lean) | `6f5ab45df2a814135e2b2fdaa62ad8933f422053009eab78424befdbb9a505f3` | `21f98543b9a79e90a154e08f296300e586536c71e7081a532db3b049d63a8fae` | 2 |

The actual continuous-time sup semigroup convergence and de-Poissonization bounds are proved for the actual model; the final original discrete sup limit revision is still pending. The actual Markov kernels are probability measures; they do not constitute a heat-kernel density, joint density continuity or strict positivity.

## Exact remaining gaps

- `EIGSNativeSupDiscreteConvergence`: first attempt failed; the corrected source has not yet been recompiled.
- `EIGSNativeSupFiniteObservations`: the first attempt failed on the Dirac/path-law measure conversion.
- Moving-start products, actual full finite-horizon path convergence, kernel identification, and compatible-law consumers: saved candidates awaiting their dependency chain and whole-file checks.
- `IntegerHorizonPathReconstruction`: first whole-file attempt failed on topology/measurability instances. Dependent coherent-prefix extension passed separately. A global continuous probability law, measurable starting-point family, strong Markov and Hunt properties remain unfinished.
- Actual address averages, their energy error, closed-domain Nash, L¹ estimates and ultracontraction: development chain pending whole-file acceptance. The accepted scalar backward-iteration lemma alone does not prove the heat-kernel claims.
- Existence, joint continuity and strict positivity of the actual heat-kernel density, its small-time global bound and stated pointwise estimates remain unfinished.

The random-cluster GHP and random diffusion extensions are expressly conjectures/outlook in the adopted paper and remain so.

## Model corrections

The adopted manuscript SHA256 is `06783166c1b05e8340edd98956319445b5a55056b47c2c9c60b65ce782746792`. The user accepted the three green means, eight green-arrow reversals with four boundary matrix changes, and one orientation of each undirected simple rule graph. Antiparallel counterexamples and correction certificates are retained; they are not claims about a distinct multigraph model.

## Handoff and archive

Round `20261013T084954Z` began at 2026-10-13 08:49:54 UTC and continues across automatic turns. Its single authoritative full archive is updated in place:
[complete round record](https://drive.google.com/file/d/1lRD_dypj77gjEx4nNGlUBZqrml7krj6d/view).

The portable evidence directory supplies current source status and accepted logs. Older local development logs may describe superseded states; the current manifest and this audit govern the upload's claims.
