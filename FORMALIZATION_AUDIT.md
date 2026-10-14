# Current formalization audit

Snapshot UTC: 2026-10-14T11:17:07.877976+00:00

Full-paper completion is **not** claimed. A clean printed axiom audit verifies the stated theorem; it does not remove mathematical assumptions from that statement. Actual-model consumers and generic conditional lemmas must be read separately.

## Verification scope

The latest completed common-dependency batch has 545 modules and unchanged checked sources. Report SHA256: `c75281dbb70120997bf6d5a5de2e1f03d14d6f9bb7a62390de27d240c20c0210`. The 634-module integration is still running and is not represented as a passed batch.

The independent manifest contains 307 accepted whole-file receipts and 1089 printed audits. These overlap the common batch and are not a completion percentage. Every published Lean source has an exact hash and explicit status; unverified and failed drafts remain visible.

## Accepted milestones

| Source | Source SHA256 | Log SHA256 | Audits |
| --- | --- | --- | --- |
| [EIGSOriginalMeasuredGHP](section3-diffusion/RequestProject/Section31/EIGSOriginalMeasuredGHP.lean) | `db3cbd82db11c43f000102d6a698de9221099458932152cd793c9018834b49ac` | `f75d931f1ef326bf9ee0f9da911085d6d4504d603654bd54c887949b83870fe4` | 10 |
| [EIGSNativeSupDiscreteConvergence](section3-diffusion/RequestProject/Section31/EIGSNativeSupDiscreteConvergence.lean) | `a87d8154328a78432c3c8d6dddbe032897e5a5c1d63f160c855744876af4b87d` | `e260306c9c1cd6613fd96600dc0977c7f128a49fa847ff5f6c2d42add58b1a6a` | 4 |
| [EIGSContinuousPathFamilyClosedIdentification](section3-diffusion/RequestProject/Section31/EIGSContinuousPathFamilyClosedIdentification.lean) | `4082ec73cb7949d0186870c273ebb454a78c1d56ea1562871205005c3a4a231f` | `13e9cf9f5c97a5a48170e3d44292bc011aab725394fa7fab2b12876d5537ecb1` | 2 |
| [EIGSFiniteStoppingClosedIdentification](section3-diffusion/RequestProject/Section31/EIGSFiniteStoppingClosedIdentification.lean) | `7ad7c76a832b11045af09d5885cd1ca4ad7c87d6105e5b6c5743a9bbdf2b3244` | `be4b3c2492ca874b3b4b9fd688c5cc89913bfb5dcbd7844ff2e61a89782ba53b` | 2 |
| [EIGSFiniteStoppingContinuousPathOfRules](section3-diffusion/RequestProject/Section31/EIGSFiniteStoppingContinuousPathOfRules.lean) | `4070353437750a73c72fa4872646adc4398d0439b86f65dd74df382627175129` | `faa250776e4fd61b3ba02df6262bda23e4400ca15ed68e16c449b0449758ebda` | 2 |
| [EIGSClosedSemigroupL1L2](section3-diffusion/RequestProject/Section31/EIGSClosedSemigroupL1L2.lean) | `fcbdf979751b6f3ba37f500029e2ab586fb5e161d298baa3c3580013c85103d9` | `9f7080838005d7d6da65dab6dc7a5b4f15e83ff0bf201d9bc7ad3093a062e386` | 2 |
| [EIGSContinuousAllTimeHeatKernelDensityOfRules](section3-diffusion/RequestProject/Section31/EIGSContinuousAllTimeHeatKernelDensityOfRules.lean) | `51f927d137199dbe983816ddef54df21088269f6167f5035c1fb5d82ffb27f8a` | `45df1e5590064805951d18596a9c462546ddfcd80d042f8818e948ece9f6699d` | 2 |
| [EIGSClosedFiniteBornPointEvaluation](section3-diffusion/RequestProject/Section31/EIGSClosedFiniteBornPointEvaluation.lean) | `7b896b4d033d9b2aa5a630ddd3d445cb2f8c0504789f22a26b4ad9228d669378` | `fa05e6e47a5d9a7a60158a00dd3602a57d5b3f658a94a03a10867812af0e8830` | 1 |
| [QuadraticEnergyFunctionalRecovery](section3-diffusion/RequestProject/Section31/QuadraticEnergyFunctionalRecovery.lean) | `d61adcee3275cbf9c97b1c7bbc5ea20f5883c5ba4684ae81f78d96be78e278ad` | `09b3ddedd0eed63e0920eb4e898fec0b806ec5a14ae6499c6918ca4459bf3c04` | 2 |
| [Section2PrimitiveIntegerGrowth](section2-random-walks/RequestProject/Section2PrimitiveIntegerGrowth.lean) | `8fd4bb6aea589da3f0d53a2cb48c66fcc56c9e440b790c3c3de71f2ef19b7aa2` | `5175a3e066e29681d95a4c0872a3bccda87c916285962e371e14830a27afc972` | 2 |
| [Section2DegreeMassGap](section2-random-walks/RequestProject/Section2DegreeMassGap.lean) | `5c463d9c1f8c716864944ed06b9815e9990e8361caa3290e09122f242937fb78` | `a11e58f848959bd5adc1045a3c23ec5f0dcf610323fd3f02423132962245aed7` | 5 |

## Proven scope and exact gaps

The same actual closed L² semigroup is identified with the global continuous-path family and the original discrete semigroup limit. Everywhere finite natural-filtration stopping times with continuous terminal tests are supplied internally. Usual/completed filtration, bounded Borel tests, potentially infinite stopping times on their finite event, and future-path strong Markov/Hunt consumers remain pending.

For each positive time the same actual semigroup has a spatially jointly continuous symmetric nonnegative probability density and the global small-time heat upper bound. This snapshot does not yet certify joint continuity in time or strict positivity. All-time bounds use a truncated time scale, not an incorrect all-time power decay on a compact conservative space.

Finite-born point evaluations extend to the same closed energy domain and are recovered along the same core sequences. Identifying them with an arbitrary continuous closed-domain representative needs the local address-star bridge. Finite-born two-sided pointwise heat bounds, typical-point logarithmic lower bounds and spectral dimensions remain open in the actual-model development. The actual primitive degree matrix growth and strict degree-to-mass spectral gap are independently verified.

Original measured GHP is verified. Final GHPS still requires normalized-metric and probability transport, the paper/native clock identification with the same normalization witnesses, canonical global-law restriction identification, and the actual càdlàg/J1 transport. New J1 candidates do not constitute a proved complete Skorokhod-space theory. Resistance-form/Brownian-regime construction and identification remain incomplete. Section 4 random GHP/diffusion outlook statements remain conjectures.

## Adopted corrections and archive

Adopted manuscript SHA256: `06783166c1b05e8340edd98956319445b5a55056b47c2c9c60b65ce782746792`. The approved changes are three green means, eight green-arrow reversals and four boundary matrix entries, and one orientation of an undirected simple rule graph. Antiparallel counterexamples are retained as correction evidence.

The active round is `20261013T084954Z`, beginning at 2026-10-13 08:49:54 UTC. Its authoritative [complete round record](https://drive.google.com/file/d/1lRD_dypj77gjEx4nNGlUBZqrml7krj6d/view) is updated in place. The same [latest progress file](https://drive.google.com/file/d/1sIIrFB6J5MijuZ3ndbsNAeNaYhA3R7dH/view) records major changes. Historical local paths in logs are diagnostic provenance; portable manifests use relative paths.
