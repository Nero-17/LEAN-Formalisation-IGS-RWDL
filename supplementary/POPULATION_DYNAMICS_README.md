# New independent critical DHL population-dynamics experiment

This experiment was newly written and run on 2026-10-17. It does not recover the historical simulation's seed, population or output. It implements the distributional resistance recursion stated in Section 4 of the manuscript.

## Reproduce

Requirements: Python 3 and NumPy. This run used Python 3.12.14 and NumPy 2.3.5 on Windows 11, NumPy `float64`, and explicit `Generator(PCG64(seed))`.

```shell
python population_dynamics.py --population 32768 --generations 10000 --seeds 20261017 20261018 20261019 20261020 --output population_dynamics_results.json
```

The standalone script contains no project-specific imports or absolute paths. The JSON records all arguments, versions, source SHA256, probabilities, generation checkpoints, run times and individual seed results. A separate 100-generation benchmark is recorded in `population_dynamics_timing.json`; its numerical seed-20261017 prefix agrees exactly with the main run through generation 100.

## Method

The initial population consists of 32,768 copies of resistance 1. At every generation, each parent samples four independent children with replacement from the preceding empirical population. With probability `q = p^4/(2p^2-p^4)`, where `p=(sqrt(5)-1)/2`, the parent is the parallel combination of the two series sums; otherwise it is the sum of the first two children. Here `q=0.23606797749978978`.

After each update, divide by the empirical arithmetic mean and accumulate the logarithm of that mean. Homogeneity makes this common normalization equivalent to running the same empirical recursion without normalization, while avoiding exponential overflow. If `scale` is the accumulated log mean and `population` is the normalized final population, the two reported empirical rates are `(scale + log(mean(population)))/n` and `(scale + mean(log(population)))/n`. They approximate the log of the mean resistance divided by `n` and the mean log resistance divided by `n` respectively.

## Observed results

UTC start: 2026-10-17 02:58:48.663680. UTC end: 2026-10-17 03:00:50.390600. Elapsed wall time: about 121.7 seconds. Process exit code 0. All recorded populations were positive and finite.

| Seed | Empirical log mean / n | Empirical mean log / n | Empirical Jensen gap / n |
|---|---:|---:|---:|
| 20261017 | 0.5631623814981774 | 0.5631551588313647 | 0.000007222666812745082 |
| 20261018 | 0.5631235459947741 | 0.5631162484462627 | 0.000007297548511364660 |
| 20261019 | 0.5631855368473161 | 0.5631782555399534 | 0.000007281307362716483 |
| 20261020 | 0.5631361908225138 | 0.5631288800387981 | 0.000007310783715630542 |

Across the four independent seeds:

- Log-mean rate: mean `0.5631519137906954`, range `0.5631235459947741`–`0.5631855368473161`, sample standard deviation `0.000027640709170359196`.
- Mean-log rate: mean `0.5631446357140948`, range `0.5631162484462627`–`0.5631782555399534`, sample standard deviation `0.000027659277930201057`.
- Jensen gap: mean `0.000007278076600614192`, range `0.000007222666812745082`–`0.000007310783715630542`.

These fresh values support an exploratory exponent near `0.563` and an empirical gap near `7.3 x 10^-6` for this finite algorithm. Individual rates straddle the four-decimal rounding boundary `0.56315`; thus `0.5631` should not be treated as a reliably resolved four-decimal value. The two different aggregate means also fall on opposite sides of that rounding boundary.

## Limits

The four populations use independent RNG seeds. Their spread is descriptive only. It is not a rigorous confidence interval, and it does not bound finite-population bias, finite-generation error, or the error in the true limiting exponent. The empirical Jensen gap is not an error bound for the exponent. No population-size convergence study was performed in this bounded reproduction task.

Minimal manuscript description: a **new independently recorded** population-dynamics run with population 32,768, 10,000 generations and seeds 20261017–20261020 gives exploratory rates near `0.563`; provide the script/JSON, report the descriptive spread if desired, and explicitly avoid a rigorous numerical enclosure claim. The historical run metadata remain unavailable.

SHA256 of script: `64c04cffaab82d59b32e97744fe1731d871c8d02703a9a2003190ad85a8a5a40`.

SHA256 of result JSON: `3d8eab8f3add66c35d590f7f343912a6b277f9e5c7221b48899d5a41a6c337bf`.
