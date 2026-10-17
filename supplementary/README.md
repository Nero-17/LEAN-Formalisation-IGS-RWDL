# Supplementary reproducibility files

For the newly recorded numerical resistance experiment, see
`POPULATION_DYNAMICS_README.md`, the standalone Python script and its JSON
outputs. These are exploratory finite-population computations, not rigorous
enclosures of the limiting exponent.

To regenerate the lower realisation in Figure 10, run from the manuscript root (or this repository root, after creating a `figure/` directory):

```shell
node supplementary/generate-four-colour-realisation.cjs
```

The generator uses seed 20261017 and the corrected four-colour conditional
replacement rules. It writes `figure/random_DHL-realisation-corrected.tex` and
`supplementary/four-colour-realisation-audit.json`. The audit records each
replacement and checks red connectivity, active-to-inactive green orientation,
blue/black endpoint states, and absence of proper geometric edge crossings
through generation three. These checks validate the displayed finite sample;
they are not a proof of the all-generation correspondence.
