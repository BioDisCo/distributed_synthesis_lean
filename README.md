# Distributed LTL Synthesis under Arbitrary Message Adversaries

Lean formalization accompanying the paper by Benedikt Bollig,
Patricia Bouyer-Decitre, Matthias Függer, Dhrubajyoti Ghosh,
Thomas Nowak, and Nathalie Sznajder.

See [AUTHORS.md](AUTHORS.md) for the authors and acknowledgments.

## Checking the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.11 or later.
Then run:

```sh
git clone git@github.com:BioDisCo/distributed_synthesis_lean.git
cd distributed_synthesis_lean
lake exe cache get
python3 verification/verify.py fast
```

The repository pins the Lean and Mathlib versions. The script builds the Lean
proofs and tests, checks the paper correspondence links, and runs the axiom audits.

For the optional Docker-based proof checks, see
[verification/README.md](verification/README.md).
