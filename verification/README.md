# Reproducible proof verification

This optional audit supplements the normal build and axiom audit. Its scope
is the public mathematical API exposed by `DistributedSynthesis.Results`,
including theorems and definitions re-exported from project dependencies.
Targets are discovered from Lean's compiled environment, not a handwritten
list. [targets.json](targets.json) fixes the root module and axiom policy;
each export carries its complete declaration inventory.

This covers all result families: general and binary-output undecidability,
next-free undecidability, no-direct-reversal decidability, the graph-hole iff,
private-input undecidability, delayed hierarchy, and finite-memory separation.
Existing hypotheses are preserved, including source or compiler parameters
on conditional results. A definition returning `Decidable` is
checked as that definition; it is not relabelled as a computable solver.

The recipe builds two local images from Debian slim. The exporter uses the
library's Lean 4.30 toolchain. The checker uses Comparator with Lean 4.34.0-rc2
and the independent Rust kernel Nanoda. Updating the checker does not require
changing the library's Lean/Mathlib versions.

## Two commands

Run from the repository root. For everyday development:

```sh
python3 verification/verify.py fast
```

This checks the paper guide links, runs the incremental Lean build, and audits
the library, component-tree, undecidability, and paper-entry endpoints. Build warnings
fail the command, so new warnings cannot silently accumulate. On a fresh checkout,
first run `lake exe cache get`.

For Comparator verification against a saved, reviewed reference:

```sh
python3 verification/verify.py check --reference /path/to/reference.tar
```

This prepares the Docker images, compiles and exports the checkout in Linux,
compares the public API, and replays the proofs. The temporary candidate export
is cleaned up automatically. Keep both checks: the fast check is the normal
coding workflow; Comparator adds reference comparison and isolated replay.

Comparator requires Docker running with Linux containers, Python 3.11 or
later, and several GB of free disk space. The first image build downloads
pinned tools and dependencies; later image builds reuse Docker's cache.
Compilation and checking run without network access.

## Save a reference once

A reference is a saved snapshot of the formal statements and definitions from
a reviewed version. It records what the current development is supposed to
preserve. Comparator checks preservation against that snapshot separately from
checking the validity of the current proofs. A different proof of the same
statement can pass; a weakened statement or changed model definition fails
comparison even if Lean accepts its proof.

The reference is not evidence that the formalization expresses the intended
mathematics. The statements, hypotheses, and model definitions still need human
review. Creating a reference exports a snapshot; it does not perform that review.

From a reviewed version, before changing the statements or definitions being
protected:

```sh
python3 verification/verify.py reference --output /path/to/reference.tar
```

Replace `/path/to/reference.tar` in both commands with the actual reference
file's path. Keep this file in a permanent location outside Git. The command
prepares Docker and refuses to overwrite an existing file. Do not regenerate a reference merely to make a
failed comparison pass: review the change first. To use a separate reviewed
checkout, add `--project /absolute/path/to/reviewed-checkout`.

## Optional and advanced commands

`--kernels lean` uses Comparator's comparison, axiom validation, and Lean
kernel replay. To require the independent Nanoda kernel as well, select
`--kernels both`. Nanoda can require substantially more memory than Lean;
allocate sufficient RAM to Docker for the full proof. There is no automatic
fallback if a selected kernel fails. The small self-test always uses both.

The export command refuses to overwrite a saved file. It prints its SHA-256;
record that hash with the reviewed source revision. An export freshly copied
from the candidate is not an independent reference. No reference is silently
created by `compare`.

Each bundle contains a declaration inventory and a hashed NDJSON payload.
Comparison requires matching inventories. Adding or removing a public result
therefore fails comparison with an older reference until the API change is
reviewed and a new reference is saved. Export also rejects public result
source modules that are absent from the compiled `Results` umbrella. The
earlier graph-hole-only NDJSON exports cannot serve as full-API references.

To manage images and candidate exports separately, the lower-level commands
remain available:

```sh
python3 verification/verify.py build
python3 verification/verify.py export --output /path/to/solution.tar
python3 verification/verify.py compare \
  --reference /path/to/reference.tar --solution /path/to/solution.tar
```

When changing the audit scripts, test both the host-side failure handling and
the actual kernel checks (after building the images):

```sh
python3 -m unittest discover -s verification -p 'test_*.py'
python3 verification/verify.py self-test
```

Each export builds source in a fresh disposable Docker volume. It does not
reuse host `.lake` files or write into the checkout. The image's dependency
cache is copied into that volume. The project toolchain, Lake configuration,
and dependency manifest must match those used to build the image. To change
versions, update the pinned exporter/toolchain together, rebuild the images,
and rerun the positive and negative self-tests and the real proof audit.

`--jobs N` before the subcommand controls Lean parallelism in Docker (default 2).
Nanoda checks serially with a 512 MiB process stack because upstream's fixed
16 MiB worker stacks are too small for some of these proof terms. This changes
resource limits, not the kernel or axiom policy. A crash, exhausted resource,
missing dependency, or rejected proof fails the command.

## What the checks establish

The ordinary `lake build` checks elaborated Lean proofs. Our
`scripts/check_library.py --axioms` additionally rejects nonstandard axioms
at the audited endpoints, including `sorryAx` and compiler-trust axioms.

The extra audit uses Comparator's statement comparison and kernel replay.
Public definitions, types, and constructors are compared exactly using its
declaration-comparison routines; there are no editable definition holes.
The axiom policy is checked for every public root, including definitions that
no theorem uses. In `both` mode Nanoda must also accept the candidate export.
Both permit only `propext`, `Classical.choice`, and `Quot.sound`. Export also
includes the pinned Comparator's own primitive and quotient lists.
See the [Comparator implementation](https://github.com/leanprover/comparator/blob/2312244ac716564a61cc0bf4e107d9abf1757a61/Main.lean)
and [Nanoda implementation](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27).

The self-test exports actual small Lean proofs. It must accept a matching
pair and reject a changed statement definition, a changed public definition
unused by any theorem, a proof using an extra axiom, and omitted or added
public results. Host-side tests also reject unimported result modules and
malformed export bundles.

The inventory includes non-private, non-internal, safe, non-partial
declarations defined in project modules imported by `Results`. Private
helpers and external-library declarations are included as dependencies when
needed by those roots. Unimported files and unsafe metaprograms are
outside this mathematical API audit. All statements and their hypotheses
still require mathematical review.

The trusted reference must include the intended definitions, not just the
theorem's printed text. Preserving a reference formalization does not establish
that it expresses the intended informal mathematics. A Lean/Mathlib upgrade
can also legitimately change referenced definitions; such a change needs a
reviewed reference update, not a relaxed axiom allowlist. Removing unused hypotheses
from public helper lemmas also changes the compared API: review the strengthened
statements before saving a new reference.

## Isolation and pins

This is a Docker adaptation of Comparator's exported-data checks, **not** its
Landrun build orchestration. Compilation/export and checking run in separate
unprivileged containers. They have no network, capabilities, Docker socket,
or writable host mounts. The checker receives only two read-only bundles and
unpacks their data into a disposable Docker volume; it receives no candidate
source, native plugin, or `.olean`. This
design relies on Docker/host isolation and is not a claim of an independently
audited sandbox equivalent to upstream's Landrun setup.

| Component | Pin |
| --- | --- |
| Project Lean / Mathlib | 4.30.0 / repository `lake-manifest.json` |
| Comparator | `2312244ac716564a61cc0bf4e107d9abf1757a61` |
| Checker Lean | 4.34.0-rc2 |
| Project lean4export | `a3e35a584f59b390667db7269cd37fca8575e4bf` |
| Comparator's parsing dependency | its committed Lake manifest |
| Nanoda | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |
| Rust build image | 1.90.0, manifest digest in Dockerfile |
| Debian base | trixie-slim, manifest digest in Dockerfile |

Git dependencies and container bases are pinned. Debian package installation
still uses the distribution repositories; this is a reproducible source
recipe, not a promise of byte-identical image builds. Only the Dockerfile,
configuration, Lean adapters, scripts, and documentation belong in Git.
Images remain in Docker's local store; exports and disposable build products
remain outside the repository.
