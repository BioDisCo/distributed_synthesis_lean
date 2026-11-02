# Third-party notices

The [paper authors](AUTHORS.md) provide this repository's Lean development.
“Lean adaptation and development” in the counter-machine headers refers to their
contribution; the separate named credits refer to the original Rocq/Coq
formalizations. Mathlib credits identify reused definitions and proofs, not
authorship of this project's bridge files. The project copyright notice refers
to the authors listed in `AUTHORS.md`; it does not replace upstream
copyright notices or claim their contributions as this project's work.

The root `LICENSE` contains the Apache-2.0 terms and the project copyright
notice. It does not replace the file-specific notices and licenses of
upstream-derived material.

The manual Rocq/Coq adaptations in
`DistributedSynthesis/Library/Computability/CounterMachines/` retain their
author attributions and MPL-2.0 notices. The Mathlib bridge retains its
Apache-2.0 notices. Both full license texts, the pinned upstream revision,
file-level provenance, and exact upstream snapshots are preserved in that
directory. See its [README](DistributedSynthesis/Library/Computability/CounterMachines/README.md).

The pinned dependencies in `lake-manifest.json` remain separate packages
with their own licenses; their downloaded sources and build caches are not
part of this repository.

The decision-task development contains selected Lean excerpts from the sibling
`consensusLTL` project, adapted to the local toolchain. Only the dependencies of
two-process task decidability and the IIS graph characterization are retained.
Its [source manifest and adaptation notes](DistributedSynthesis/Library/Distributed/DecisionTasks/SOURCE.md)
record the original commit, file hashes, selected declarations, and source
assistance credits.

The distinction between project attribution and retained upstream notices is
consistent with the notice provisions of [MPL-2.0, section 3.4](https://www.mozilla.org/en-US/MPL/2.0/#notices)
and [Apache-2.0, section 4](https://www.apache.org/licenses/LICENSE-2.0.txt).
