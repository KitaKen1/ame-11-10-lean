# Notices and provenance

The standalone AME interface embedded in
`lean4web/AME11_10Lean4Web.lean` is adapted from
`FormalConjectures/OpenQuantumProblems/35.lean` at commit
`8927a585c5d522fc132d7ea6488fcd9e30ccd80e`, copyright the Formal
Conjectures authors and distributed under Apache-2.0.

The mathematical proof strategy was informed by an earlier AME(9,10)
formalization at commit `15e4b3a7584e218cec531aeaf71cce72a8a9ecb1`.
The character-orthogonality and coordinate-reindexing modules in this
repository are independently implemented; source code from that repository is
not incorporated here.

The quinary graph data comes from `sjbevins/AME-paper-materials` at commit
`2713599bec8fb429f6bb796b1ee4628dd4b51ef4`, copyright Samuel Bevins and
Yunus Bidav and distributed under the MIT License.  Its license text is
retained as `THIRD_PARTY_LICENSES/ame_materials_LICENSE`.

The explicit inverse matrices in the generated batch files are certificates
derived from the published graph data.  Lean checks every matrix against the
graph encoded in the proof.
