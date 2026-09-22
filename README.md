# A Lean proof of AME(11,10)

This repository proves the existence of an absolutely maximally entangled state
with 11 parties and local dimension 10.  It targets the declaration
[`OpenQuantumProblem35.ame_11_10_open`](https://github.com/google-deepmind/formal-conjectures/blob/8927a585c5d522fc132d7ea6488fcd9e30ccd80e/FormalConjectures/OpenQuantumProblems/35.lean#L866-L870)
in Formal Conjectures commit
[`8927a585c5d522fc132d7ea6488fcd9e30ccd80e`](https://github.com/google-deepmind/formal-conjectures/commit/8927a585c5d522fc132d7ea6488fcd9e30ccd80e).

The Formal Conjectures version proves the explicit replacement target

```lean
theorem ame_11_10_solved :
    answer(True) ↔ OpenQuantumProblem35.ExistsAME 11 10
```

using the unconditional theorem

```lean
AMEProbe.AME11_10.existsAME_11_10 :
  OpenQuantumProblem35.ExistsAME 11 10
```

The checked proof contains no `sorry`, `admit`, `native_decide`, custom axiom,
or `unsafe` theorem.  The final `#print axioms` output is

```text
[propext, Classical.choice, Quot.sound]
```

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fame-11-10-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FAME11_10Lean4Web.lean).

## Construction

The local ten-dimensional system is written as

```text
Fin 10 ≃ ZMod 2 × ZMod 5.
```

The proof couples two branches obtained from:

- a 12-qubit graph state whose reductions on every five-party subsystem are
  maximally mixed; and
- the published quinary graph construction of an `AME(12,5)` state.

Lean checks 792 binary five-versus-seven cut certificates and 924 quinary
six-versus-six cut certificates.  A proved bit-mask encoding shows that these
certificates cover every required subsystem.  The parent reductions are then
converted into branch identities, coupled on 11 sites, normalized, and
transported through `Fin 10 ≃ ZMod 2 × ZMod 5` to the exact Formal Conjectures
definition.

For a five-site subsystem `S`, the resulting normalized state satisfies

```text
ρ_S = I / 10^5.
```

## Mathematical explanation (AI-generated)

This section is AI-generated explanatory prose.  It is intended to let a
mathematician follow the proof without reading Lean syntax; the Lean source is
the authoritative verification.

### 1. What must be proved

Write the local alphabet as

$$
D=\mathbb Z/2\mathbb Z\times\mathbb Z/5\mathbb Z,
\qquad |D|=10.
$$

For an eleven-party amplitude function
$\psi:D^{11}\to\mathbb C$ and a set $A$ of five parties, the reduced density
matrix has entries

$$
\rho_A(x,y)=\sum_{z\in D^{A^c}}
  \psi(x\mathbin{\sqcup_A}z)\,
  \overline{\psi(y\mathbin{\sqcup_A}z)}.
$$

Here $x\mathbin{\sqcup_A}z$ denotes the full word obtained by pasting the
coordinates on $A$ and $A^c$.  For an AME$(11,10)$ state it is enough to prove,
for every $|A|=5$,

$$
\rho_A(x,y)=10^{-5}\delta_{x,y}.
\tag{1}
$$

The diagonal entries in (1) sum to one, so the same identity also proves the
normalization of $\psi$.

### 2. The graph-state orthogonality lemma

Let $p$ be $2$ or $5$, let $G$ be a symmetric $n\times n$ matrix over
$\mathbb Z/p\mathbb Z$ with zero diagonal, and put

$$
q_G(w)=\sum_{i<j}G_{ij}w_iw_j,
\qquad
\chi_p(t)=\exp(2\pi i t/p).
$$

For a cut $A\subseteq\{0,\ldots,n-1\}$, define its cut map

$$
C_A:(\mathbb Z/p\mathbb Z)^A\longrightarrow
    (\mathbb Z/p\mathbb Z)^{A^c},
\qquad
(C_A d)_j=\sum_{i\in A}G_{ji}d_i.
$$

If $d=x-y$ on $A$ and is zero on $A^c$, expansion of the quadratic form gives

$$
q_G(x\mathbin{\sqcup_A}z)-q_G(y\mathbin{\sqcup_A}z)
  =b(x,y)+\sum_{j\in A^c}z_j(C_A d)_j,
\tag{2}
$$

where $b(x,y)$ is independent of $z$.  Character orthogonality in each
coordinate then gives

$$
\sum_{z\in(\mathbb Z/p\mathbb Z)^{A^c}}
 \chi_p\!\left(q_G(x\mathbin{\sqcup_A}z)-
                    q_G(y\mathbin{\sqcup_A}z)\right)
=
\begin{cases}
p^{|A^c|},& C_A d=0,\\
0,& C_A d\ne0.
\end{cases}
\tag{3}
$$

When $C_A$ is injective, $C_A d=0$ is equivalent to $x=y$.  Thus (3) is
exactly the orthogonality of the graph-state rows across the cut.  This is
proved for general $G$ and $A$ in
[`GraphCharacter.lean`](lean/GraphCharacter.lean).  The passage from (3) to a
reduced density matrix, including the normalization scalar, is in
[`GraphState.lean`](lean/GraphState.lean).

### 3. The two twelve-party parent graphs

The proof uses an extra coordinate as a branch label, so both parents have
twelve coordinates.

* The binary matrix $B$ in [`BinaryGraph.lean`](lean/BinaryGraph.lean) is a
  symmetric circulant-type graph over $\mathbb Z/2\mathbb Z$.  For every
  five-element cut $S$, its $7\times5$ cut matrix $C_S$ has full column rank.
  There are $\binom{12}{5}=792$ such cuts.
* The quinary matrix $Q$ in [`QuinaryGraph.lean`](lean/QuinaryGraph.lean) is the
  published AME$(12,5)$ graph over $\mathbb Z/5\mathbb Z$.  For every
  six-element cut $T$, its $6\times6$ cut matrix is invertible.  There are
  $\binom{12}{6}=924$ such cuts.

For each cut the repository contains an explicit matrix $L$ satisfying
$LC_S=I$.  This is a finite certificate that $C_S$ is injective.  Lean checks
the matrix products and also checks, through an injective bit-mask encoding,
that the 792 and 924 certificates cover every cut.  These finite computations
are the large generated batch files; no unproved rank assertion is used.

With amplitude $p^{-6}\chi_p(q_G(w))$, equation (3) shows that the binary
parent has maximally mixed reductions on every five-party subsystem, while the
quinary parent has maximally mixed reductions on every six-party subsystem.
Indeed the diagonal scalar on a cut $A$ is
$p^{-12}p^{12-|A|}=p^{-|A|}$.  Only the quinary parent is asserted to be an
AME$(12,5)$ state; the binary parent supplies exactly the five-party property
needed below.

### 4. Turning the extra coordinate into two branches

Write a twelve-coordinate word as $(a,x)$, where $a$ is coordinate zero and
$x$ consists of the remaining eleven coordinates.  Define the unnormalized
phase amplitudes

$$
u_a(x)=\chi_2(q_B(a,x)),
\qquad
v_a(x)=\chi_5(q_Q(a,x)).
$$

In the final construction only the labels $a=0,1$ are used, interpreted in
the appropriate field in each factor.

For the binary parent, fix only the five physical coordinates in $A$.  The
complement then consists of the branch label $a\in\mathbb Z/2\mathbb Z$ and
six remaining physical coordinates.  Applying (3) gives

$$
\sum_{a\in\mathbb Z/2\mathbb Z}\ \sum_{z_2}
 u_a(x_2\mathbin{\sqcup_A}z_2)
 \overline{u_a(y_2\mathbin{\sqcup_A}z_2)}
=2^7\delta_{x_2,y_2}.
\tag{4}
$$

For the quinary parent, fix the branch coordinate together with the five
physical coordinates in $A$.  This is a six-coordinate cut.  Equation (3)
now gives the stronger block identity

$$
\sum_{z_5}
 v_a(x_5\mathbin{\sqcup_A}z_5)
 \overline{v_b(y_5\mathbin{\sqcup_A}z_5)}
=5^6\delta_{a,b}\delta_{x_5,y_5}.
\tag{5}
$$

The coordinate embeddings and the conversion of the parent cuts into (4) and
(5) are proved in [`LiftedCuts.lean`](lean/LiftedCuts.lean) and
[`ParentBranches.lean`](lean/ParentBranches.lean).

### 5. Coupling the branches

For $x=(x_2,x_5)\in D^{11}$ define the raw amplitude

$$
R(x)=u_0(x_2)v_0(x_5)+u_1(x_2)v_1(x_5).
\tag{6}
$$

Expanding the reduction of (6) produces four terms.  Each term factors into a
binary reduction and a quinary reduction because the complementary variables
$z_2$ and $z_5$ are independent.  The two cross terms vanish by (5), since
$0\ne1$ in $\mathbb Z/5\mathbb Z$.  The two diagonal terms combine by (4).
Consequently, for every five-party cut $A$,

$$
\sum_{z\in D^{A^c}}
 R(x\mathbin{\sqcup_A}z)\overline{R(y\mathbin{\sqcup_A}z)}
=2^7 5^6\,\delta_{x,y}
=2{,}000{,}000\,\delta_{x,y}.
\tag{7}
$$

This four-block calculation is formalized in
[`AMEProbe.lean`](lean/AMEProbe.lean) and specialized to the two parents in
[`CoupledState.lean`](lean/CoupledState.lean).

### 6. Scaling and normalization

Set

$$
s=\frac{\sqrt5}{1{,}000{,}000},
\qquad \psi(x)=sR(x).
$$

Since

$$
|s|^2\,2{,}000{,}000
=\frac{5}{10^{12}}\,2{,}000{,}000
=\frac1{100{,}000}
=\frac1{10^5},
$$

equation (7) becomes exactly (1).  Taking the trace of any such five-party
reduction gives

$$
\|\psi\|^2=10^5\cdot10^{-5}=1.
$$

The exact real-square-root calculation and the trace argument are in
[`FinalState.lean`](lean/FinalState.lean).

### 7. Matching the Formal Conjectures statement

Finally, the local-coordinate equivalence

$$
\operatorname{Fin}(10)
\simeq \operatorname{Fin}(2)\times\operatorname{Fin}(5)
\simeq \mathbb Z/2\mathbb Z\times\mathbb Z/5\mathbb Z
$$

reindexes $\psi$ without changing any sums.  Arbitrary five-party cuts are
transported to the first five coordinates after a permutation, which is the
form used by the Formal Conjectures definition.  These transports are proved
in [`FCValueBridge.lean`](lean/FCValueBridge.lean) and
[`FCSubsystemBridge.lean`](lean/FCSubsystemBridge.lean).  Therefore
[`AME11_10.lean`](lean/AME11_10.lean) proves `ExistsAME 11 10`, and
[`AME11_10FC.lean`](lean/AME11_10FC.lean) proves the replacement target

```lean
answer(True) ↔ OpenQuantumProblem35.ExistsAME 11 10.
```

The conceptual implication chain is

```text
checked left inverses for all cuts
  ⇒ injective cut maps
  ⇒ graph-character orthogonality
  ⇒ binary diagonal-sum and quinary cross-block identities
  ⇒ coupled raw reduction = 2,000,000 · I
  ⇒ scaled reduction = I / 10^5
  ⇒ normalized AME(11,10) state
  ⇒ exact Formal Conjectures target.
```

## Files

| Directory | Dependencies | Purpose |
|---|---|---|
| `lean/` | Formal Conjectures at `8927a585...` | Proof of the exact FC target `answer(True) ↔ ExistsAME 11 10` |
| `lean4web/` | mathlib `v4.33.1` only | One standalone file to paste directly into Lean4Web |

The FC project keeps the proof split into small modules so that the 1,716
explicit cut certificates can be built in parallel.  The generated
`lean4web/AME11_10Lean4Web.lean` inlines all 88 proof modules into one file.  It
has exactly one import, `Mathlib`, and can be copied and pasted as a whole into
Lean4Web.  The file is about 1.1 MB, so browser elaboration takes substantial
time.

## Verification

Formal Conjectures target:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib-only target:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Lean4Web:

1. Open <https://live.lean-lang.org/>.
2. Copy the complete contents of `lean4web/AME11_10Lean4Web.lean` into the editor.
3. Wait for all 1,716 explicit certificates and the final theorem to elaborate.

The project uses Lean and mathlib `v4.33.1`.  The aggregate module
`AMEProgress.lean` prints the axioms of nine major checkpoints, including the
parent states, coupled reduction, normalization, and final existence theorem.
The FC command above was replayed from a fresh Lake dependency directory on
2026-09-22 and completed 9,001 build jobs.  The final single-file Lean4Web
source was separately compiled with Lean 4.33.1 and mathlib 4.33.1 in 1,063
seconds.  Its final axiom output was
`[propext, Classical.choice, Quot.sound]`.

## Formal Conjectures status boundary

This proves the positive answer for the single pair `(n,d) = (11,10)`.  It does
not classify every pair `(n,d)` in Open Quantum Problem 35.  The pinned Formal
Conjectures revision still labels `ame_11_10_open` as `research open`; changing
that metadata requires a separate reviewed contribution.

## Sources and attribution

- [Formal Conjectures, Open Quantum Problem 35](https://github.com/google-deepmind/formal-conjectures/blob/8927a585c5d522fc132d7ea6488fcd9e30ccd80e/FormalConjectures/OpenQuantumProblems/35.lean)
- [Bevins--Bidav, *Symmetry-guided constructions of absolutely maximally entangled states in five open cases*](https://arxiv.org/abs/2608.05781)
- [Published `AME(12,5)` graph data](https://github.com/sjbevins/AME-paper-materials/blob/2713599bec8fb429f6bb796b1ee4628dd4b51ef4/data/theta_ame125.txt)
- [An earlier AME(9,10) formalization](https://github.com/niketp03/atlas-fc-verified/blob/15e4b3a7584e218cec531aeaf71cce72a8a9ecb1/AtlasFCSolutions/Oqp35.lean), which helped identify the character-orthogonality and coordinate-reindexing strategy. The corresponding modules here are independently implemented and do not incorporate its source code.

See [`NOTICE.md`](NOTICE.md) and `THIRD_PARTY_LICENSES/` for incorporated
third-party material and its license information.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra.
