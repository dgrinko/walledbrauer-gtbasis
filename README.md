# Walled Brauer algebra: Gelfand–Tsetlin basis and mixed Schur transform

Wolfram Language (Mathematica) code for the representation theory of **mixed Schur–Weyl duality**. It supports the paper

> [Gelfand-Tsetlin basis for partially transposed permutations, with applications to quantum information](https://arxiv.org/abs/2310.02252)

## Background

Consider the mixed tensor space

$$(\mathbb{C}^d)^{\otimes n} \otimes (\mathbb{C}^{d*})^{\otimes m}$$

that is, $n$ copies of $\mathbb{C}^d$ and $m$ copies of its dual. Two commuting actions live on it, and the algebras they generate are each other's commutants:

* The **unitary group** $U(d)$ acts as $U^{\otimes n} \otimes \bar{U}^{\otimes m}$.
* The **algebra of partially transposed permutations** acts by permuting the first $n$ and the last $m$ tensor factors, and by the contraction between factors $n$ and $n+1$. The contraction is the partial transpose of the swap of those two factors. This algebra is the image of the walled Brauer algebra $B_{n,m}(d)$ acting on the tensor space: it is isomorphic to $B_{n,m}(d)$ when $d \ge n + m$ and a proper quotient of it otherwise. As in the function names, we still call it the walled Brauer algebra (WBA) below. Its irreps are labelled by pairs of partitions $(\lambda, \mu)$ of $n - k$ and $m - k$, $k = 0, \dots, \min(n, m)$, with at most $d$ rows in total.

The space therefore decomposes as $\bigoplus_\lambda V_\lambda \otimes W_\lambda$. Here $V_\lambda$ is an irrep of $U(d)$ and $W_\lambda$ is the matching irrep of the walled Brauer algebra. The code provides the following:

* **Irreps and Bratteli diagrams.** It lists the irreps $\lambda$ and draws the Bratteli diagrams of the walled Brauer algebra and of $U(d)$.
* **Gelfand–Tsetlin (GT) bases.** For the walled Brauer algebra these are paths in the Bratteli diagram. For $U(d)$ they are GT patterns.
* **Generators in the GT basis.** It gives the matrices of the transpositions and of the contraction in the GT basis.
* **Clebsch–Gordan coefficients of $U(d)$.** These cover $\lambda \otimes \mathbb{C}^d$ and $\lambda \otimes \mathbb{C}^{d*}$.
* **The mixed quantum Schur transform.** This is the orthogonal matrix that changes the standard basis of the tensor space into the basis adapted to $\bigoplus_\lambda V_\lambda \otimes W_\lambda$.

## Repository contents

| File | Description |
| --- | --- |
| [`Mixed Schur Tools.wl`](Mixed%20Schur%20Tools.wl) | The main package (context ``MixedSchurTools` ``) with everything listed above. |
| [`Bratteli diagram.nb`](Bratteli%20diagram.nb) | Draws the Bratteli diagram of the walled Brauer algebra. |
| [`Matrix Units.nb`](Matrix%20Units.nb) | Builds matrix units of the algebra in the Gelfand–Tsetlin basis from products of Clebsch–Gordan tensors, and compares them with the Schur transform. |
| [`v1/`](v1) | Code for version 1 of the paper (see [below](#v1-code-of-the-first-arxiv-version)). |

## Getting started

The package needs Wolfram Mathematica or the free Wolfram Engine. The notebooks were created with Mathematica 14.0. Load the package with `Get`:

```mathematica
Get["/path/to/walledbrauer-gtbasis/Mixed Schur Tools.wl"]

(* from a notebook saved in the repository folder *)
Get[NotebookDirectory[] <> "/Mixed Schur Tools.wl"]
```

Load the package before you evaluate any cell that uses its functions. The notebooks do this in their first cell, which is an initialization cell. If a cell that mentions, say, `CG` runs first, Mathematica creates an empty ``Global`CG`` and reports `CG::shdw` when the package loads. Definitions evaluated before loading, such as `PathTensor` in `Matrix Units.nb`, keep referring to that empty symbol. To recover, run ``Remove["Global`CG"]`` and evaluate those cells again, or quit the kernel and evaluate the notebook from the top.

Do not load `Mixed Schur Tools.wl` and `v1/walled_brauer_gt_basis.wl` in the same kernel. Both define `Irreps` and `OrderWBA`, with different conventions: v1 uses pairs of partitions, the package uses staircases. Whichever file is loaded second breaks the other one's functions without any error message. Notebooks share one kernel by default, so quit the kernel (Evaluation > Quit Kernel) before switching between a v1 notebook and a top-level notebook.

A short session for $n = 2$, $m = 1$, $d = 2$:

```mathematica
{n, m, d} = {2, 1, 2};

Irreps[n, m, d]                 (* {{2, -1}, {1, 0}}  irreps as staircases *)
IrrepDimsWBA[n, m, d]           (* {1, 2}             dimensions of the walled Brauer irreps *)
IrrepDimsGL[n, m, d]            (* {4, 2}             dimensions of the U(d) irreps; 1*4 + 2*2 = 2^3 *)

BratteliDiagramWBALabelled[n, m, d]       (* draw the Bratteli diagram *)
PathsToIrrepWBA[{1, 0}, n, m, d]          (* GT basis of the irrep {1, 0}: the two paths
                                             {1, 0} -> {2, 0} -> {1, 0} and {1, 0} -> {1, 1} -> {1, 0} *)
GTPatterns[{1, 0}]                        (* GT basis of the U(2) irrep {1, 0}: {{{1}, {1, 0}}, {{0}, {1, 0}}} *)

GeneratorsGT[n, m, d]           (* matrices of sigma_1, sigma_2 (sigma_n is the contraction), one per irrep *)
CG[{1, 0}, {2, 0}]              (* Clebsch-Gordan tensor for {1, 0} (x) C^2 -> {2, 0} *)
S = SchurTransform[n, m, d];    (* 8 x 8 mixed Schur transform, a SparseArray *)
```

Every exported function has a usage message, so `?SchurTransform` describes a single function and ``?MixedSchurTools`*`` lists them all.

## Conventions

| Object | Representation |
| --- | --- |
| **staircase** | A non-increasing integer list of length $d$ that labels an irrep, e.g. `{2, 1, 0, -1}`. Its positive entries form the "left" partition and its negative entries the reversed "right" partition. `ToStaircase[{{2, 1}, {1}, 4}]` gives `{2, 1, 0, -1}`, and `ToPair` converts back. |
| **vertex** | A vertex `{staircase, level}` of the walled Brauer Bratteli diagram, with `level` from `0` to `n + m`. A step to one of the levels `1..n` adds a cell to the left partition. A step to one of the levels `n+1..n+m` either adds a cell to the right partition or removes one from the left partition. |
| **path** | A list `{T_1, ..., T_(n+m)}` of staircases from the root (omitted) to an irrep. Paths label the GT basis of the walled Brauer irreps. |
| **GT pattern** | A list of rows `{P_1, ..., P_d}`, where row `k` has length `k`, consecutive rows interlace, and `P_d` is the irrep. Patterns label the GT basis of $U(d)$ irreps. |
| **string** | A list `x` of `n + m` letters from `1..d` that labels the standard basis vector $\lvert x_1 \dots x_{n+m}\rangle$. |
| **Schur basis** | Pairs `{T, P}` of a path and a GT pattern of the same irrep. They are ordered by irrep (as in `Irreps`), then by path, then by pattern. |

Row `i` of `SchurTransform[n, m, d]` is the Schur basis vector `SchurBasis[n, m, d][[i]]`. Column `j` is the string `StandardBasis[n + m, d][[j]]`, so strings are in lexicographic order.

## Function reference: `Mixed Schur Tools.wl`

**Staircases and Young diagrams**

| Function | Description |
| --- | --- |
| `ToStaircase[{left, right, d}]`, `ToPair[staircase]` | Convert between a pair of partitions and a staircase. |
| `DisplayStaircase[staircase]` | Draw a staircase as two Young diagrams separated by a wall. |
| `TransposePartition`, `AddCell`, `AddableCells` | Basic operations on partitions. |
| `Id[n]`, `Enumerate[list]` | Sparse identity matrix, and pairs `{element, position}`. |

**Walled Brauer algebra**

| Function | Description |
| --- | --- |
| `BratteliLevelsWBA`, `BratteliDiagramWBA`, `BratteliDiagramWBALabelled` | Vertices by level, the Bratteli diagram as a `Graph`, and a drawing with labelled vertices. |
| `OrderWBA[u, v]` | Edge relation of the Bratteli diagram. |
| `Irreps[n, m, d]` | Irreps appearing in $(\mathbb{C}^d)^{\otimes n} \otimes (\mathbb{C}^{d*})^{\otimes m}$. |
| `PathsToIrrepWBA`, `AllPathsWBA`, `IrrepDimWBA`, `IrrepDimsWBA` | GT basis paths and dimensions of the walled Brauer irreps. |
| `AssociationIrrepsWBA`, `AssociationPathsToIrrepWBA` | Positions of irreps and of paths. |

**Unitary group**

| Function | Description |
| --- | --- |
| `GTPatterns[λ]`, `AssociationGTPatterns[λ]` | GT patterns of a $U(d)$ irrep and their positions. |
| `WeylDim[λ]`, `IrrepDimsGL[n, m, d]` | Dimensions of $U(d)$ irreps. |
| `InterlacingCandidates`, `OrderGL` | Interlacing rows, and the edge relation of the $U(d)$ Bratteli diagram. |
| `BratteliLevelsGL`, `BratteliDiagramGL`, `AllGTPatterns` | Bratteli diagram of $U(0) \subset U(1) \subset \dots \subset U(d)$, and GT patterns as paths in it. |

**Clebsch–Gordan coefficients**

| Function | Description |
| --- | --- |
| `CG[μ, λ]` | Clebsch–Gordan tensor `C[[x, i, j]]` for $\mu \otimes \mathbb{C}^d \to \lambda$ or $\mu \otimes \mathbb{C}^{d*} \to \lambda$. |
| `CGcoef[P, x, Q]`, `RWcoef`, `GTcandidates` | A single coefficient, its factorization into reduced Wigner coefficients, and the patterns where it can be non-zero. |

**Mixed Schur transform**

| Function | Description |
| --- | --- |
| `SchurTransform[n, m, d]` | The mixed Schur transform. Only entries that can be non-zero are computed. |
| `SchurTransformSlow[n, m, d]` | The same matrix, computed entry by entry. |
| `SchurBasis`, `SchurIndex`, `StandardBasis` | Row and column labels of the transform. |
| `SchurCoef[x, {T, P}]`, `CGmatProduct[x, T]` | Individual coefficients $\langle T, P \vert x\rangle$. |
| `Weight`, `GTPatternsWeight` | $U(d)$ weights of strings and of GT patterns. |
| `BratteliLevelsWBAString`, `BratteliDiagramWBAString`, `AllPathsWBAString`, `SchurBasisGivenString` | Bratteli diagram and Schur basis restricted to one string. This is what speeds up `SchurTransform`. |

**Gelfand–Tsetlin basis of the partially transposed permutations**

| Function | Description |
| --- | --- |
| `GeneratorsGT[n, m, d]` | Matrices of all generators $\sigma_1, \dots, \sigma_{n+m-1}$, one per irrep. |
| `TranspositionGT[i, n, m, d]` | Transposition $(i, i+1)$ for $i \ne n$, from Young's orthogonal form. |
| `ContractionGT[n, m, d]` | The contraction $\sigma_n$. |
| `WalledContent`, `AxialDistance` | Signed contents of cells along a path, and the axial distances that define the transpositions. |

The old names `InterlacingCanditates`, `transpostionGT`, `contractionGT` and `generatorsGT` still work as aliases.

## v1: code of the first arXiv version

The [`v1`](v1) folder holds the code for [arXiv:2310.02252v1](https://arxiv.org/abs/2310.02252v1). Here the irreps are pairs of partitions `{left, right}`, and the Gelfand–Tsetlin basis vectors are pairs of mixed Young tableaux. The parameters are called `p, q, d` instead of `n, m, d`.

| File | Description |
| --- | --- |
| [`walled_brauer_gt_basis.wl`](v1/walled_brauer_gt_basis.wl) | `BratteliDiagram`, `Irreps`, `AllPaths`, `IrrepDims`, `DisplayAllPathsAsYT` (paths as mixed Young tableaux), `AllGeneratorsGT` (generators in the Young–Yamanouchi basis) and `CheckRelations` (checks the walled Brauer algebra relations). Its definitions live in the ``Global` `` context, so the notebooks can extend them. Do not load it in a kernel that already has the main package (see [Getting started](#getting-started)). |
| [`wba_gt_basis_demonstration.nb`](v1/wba_gt_basis_demonstration.nb) | Demonstrates the Bratteli diagram, the irreps, the mixed Young tableaux and the generator matrices, and checks the relations. |
| [`port-based teleportation.nb`](v1/port-based%20teleportation.nb) | Applies the code to port-based teleportation. It builds the pretty good measurement and a Naimark-dilated projective measurement in the Gelfand–Tsetlin basis. |

## Citation

If you use this code, please cite [arXiv:2310.02252](https://arxiv.org/abs/2310.02252).
