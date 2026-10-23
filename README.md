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
| [`Bratteli diagram.nb`](Bratteli%20diagram.nb) | Draws the Bratteli diagrams of the walled Brauer algebra and of $U(d)$, and lists the irreps with their dimensions, the paths to one irrep as mixed Young tableaux, and its GT patterns. |
| [`Matrix Units.nb`](Matrix%20Units.nb) | Builds the matrix units of the algebra in the Gelfand–Tsetlin basis with `MatrixUnit`, shows them in the mixed Schur basis, and checks their multiplication rule. |
| [`v1/`](v1) | Notebooks for version 1 of the paper (see [below](#v1-notebooks-of-the-first-arxiv-version)). |

## Getting started

The package needs Wolfram Mathematica or the free Wolfram Engine. It was developed with Mathematica 14.0. Load the package with `Get`:

```mathematica
Get["/path/to/walledbrauer-gtbasis/Mixed Schur Tools.wl"]

(* from a notebook saved in the repository folder *)
Get[FileNameJoin[{NotebookDirectory[], "Mixed Schur Tools.wl"}]]

(* from a notebook in the v1 folder *)
Get[FileNameJoin[{ParentDirectory[NotebookDirectory[]], "Mixed Schur Tools.wl"}]]
```

The notebooks are saved without outputs. Open one and choose Evaluation > Evaluate Notebook to see the results. The setup cells load the package, set the default parameters, and initialize the display helpers. Mathematica offers to evaluate these initialization cells when needed. Each notebook uses its own context, so its example variables stay independent when several notebooks are open. Display helpers are in a closed group under Setup; expand it to customize the presentation.

Load the package before you evaluate any cell that uses its functions. If a cell that mentions, say, `CG` runs first, Mathematica creates an empty ``Global`CG`` and reports `CG::shdw` when the package loads. Definitions evaluated before loading keep referring to that empty symbol. To recover, run ``Remove["Global`CG"]`` and evaluate those cells again, or quit the kernel and evaluate the notebook from the top.

A short session for $n = 2$, $m = 1$, $d = 2$:

```mathematica
{n, m, d} = {2, 1, 2};

Irreps[n, m, d]                 (* {{2, -1}, {1, 0}}  irreps as staircases *)
IrrepDimsWBA[n, m, d]           (* {1, 2}             dimensions of the walled Brauer irreps *)
IrrepDimsGL[n, m, d]            (* {4, 2}             dimensions of the U(d) irreps; 1*4 + 2*2 = 2^3 *)

BratteliDiagramWBALabelled[n, m, d]       (* draw the Bratteli diagram *)
PathsToIrrepWBA[{1, 0}, n, m, d]          (* GT basis of the irrep {1, 0}: the two paths
                                             {1, 0} -> {2, 0} -> {1, 0} and {1, 0} -> {1, 1} -> {1, 0} *)
PathToYoungTableaux[{{1, 0}, {2, 0}, {1, 0}}]
                                          (* {{{{1}, {2, 3}}}, {}}: step 3 removes the cell that step 2 added *)
DisplayPath /@ PathsToIrrepWBA[{1, 0}, n, m, d]   (* draw the paths as mixed Young tableaux *)
GTPatterns[{1, 0}]                        (* GT basis of the U(2) irrep {1, 0}: {{{1}, {1, 0}}, {{0}, {1, 0}}} *)

gens = GeneratorsGT[n, m, d];   (* matrices of sigma_1, sigma_2 (sigma_n is the contraction), indexed [[i, irrep]] *)
CheckRelationsWBA[gens[[All, 2]], n, m, d]   (* the walled Brauer relations in the irrep {1, 0}: all True *)
CG[{1, 0}, {2, 0}]              (* Clebsch-Gordan tensor for {1, 0} (x) C^2 -> {2, 0} *)
S = SchurTransform[n, m, d];    (* 8 x 8 mixed Schur transform, a SparseArray *)
MatrixUnit[{{1, 0}, {2, 0}, {1, 0}}, {{1, 0}, {1, 1}, {1, 0}}]   (* 8 x 8 matrix unit of the algebra *)
```

Every exported function has a usage message, so `?SchurTransform` describes a single function and ``?MixedSchurTools`*`` lists them all.

## Validation

Open each notebook in Wolfram's front end and choose Evaluation > Evaluate Notebook.
The dimension identity in `Bratteli diagram.nb` and both matrix-unit checks in `Matrix Units.nb` should return `True`.
In `v1/wba_gt_basis_demonstration.nb`, the generator relations should all hold, and the final tensor-space comparison should return `{True, True, True}`.
In `v1/port-based teleportation.nb`, the ordinary and dilated generator checks should return `True`.
The final dilated measurement's commutation table should contain only `yes`, and its spectra should contain only 0 and 1; multiplicities are shown in parentheses.
The earlier, undilated measurement can have noncommuting elements.

## Conventions

| Object | Representation |
| --- | --- |
| **staircase** | A non-increasing integer list of length $d$ that labels an irrep, e.g. `{2, 1, 0, -1}`. Its positive entries form the "left" partition and its negative entries the reversed "right" partition. `ToStaircase[{{2, 1}, {1}, 4}]` gives `{2, 1, 0, -1}`, and `ToPair` converts back. |
| **vertex** | A vertex `{staircase, level}` of the walled Brauer Bratteli diagram, with `level` from `0` to `n + m`. A step to one of the levels `1..n` adds a cell to the left partition. A step to one of the levels `n+1..n+m` either adds a cell to the right partition or removes one from the left partition. |
| **path** | A list `{T_1, ..., T_(n+m)}` of staircases from the root (omitted) to an irrep. Paths label the GT basis of the walled Brauer irreps. |
| **mixed Young tableaux** | The pair `{left, right}` of tableaux equivalent to a path, each a list of rows of cell labels. Step `i` labels the cell it adds by `{i}`. A step that removes a cell from the left partition appends its number to that cell's label, so `{2, 3}` is a cell that step 2 added and step 3 removed. |
| **GT pattern** | A list of rows `{P_1, ..., P_d}`, where row `k` has length `k`, consecutive rows interlace, and `P_d` is the irrep. Patterns label the GT basis of $U(d)$ irreps. |
| **string** | A list `x` of `n + m` letters from `1..d` that labels the standard basis vector $\lvert x_1 \dots x_{n+m}\rangle$. |
| **Schur basis** | Pairs `{T, P}` of a path and a GT pattern of the same irrep. They are ordered by irrep (as in `Irreps`), then by path, then by pattern. |

Row `i` of `SchurTransform[n, m, d]` is the Schur basis vector `SchurBasis[n, m, d][[i]]`. Column `j` is the string `StandardBasis[n + m, d][[j]]`, so strings are in lexicographic order.

## Computation and memory

`SchurTransform` assembles sparse Clebsch–Gordan blocks along each path and shares common path prefixes during the calculation.
The intermediate prefix matrices are released after each call.
`SchurTransformSlow` provides the entry-by-entry calculation for comparison, and `SchurCoef` computes individual coefficients.
All three use exact arithmetic and the same basis ordering.
For exact matrix comparisons, simplify the difference, since multiplication order can change the forms of radical expressions.

`IrrepDimsWBA` counts paths by integer dynamic programming, so dimension queries do not enumerate the basis paths.
Path queries use adjacency lists; the diagram functions construct `Graph` objects for display.
Queries restricted to a string reuse GT patterns grouped by weight.
Many package functions cache their results; loading the package again with `Get` clears these caches.
The full transform still has `d^(n+m)` rows and columns, so its output size limits the parameters that can be computed in memory.

## Function reference: `Mixed Schur Tools.wl`

**Staircases and Young diagrams**

| Function | Description |
| --- | --- |
| `ToStaircase[{left, right, d}]`, `ToPair[staircase]` | Convert between a pair of partitions and a staircase. |
| `DisplayStaircase[staircase]` | Draw a staircase as two Young diagrams separated by a wall. |
| `TransposePartition`, `AddCell`, `AddableCells` | Basic operations on partitions. |
| `AddableCellPositions[λ]`, `RemovableCellPositions[λ]`, `CellContent[{row, column}]` | Positions of the cells that can be added to or removed from a Young diagram, and the content `column - row` of a cell. |
| `TransitionWeight[λ, a]` | Transition probability of the addable cell `a` of `λ`. The weights of all addable cells sum to 1. |
| `Id[n]`, `Enumerate[list]` | Sparse identity matrix, and pairs `{element, position}`. |

**Walled Brauer algebra**

| Function | Description |
| --- | --- |
| `BratteliLevelsWBA`, `BratteliDiagramWBA`, `BratteliDiagramWBALabelled` | Vertices by level, the Bratteli diagram as a `Graph`, and a drawing with labelled vertices. `BratteliDiagramWBA[levels]` draws a diagram with modified levels. |
| `OrderWBA[u, v]` | Edge relation of the Bratteli diagram. |
| `Irreps[n, m, d]` | Irreps appearing in $(\mathbb{C}^d)^{\otimes n} \otimes (\mathbb{C}^{d*})^{\otimes m}$. |
| `PathsToIrrepWBA`, `AllPathsWBA`, `IrrepDimWBA`, `IrrepDimsWBA` | GT basis paths and dimensions of the walled Brauer irreps. `AllPathsWBA[levels]` gives the paths in a diagram with modified levels. |
| `PathToYoungTableaux[T]`, `DisplayYoungTableaux[{left, right}]`, `DisplayYoungTableau[t]`, `DisplayPath[T]` | A path as a pair of mixed Young tableaux, and drawings of a pair, of a single tableau and of a path. |
| `AssociationIrrepsWBA`, `AssociationPathsToIrrepWBA` | Positions of irreps and of paths. |

**Unitary group**

| Function | Description |
| --- | --- |
| `GTPatterns[λ]`, `AssociationGTPatterns[λ]` | GT patterns of a $U(d)$ irrep and their positions. |
| `WeylDim[λ]`, `WeylDim[λ, d]`, `IrrepDimsGL[n, m, d]` | Dimensions of $U(d)$ irreps, labelled by a staircase or by a partition. |
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
| `SchurTransform[n, m, d]` | The mixed Schur transform, assembled from sparse Clebsch–Gordan blocks. |
| `SchurTransformSlow[n, m, d]` | The same matrix, computed entry by entry. |
| `SchurBasis`, `SchurIndex`, `StandardBasis` | Row and column labels of the transform. |
| `SchurCoef[x, {T, P}]`, `CGmatProduct[x, T]` | Individual coefficients $\langle T, P \vert x\rangle$. |
| `Weight`, `GTPatternsWeight` | $U(d)$ weights of strings and of GT patterns. |
| `BratteliLevelsWBAString`, `BratteliDiagramWBAString`, `AllPathsWBAString`, `SchurBasisGivenString` | Bratteli diagram and Schur basis restricted to one string, for computing or inspecting the entries that can be non-zero. |

**Gelfand–Tsetlin basis of the partially transposed permutations**

| Function | Description |
| --- | --- |
| `GeneratorsGT[n, m, d]` | Matrices of all generators $\sigma_1, \dots, \sigma_{n+m-1}$, one per irrep. |
| `TranspositionGT[i, n, m, d]` | Transposition $(i, i+1)$ for $i \ne n$, from Young's orthogonal form. |
| `ContractionGT[n, m, d]` | The contraction $\sigma_n$. Its option `"Weight"` replaces the weights $(d + c(a))\,$`TransitionWeight[μ, a]` of the cells, for example by `TransitionWeight` for the projector of the Naimark dilation. |
| `WalledContent`, `AxialDistance` | Signed contents of cells along a path, and the axial distances that define the transpositions. |
| `CheckRelationsWBA[σ, n, m, d]` | Checks the defining relations of the walled Brauer algebra for the generator matrices `σ` of one irrep. |
| `MatrixUnit[T, S]` | The matrix unit that maps the GT basis vector `S` to `T`, as an operator on the tensor space. |

`GeneratorsGT`, `TranspositionGT` and `ContractionGT` take an optional list of paths per irrep after `n, m, d`, such as `AllPathsWBA[levels]` for modified levels, and use it as the basis instead of `AllPathsWBA[n, m, d]`.

The old names `InterlacingCanditates`, `transpostionGT`, `contractionGT` and `generatorsGT` still work as aliases.

## v1: notebooks of the first arXiv version

The [`v1`](v1) folder holds the notebooks for [arXiv:2310.02252v1](https://arxiv.org/abs/2310.02252v1). They use only the main package.

| File | Description |
| --- | --- |
| [`wba_gt_basis_demonstration.nb`](v1/wba_gt_basis_demonstration.nb) | Demonstrates the Bratteli diagram, the irreps, the mixed Young tableaux and the generator matrices, and checks the relations. It also checks that the mixed Schur transform block-diagonalizes the generators acting on the tensor space. |
| [`port-based teleportation.nb`](v1/port-based%20teleportation.nb) | Applies the code to port-based teleportation. It builds the pretty good measurement and a Naimark-dilated projective measurement in the Gelfand–Tsetlin basis. |

The first version of this code was a separate package, `v1/walled_brauer_gt_basis.wl`, that labelled irreps by pairs of partitions and called the parameters `p, q, d`. Its functions are now part of `Mixed Schur Tools.wl`:

| v1 function | Package function |
| --- | --- |
| `BratteliLevels`, `BratteliDiagram`, `Irreps`, `AllPaths`, `IrrepDims` | `BratteliLevelsWBA`, `BratteliDiagramWBA`, `Irreps`, `AllPathsWBA`, `IrrepDimsWBA` (staircases instead of pairs of partitions) |
| `PathToYoungTableauxPair`, `TransformAllPathToYT` | `PathToYoungTableaux`, `Map[PathToYoungTableaux, AllPathsWBA[n, m, d], {2}]` |
| `DisplayYoungDiagram`, `DisplayYoungTableaux` (one tableau), `DisplayYoungTableauxPair` | `DisplayStaircase`, `DisplayYoungTableau`, `DisplayYoungTableaux` (a pair) |
| `DisplayPathAsYT`, `DisplayAllPathsAsYT` | `DisplayPath`, `Map[DisplayPath, AllPathsWBA[n, m, d], {2}]` |
| `AddCellPositions`, `RemoveCellPositions`, `Content`, `ConjugatePartition`, `m[λ, d]` | `AddableCellPositions`, `RemovableCellPositions`, `CellContent`, `TransposePartition`, `WeylDim[λ, d]` |
| `wCoord`, `HookDistance` (axial distances in walled coordinates) | `WalledContent`, `AxialDistance` |
| `AllGeneratorsGT[p, q, d, paths]` | `GeneratorsGT[n, m, d, paths]` |
| `CheckRelations` | `CheckRelationsWBA` |

## Citation

If you use this code, please cite [arXiv:2310.02252](https://arxiv.org/abs/2310.02252).
