(* ::Package:: *)

(* ::Title:: *)
(*Mixed Schur Tools*)


(* ::Text:: *)
(*Representation theory of the mixed Schur-Weyl duality on (C^d)^(tensor n) (x) (dual of C^d)^(tensor m):*)
(*the unitary group U(d) acts as U^(tensor n) (x) conj(U)^(tensor m), and the algebra of partially transposed*)
(*permutations (walled Brauer algebra) acts by permuting and contracting the tensor factors.*)
(**)
(*Load with  Get["/path/to/Mixed Schur Tools.wl"]  and see the README for an overview.*)
(**)
(*Conventions used throughout the package:*)
(*  staircase   a non-increasing integer list of length d labelling an irrep of U(d), e.g. {2, 1, 0, -1}.*)
(*              Its positive entries form the "left" partition, its negative entries the reversed "right" one.*)
(*  vertex      a vertex {staircase, level} of the walled Brauer Bratteli diagram, level = 0, ..., n + m.*)
(*  path        a list {T_1, ..., T_(n+m)} of staircases leading from the root to an irrep (root omitted).*)
(*              Paths label the Gelfand-Tsetlin basis of the walled Brauer algebra irreps.*)
(*  GT pattern  a list of rows {P_1, ..., P_d}, row k of length k, with P_d = lambda.*)
(*              Patterns label the Gelfand-Tsetlin basis of the U(d) irrep lambda.*)
(*  string      a list x of n + m letters from {1, ..., d}, labelling the standard basis vector |x_1 ... x_(n+m)>.*)
(*  tableaux    the pair {left tableau, right tableau} of mixed Young tableaux equivalent to a path: step i labels*)
(*              the cell it adds by {i}; a step that removes a cell of the left tableau appends i to its label.*)


BeginPackage["MixedSchurTools`"];

(* Reloading the file starts from a clean state, including all memoized values *)
ClearAll["MixedSchurTools`*", "MixedSchurTools`Private`*"];


(* ::Section:: *)
(*Public interface*)


(* ::Subsection:: *)
(*Staircases and Young diagrams*)


ToStaircase::usage = "ToStaircase[{\[Lambda], \[Mu], d}] combines the partitions \[Lambda] (left) and \[Mu] (right), with Length[\[Lambda]] + Length[\[Mu]] <= d, into a staircase of length d: \[Lambda] padded with zeros minus \[Mu] reversed.";
ToPair::usage = "ToPair[\[Lambda]] splits the staircase \[Lambda] into {left partition, right partition, d}. It is the inverse of ToStaircase.";
TransposePartition::usage = "TransposePartition[\[Lambda]] gives the conjugate (transposed) partition of \[Lambda].";
AddCell::usage = "AddCell[\[Lambda], i] adds a cell to row i of \[Lambda].";
AddableCells::usage = "AddableCells[\[Lambda]] lists the rows of \[Lambda] (a list of fixed length) to which a cell can be added so that \[Lambda] stays non-increasing.";
AddableCellPositions::usage = "AddableCellPositions[\[Lambda]] lists the positions {row, column} of the cells that can be added to the Young diagram of the partition \[Lambda], including the first cell of a new row.";
RemovableCellPositions::usage = "RemovableCellPositions[\[Lambda]] lists the positions {row, column} of the cells that can be removed from the Young diagram of the partition \[Lambda].";
CellContent::usage = "CellContent[{row, column}] gives the content column - row of a cell of a Young diagram.";
TransitionWeight::usage = "TransitionWeight[\[Lambda], a] gives the transition probability of the addable cell a of the partition \[Lambda]: the product of c(a) - c(r) over the removable cells r divided by the product of c(a) - c(b) over the other addable cells b, where c is the content. The weights of all addable cells sum to 1, and (d + c(a)) TransitionWeight[\[Lambda], a] is the ratio of the dimensions of the U(d) irreps \[Lambda] + a and \[Lambda].";
DisplayStaircase::usage = "DisplayStaircase[\[Lambda]] draws the staircase \[Lambda] as two Young diagrams separated by a thick wall: positive rows to the right of the wall, negative rows to the left.";
Id::usage = "Id[n] gives the n\[Times]n identity matrix as a SparseArray.";
Enumerate::usage = "Enumerate[list] pairs every element of list with its position: {{e1, 1}, {e2, 2}, ...}.";


(* ::Subsection:: *)
(*Walled Brauer algebra*)


BratteliLevelsWBA::usage = "BratteliLevelsWBA[n, m, d] gives the vertices {\[Lambda], level} of the Bratteli diagram of the walled Brauer algebra acting on (C^d)^n \[CircleTimes] (C^d*)^m, grouped by level 0, ..., n + m.";
OrderWBA::usage = "OrderWBA[u, v] is True if the walled Brauer Bratteli diagram has an edge from vertex u to vertex v: v is one level higher and its staircase differs from that of u in a single entry.";
BratteliDiagramWBA::usage = "BratteliDiagramWBA[n, m, d] gives the walled Brauer Bratteli diagram as a Graph. Hover over a vertex to see its staircase.\nBratteliDiagramWBA[levels] gives the Bratteli diagram with the given levels of vertices, such as a modified BratteliLevelsWBA[n, m, d].";
BratteliDiagramWBALabelled::usage = "BratteliDiagramWBALabelled[n, m, d] draws the walled Brauer Bratteli diagram with every vertex labelled by its staircase.";
Irreps::usage = "Irreps[n, m, d] lists the staircases of the irreps appearing in the mixed Schur-Weyl duality on (C^d)^n \[CircleTimes] (C^d*)^m.";
PathsToIrrepWBA::usage = "PathsToIrrepWBA[\[Lambda], n, m, d] lists the paths of n + m staircases from the root of the Bratteli diagram to the irrep \[Lambda]. They label the Gelfand-Tsetlin basis of the walled Brauer irrep \[Lambda].";
IrrepDimWBA::usage = "IrrepDimWBA[\[Lambda], n, m, d] gives the dimension of the walled Brauer irrep \[Lambda].";
AllPathsWBA::usage = "AllPathsWBA[n, m, d] gives PathsToIrrepWBA for every irrep in Irreps[n, m, d].\nAllPathsWBA[levels] lists, for every vertex of the last level, the paths from the root in BratteliDiagramWBA[levels].";
IrrepDimsWBA::usage = "IrrepDimsWBA[n, m, d] gives the dimensions of the walled Brauer irreps, in the order of Irreps[n, m, d].";
AssociationIrrepsWBA::usage = "AssociationIrrepsWBA[n, m, d] maps every irrep to its position in Irreps[n, m, d].";
AssociationPathsToIrrepWBA::usage = "AssociationPathsToIrrepWBA[\[Lambda], n, m, d] maps every path to \[Lambda] to its position in PathsToIrrepWBA[\[Lambda], n, m, d].";

PathToYoungTableaux::usage = "PathToYoungTableaux[T] gives the pair {left tableau, right tableau} of mixed Young tableaux equivalent to the path T. Step i labels the cell it adds by {i}; a step that removes a cell from the left partition appends i to the label of that cell. A tableau is a list of rows, a row a list of cell labels.";
DisplayYoungTableau::usage = "DisplayYoungTableau[t] draws one Young tableau t, given as a list of rows of cell labels; the empty tableau is drawn as \[EmptySet].";
DisplayYoungTableaux::usage = "DisplayYoungTableaux[{left, right}] draws a pair of mixed Young tableaux side by side.";
DisplayPath::usage = "DisplayPath[T] draws the path T as its pair of mixed Young tableaux.";


(* ::Subsection:: *)
(*Unitary group*)


InterlacingCandidates::usage = "InterlacingCandidates[\[Lambda]] lists all rows \[Mu] of length Length[\[Lambda]] - 1 that interlace \[Lambda], i.e. \[Lambda][[i]] >= \[Mu][[i]] >= \[Lambda][[i + 1]], in reverse lexicographic order.";
OrderGL::usage = "OrderGL[\[Mu], \[Lambda]] is True if \[Mu] is one entry shorter than \[Lambda] and interlaces it.";
BratteliLevelsGL::usage = "BratteliLevelsGL[n, m, d] gives the levels of the Bratteli diagram of the chain U(0) \[Subset] U(1) \[Subset] ... \[Subset] U(d) that lead to the irreps Irreps[n, m, d].";
BratteliDiagramGL::usage = "BratteliDiagramGL[n, m, d] gives the Bratteli diagram with levels BratteliLevelsGL[n, m, d] as a Graph.";
AllGTPatterns::usage = "AllGTPatterns[n, m, d] lists, for every irrep in Irreps[n, m, d], its Gelfand-Tsetlin patterns, found as paths in BratteliDiagramGL[n, m, d].";
IrrepDimsGL::usage = "IrrepDimsGL[n, m, d] gives the dimensions of the U(d) irreps, in the order of Irreps[n, m, d].";
GTPatterns::usage = "GTPatterns[\[Lambda]] lists the Gelfand-Tsetlin patterns {P_1, ..., P_d} (row k of length k, P_d = \[Lambda]) of the U(d) irrep \[Lambda] in reverse lexicographic order. They label its Gelfand-Tsetlin basis.";
WeylDim::usage = "WeylDim[\[Lambda]] gives the dimension of the U(d) irrep \[Lambda], d = Length[\[Lambda]], by the Weyl dimension formula.\nWeylDim[\[Lambda], d] gives the dimension of the U(d) irrep labelled by the partition \[Lambda], by the hook-content formula. It is 0 if \[Lambda] has more than d rows, and d may be symbolic.";
AssociationGTPatterns::usage = "AssociationGTPatterns[\[Lambda]] maps every Gelfand-Tsetlin pattern of \[Lambda] to its position in GTPatterns[\[Lambda]].";


(* ::Subsection:: *)
(*Clebsch-Gordan coefficients*)


RWcoef::usage = "RWcoef[{P_k, P_(k+1)}, {w_k, w_(k+1)}, {Q_k, Q_(k+1)}] gives the reduced Wigner coefficient for rows k and k + 1 of three Gelfand-Tsetlin patterns: P of \[Mu], w of a basis vector of C^d or of its dual, and Q of \[Lambda]. CGcoef[P, x, Q] is a product of such factors.";
CGcoef::usage = "CGcoef[P, x, Q] gives the Clebsch-Gordan coefficient <Q|(|P> \[CircleTimes] |x>) for Gelfand-Tsetlin patterns P and Q. Here |x> is the basis vector e_x of C^d if x > 0, and the basis vector e_(-x) of the dual space C^d* if x < 0.";
GTcandidates::usage = "GTcandidates[\[Lambda], P, x] lists the Gelfand-Tsetlin patterns Q of \[Lambda] for which CGcoef[P, \[PlusMinus]x, Q] can be non-zero.";
CG::usage = "CG[\[Mu], \[Lambda]] gives the Clebsch-Gordan tensor with entries C[[x, i, j]] = CGcoef[GTPatterns[\[Mu]][[i]], \[PlusMinus]x, GTPatterns[\[Lambda]][[j]]], for \[Mu] \[CircleTimes] C^d \[RightArrow] \[Lambda] if \[Lambda] is \[Mu] with one entry increased by 1 (sign +), or \[Mu] \[CircleTimes] C^d* \[RightArrow] \[Lambda] if \[Lambda] is \[Mu] with one entry decreased by 1 (sign -).\nCG[\[Mu], \[Lambda], d] first pads \[Mu] and \[Lambda] with zeros to length d.";


(* ::Subsection:: *)
(*Mixed Schur transform*)


Weight::usage = "Weight[x, n, m, d] gives the U(d) weight of the string x: how many times each letter 1, ..., d occurs among the first n letters, minus how many times it occurs among the last m letters.\nWeight[x, i, n, m, d] gives the weight of the first i letters of x.\nWeight[x, {n, m, d}] is Weight[x, n, m, d].";
SchurBasis::usage = "SchurBasis[n, m, d] lists the mixed Schur basis vectors {T, P}, where T is a path to an irrep and P a Gelfand-Tsetlin pattern of the same irrep. They are ordered by irrep (as in Irreps), then by path, then by pattern.";
SchurIndex::usage = "SchurIndex[{T, P}, n, m, d] gives the position of the Schur basis vector {T, P} in SchurBasis[n, m, d].";
StandardBasis::usage = "StandardBasis[k, d] lists the strings of length k over {1, ..., d} in lexicographic order.";
CGmatProduct::usage = "CGmatProduct[x, T] multiplies the Clebsch-Gordan tensors along the path T for the string x. Entry j of the result is the Schur transform coefficient <T, GTPatterns[Last[T]][[j]]|x>.";
SchurCoef::usage = "SchurCoef[x, {T, P}] gives the mixed Schur transform coefficient <T, P|x>.";
SchurTransformSlow::usage = "SchurTransformSlow[n, m, d] gives the d^(n+m)\[Times]d^(n+m) mixed Schur transform, computing every entry. Row i corresponds to SchurBasis[n, m, d][[i]], column j to StandardBasis[n + m, d][[j]].";
SchurTransform::usage = "SchurTransform[n, m, d] gives the same matrix as SchurTransformSlow[n, m, d], assembling sparse Clebsch-Gordan blocks along the paths instead of computing entries separately.";

GTPatternsWeight::usage = "GTPatternsWeight[\[Lambda], w] lists the Gelfand-Tsetlin patterns of \[Lambda] with weight w.";
BratteliLevelsWBAString::usage = "BratteliLevelsWBAString[x, n, m, d] keeps only those vertices of BratteliLevelsWBA[n, m, d] whose U(d) irrep contains the weight of the prefix of the string x of the same length.";
BratteliDiagramWBAString::usage = "BratteliDiagramWBAString[x, n, m, d] gives the Bratteli diagram with levels BratteliLevelsWBAString[x, n, m, d] as a Graph.";
AllPathsWBAString::usage = "AllPathsWBAString[x, n, m, d] lists, grouped by irrep, the paths in BratteliDiagramWBAString[x, n, m, d]: the only paths T for which <T, P|x> can be non-zero.";
SchurBasisGivenString::usage = "SchurBasisGivenString[x, n, m, d] lists the Schur basis vectors {T, P} for which <T, P|x> can be non-zero.";


(* ::Subsection:: *)
(*Gelfand-Tsetlin basis of the partially transposed permutations*)


WalledContent::usage = "WalledContent[T, i] gives the signed content of the cell that step i of the path T changes: CellContent[cell] if the step adds the cell to the left partition, -CellContent[cell] if it removes the cell from the left partition, and the walled content d - k + c if it adds the cell in row k and column c to the right partition, where d is the length of the staircases.\nWalledContent[T, i, d] uses the given d instead of the length of the staircases, which allows staircases padded beyond length d.";
AxialDistance::usage = "AxialDistance[T, i] gives WalledContent[T, i + 1] - WalledContent[T, i], which determines how the transposition (i, i + 1) acts on the Gelfand-Tsetlin basis vector T.\nAxialDistance[T, i, d] uses WalledContent[T, i, d].";
TranspositionGT::usage = "TranspositionGT[i, n, m, d] gives, for every irrep in Irreps[n, m, d], the matrix of the transposition (i, i + 1), i != n, in the Gelfand-Tsetlin basis PathsToIrrepWBA.\nTranspositionGT[i, n, m, d, paths] uses as basis the given list of paths for each irrep, such as AllPathsWBA[levels] for modified Bratteli levels.";
ContractionGT::usage = "ContractionGT[n, m, d] gives, for every irrep in Irreps[n, m, d], the matrix of the contraction generator (partial transpose of the swap of tensor factors n and n + 1) in the Gelfand-Tsetlin basis PathsToIrrepWBA.\nContractionGT[n, m, d, paths] uses as basis the given list of paths for each irrep.\nWith the option \"Weight\" -> w, the coefficient of the path through T_(n-1) + a in the image of a path through T_(n-1) + b is Sqrt[w[\[Mu], a] w[\[Mu], b]], where \[Mu] is the partition T_(n-1); the default is w[\[Mu], a] = (d + CellContent[a]) TransitionWeight[\[Mu], a]. \"Weight\" -> TransitionWeight gives the rank-one projectors used for the Naimark dilation of port-based teleportation.";
GeneratorsGT::usage = "GeneratorsGT[n, m, d] gives the Gelfand-Tsetlin basis matrices of all generators \[Sigma]_1, ..., \[Sigma]_(n+m-1): TranspositionGT for i != n and ContractionGT for i = n. The result is indexed as [[i, irrep]].\nGeneratorsGT[n, m, d, paths] uses as basis the given list of paths for each irrep.";
CheckRelationsWBA::usage = "CheckRelationsWBA[{\[Sigma]_1, ..., \[Sigma]_(n+m-1)}, n, m, d] checks the defining relations of the walled Brauer algebra for the matrices \[Sigma]_i of its generators in one representation, \[Sigma]_n being the contraction. It gives an Association from each family of relations to the list of its results; all of them are True for a representation.";
MatrixUnit::usage = "MatrixUnit[T, S] gives, as a d^(n+m)\[Times]d^(n+m) matrix in the standard basis, the matrix unit of the walled Brauer algebra that maps the Gelfand-Tsetlin basis vector S to T, for two paths T and S to the same irrep: the sum over all Gelfand-Tsetlin patterns P of |T, P><S, P|.";


(* ::Subsection:: *)
(*Deprecated names*)


InterlacingCanditates::usage = "InterlacingCanditates is a deprecated name of InterlacingCandidates.";
transpostionGT::usage = "transpostionGT is a deprecated name of TranspositionGT.";
contractionGT::usage = "contractionGT is a deprecated name of ContractionGT.";
generatorsGT::usage = "generatorsGT is a deprecated name of GeneratorsGT.";


ToStaircase::height = "The partitions `1` and `2` have more than `3` rows in total.";
CG::length = "The staircases `1` and `2` have different lengths.";
CG::step = "The staircase `2` is not obtained from `1` by increasing or decreasing a single entry by 1.";
TranspositionGT::contraction = "The generator `1` = n is the contraction, not a transposition. Use ContractionGT instead.";
ContractionGT::none = "There is no contraction generator for n = `1`, m = `2`: both must be positive.";
GeneratorsGT::path = "The path `1` that a generator maps to is not among the given paths; its matrix entry is dropped.";
MatrixUnit::irrep = "The paths `1` and `2` lead to different irreps.";


Begin["`Private`"];


(* ::Section:: *)
(*Helpers*)


(* All-zero staircase of the root of the Bratteli diagrams *)
zeroStaircase[d_] := ConstantArray[0, d]

(* The path T with the root staircase prepended, so that path[[k + 1]] = T_k and path[[1]] = T_0 *)
withRoot[T_] := Prepend[T, zeroStaircase@Length@Last@T]

(* Association from the elements of list to their positions *)
indexAssociation[list_] := AssociationThread[list -> Range@Length@list]

(* Product of all entries of list except the k-th one *)
productExcept[list_, k_] := Times @@ Delete[list, k]

(* The position i with  new == old + s UnitVector[Length[old], i],  or None if there is no such i *)
stepPosition[old_, new_, s_] := With[{diff = new - old},
	If[Count[diff, 0] == Length@diff - 1 && Count[diff, s] == 1, First@FirstPosition[diff, s], None]
]

(* What a step from the staircase before to the staircase after does, as {"add", cell} or {"remove", cell} for a cell
   {row, column} of the left partition, or {"right", cell} for a cell added to the right partition. Its row k sits at
   entry L - k + 1 of a staircase of length L. *)
stepCell[before_, after_] := With[{r = First@FirstPosition[Abs[after - before], 1]},
	Which[
		after[[r]] > before[[r]], {"add", {r, after[[r]]}},
		before[[r]] > 0, {"remove", {r, before[[r]]}},
		True, {"right", {Length@after - r + 1, 1 - before[[r]]}}
	]
]

(* FindPath omits the trivial path from a vertex to itself, which is the unique path for an empty tensor product *)
allPathsOfLength[graph_, root_, vertex_, length_] := If[length == 0,
	If[root === vertex, {{root}}, {}],
	FindPath[graph, root, vertex, {length}, All]
]

(* An empty path ends at the root staircase; its dimension must be supplied explicitly *)
pathIrrep[T_, d_] := If[T === {}, zeroStaircase[d], Last@T]

(* Vertex labels showing the staircase of every vertex as a tooltip *)
tooltipLabels[vertices_, staircaseOf_] := Table[v -> Placed[DisplayStaircase@staircaseOf@v, Tooltip], {v, vertices}]

(* Coordinates follow Catenate[levels], keeping the vertex and path ordering unchanged. *)
centeredLevelCoordinates[levels_] := Catenate@MapIndexed[
	Function[{level, index}, Table[{j - (Length@level + 1)/2, -0.85 (First@index - 1)}, {j, Length@level}]],
	levels
]


(* ::Section:: *)
(*Staircases and Young diagrams*)


ToStaircase[{left_, right_, d_}] := If[Length@left + Length@right > d,
	Message[ToStaircase::height, left, right, d]; $Failed,
	PadRight[left, d] - PadLeft[Reverse@right, d]
]

ToPair[\[Lambda]_] := {Select[\[Lambda], # > 0 &], -Reverse@Select[\[Lambda], # < 0 &], Length@\[Lambda]}

TransposePartition[{}] = {};
TransposePartition[\[Lambda]_] := Table[Count[\[Lambda], row_ /; row >= i], {i, First@\[Lambda]}]

AddCell[\[Lambda]_, i_] := \[Lambda] + UnitVector[Length@\[Lambda], i]

AddableCells[\[Lambda]_] := Prepend[Select[Range[2, Length@\[Lambda]], \[Lambda][[# - 1]] > \[Lambda][[#]] &], 1]

CellContent[{row_, column_}] := column - row

AddableCellPositions[\[Lambda]_] := With[{rows = Append[DeleteCases[\[Lambda], 0], 0]},
	Table[If[i == 1 || rows[[i]] < rows[[i - 1]], {i, rows[[i]] + 1}, Nothing], {i, Length@rows}]
]

RemovableCellPositions[\[Lambda]_] := With[{rows = DeleteCases[\[Lambda], 0]},
	Table[If[i == Length@rows || rows[[i]] > rows[[i + 1]], {i, rows[[i]]}, Nothing], {i, Length@rows}]
]

TransitionWeight[\[Lambda]_, a_] :=
	Product[CellContent@a - CellContent@r, {r, RemovableCellPositions@\[Lambda]}] /
	Product[CellContent@a - CellContent@b, {b, DeleteCases[AddableCellPositions@\[Lambda], a]}]

Id[dim_] := SparseArray[{Band[{1, 1}] -> 1}, {dim, dim}]

Enumerate[list_List] := MapIndexed[{#1, First@#2} &, list]

(* Row i holds Abs[\[Lambda][[i]]] framed cells: to the right of the wall if \[Lambda][[i]] > 0, to its left if \[Lambda][[i]] < 0 *)
DisplayStaircase[\[Lambda]_] := If[AllTrue[\[Lambda], # == 0 &],
	"\[EmptySet]",
	With[{rows = Take[\[Lambda], Last@Flatten@Position[\[Lambda], Except[0], {1}]]},
	With[{wall = Max[0, -Min@rows]},
		Grid[
			ConstantArray["", {Length@rows, wall + Max[0, Max@rows]}],
			Alignment -> Center,
			ItemSize -> {1.6, 1.3},
			Spacings -> {0, 0},
			Dividers -> {{wall + 1 -> Directive[AbsoluteThickness[2.5]]}},
			Frame -> {None, None, Flatten@Table[
				{i, j + wall} -> True,
				{i, Length@rows}, {j, Min[rows[[i]], 0] + 1, Max[rows[[i]], 0]}
			]}
		]
	]
	]
]


(* ::Section:: *)
(*Walled Brauer algebra: Bratteli diagram, irreps and paths*)


(* Pairs of partitions (\[Lambda] of n - k, \[Mu] of m - k) with at most d rows in total, k = 0, ..., Min[n, m] *)
Irreps[n_, m_, d_] := Irreps[n, m, d] = Flatten[
	Table[
		ToStaircase[{\[Lambda], \[Mu], d}],
		{k, 0, Min[n, m]}, {\[Lambda], IntegerPartitions[n - k, d]}, {\[Mu], IntegerPartitions[m - k, d - Length@\[Lambda]]}
	],
	2
]

(* Levels 0, ..., n hold the partitions of the level; level n + i holds the irreps for (n, i) *)
BratteliLevelsWBA[n_, m_, d_] := BratteliLevelsWBA[n, m, d] = Join[
	Table[{ToStaircase[{\[Lambda], {}, d}], i}, {i, 0, n}, {\[Lambda], IntegerPartitions[i, d]}],
	Table[{#, n + i} & /@ Irreps[n, i, d], {i, 1, m}]
]

OrderWBA[{\[Mu]_, i_}, {\[Lambda]_, j_}] := j == i + 1 && Count[\[Mu] - \[Lambda], 0] == Length@\[Mu] - 1

BratteliDiagramWBA[n_, m_, d_] := BratteliDiagramWBA[n, m, d] = BratteliDiagramWBA@BratteliLevelsWBA[n, m, d]

BratteliDiagramWBA[levels_List] := With[{vertices = Catenate@levels},
	RelationGraph[OrderWBA, vertices,
		VertexSize -> 0.2,
		VertexStyle -> Automatic,
		VertexLabels -> tooltipLabels[vertices, First],
		VertexCoordinates -> centeredLevelCoordinates[levels],
		ImagePadding -> 24,
		ImageSize -> 400
	]
]

BratteliDiagramWBALabelled[n_, m_, d_] := With[{levels = BratteliLevelsWBA[n, m, d]},
	With[{vertices = Catenate@levels},
	RelationGraph[OrderWBA, vertices,
		VertexSize -> 0.55,
		VertexShape -> Graphics[{Transparent, Disk[]}],
		VertexStyle -> Automatic,
		VertexLabels -> Table[v -> Placed[DisplayStaircase@First@v, Center], {v, vertices}],
		VertexCoordinates -> centeredLevelCoordinates[levels],
		ImagePadding -> {{42, 42}, {28, 28}},
		ImageSize -> 620
	]
	]
]

(* Computation needs adjacency only, without constructing a styled Graph. Preserve vertex insertion order even
   when custom outer levels differ from the stored level tags. The third list indexes the requested endpoints. *)
wbaPathData[input_List] := wbaPathData[input] = Module[
	{vertices = DeleteDuplicates@Catenate@input, firstTag, levels, terminalIndex, successors},
	firstTag = Last@First@First@input;
	levels = Table[Select[vertices, Last@# == firstTag + i &], {i, 0, Length@input - 1}];
	terminalIndex = indexAssociation@Last@levels;
	successors = Table[
		Table[Reverse@Select[Range@Length@levels[[i + 1]], OrderWBA[vertex, levels[[i + 1, #]]] &],
			{vertex, levels[[i]]}],
		{i, Length@levels - 1}
	];
	{levels, successors, Replace[terminalIndex /@ Last@input, _Missing -> 0, {1}]}
]

(* Descending successors reproduce FindPath's path order; endpoint groups keep the input's terminal order. *)
wbaPathGroups[{levels_, successors_, terminals_}] := Module[{walk, groups, depth = Length@levels},
	walk[level_, index_, prefix_] := If[level == depth,
		Sow[prefix, index],
		Scan[walk[level + 1, #, Append[prefix, levels[[level + 1, #, 1]]]] &, successors[[level, index]]]
	];
	groups = Association[Reap[walk[1, 1, {}], _, Rule][[2]]];
	Table[If[i == 0, {}, Lookup[groups, i, {}]], {i, terminals}]
]

(* A single-irrep query first prunes vertices that cannot reach its endpoint. *)
wbaPathsTo[{levels_, successors_, terminals_}, target_] := Module[
	{reachable, index, walk, harvested, depth = Length@levels},
	index = FirstPosition[Last@levels, target];
	If[MissingQ@index, Return[{}]];
	reachable = Table[{}, {depth}];
	reachable[[-1]] = UnitVector[Length@Last@levels, First@index];
	Do[
		reachable[[level]] = Table[
			Boole@AnyTrue[successors[[level, j]], reachable[[level + 1, #]] == 1 &],
			{j, Length@levels[[level]]}],
		{level, depth - 1, 1, -1}
	];
	If[reachable[[1, 1]] == 0, Return[{}]];
	walk[level_, j_, prefix_] := If[level == depth,
		Sow[prefix],
		Scan[If[reachable[[level + 1, #]] == 1,
			walk[level + 1, #, Append[prefix, levels[[level + 1, #, 1]]]]] &, successors[[level, j]]]
	];
	harvested = Reap[walk[1, 1, {}]][[2]];
	If[harvested === {}, {}, First@harvested]
]

(* Count paths with integer dynamic programming instead of enumerating their exponentially larger list. *)
wbaPathCounts[{levels_, successors_, terminals_}] := Module[
	{counts = UnitVector[Length@First@levels, 1], next},
	Do[
		next = ConstantArray[0, Length@levels[[level + 1]]];
		Do[Scan[(next[[#]] += counts[[vertex]]) &, successors[[level, vertex]]], {vertex, Length@counts}];
		counts = next,
		{level, Length@levels - 1}
	];
	Table[If[i == 0, 0, counts[[i]]], {i, terminals}]
]

PathsToIrrepWBA[\[Lambda]_, n_, m_, d_] := PathsToIrrepWBA[\[Lambda], n, m, d] =
	wbaPathsTo[wbaPathData@BratteliLevelsWBA[n, m, d], {\[Lambda], n + m}]

IrrepDimWBA[\[Lambda]_, n_, m_, d_] := IrrepDimWBA[\[Lambda], n, m, d] = With[
	{index = AssociationIrrepsWBA[n, m, d][\[Lambda]]},
	If[MissingQ@index, 0, IrrepDimsWBA[n, m, d][[index]]]
]

AllPathsWBA[n_, m_, d_] := AllPathsWBA[n, m, d] = Module[
	{paths = wbaPathGroups[wbaPathData@BratteliLevelsWBA[n, m, d]]},
	MapThread[(PathsToIrrepWBA[#1, n, m, d] = #2) &, {Irreps[n, m, d], paths}];
	paths
]

AllPathsWBA[levels_List] := wbaPathGroups@wbaPathData@levels

IrrepDimsWBA[n_, m_, d_] := IrrepDimsWBA[n, m, d] = wbaPathCounts[wbaPathData@BratteliLevelsWBA[n, m, d]]

AssociationIrrepsWBA[n_, m_, d_] := AssociationIrrepsWBA[n, m, d] = indexAssociation@Irreps[n, m, d]

AssociationPathsToIrrepWBA[\[Lambda]_, n_, m_, d_] := AssociationPathsToIrrepWBA[\[Lambda], n, m, d] =
	indexAssociation@PathsToIrrepWBA[\[Lambda], n, m, d]


(* ::Subsection:: *)
(*Mixed Young tableaux*)


PathToYoungTableaux[{}] = {{}, {}};
PathToYoungTableaux[T_] := Module[{path = withRoot@T, steps},
	steps = Table[Append[stepCell[path[[i]], path[[i + 1]]], i], {i, Length@T}];
	{
		toTableau@Cases[steps, {"add", cell_, i_} :> (cell -> Prepend[Cases[steps, {"remove", cell, j_} :> j], i])],
		toTableau@Cases[steps, {"right", cell_, i_} :> (cell -> {i})]
	}
]

(* Rows of a tableau given as a list of rules {row, column} -> label *)
toTableau[cells_] := With[{positions = cells[[All, 1]]},
	Table[Replace[{row, column}, cells], {row, Max[0, First /@ positions]}, {column, Count[positions, {row, _}]}]
]

DisplayYoungTableau[{}] := "\[EmptySet]"
DisplayYoungTableau[tableau_] := Grid[
	Map[Style[StringRiffle[ToString /@ #, ","], LineBreakWithin -> False] &, tableau, {2}],
	Alignment -> Center,
	ItemSize -> {Full, 1.3},
	Spacings -> {0.6, 0},
	Frame -> {None, None, Flatten[Table[{i, j} -> True, {i, Length@tableau}, {j, Length@tableau[[i]]}], 1]}
]

DisplayYoungTableaux[{left_, right_}] := Row[{DisplayYoungTableau@left, DisplayYoungTableau@right}, Spacer[12]]

DisplayPath[T_] := DisplayYoungTableaux@PathToYoungTableaux@T


(* ::Section:: *)
(*Unitary group: Gelfand-Tsetlin patterns and Bratteli diagram*)


(* Descending ranges already put the tuples in reverse lexicographic order. *)
InterlacingCandidates[\[Lambda]_] := Tuples@Table[Range[\[Lambda][[i]], \[Lambda][[i + 1]], -1], {i, Length@\[Lambda] - 1}]

OrderGL[\[Mu]_, \[Lambda]_] := Length@\[Lambda] == Length@\[Mu] + 1 &&
	AllTrue[Most@\[Lambda] - \[Mu], NonNegative] && AllTrue[\[Mu] - Rest@\[Lambda], NonNegative]

(* All rows interlacing some row of the given level *)
levelBelow[level_] := Reverse@Union@Catenate[InterlacingCandidates /@ level]

BratteliLevelsGL[n_, m_, d_] := BratteliLevelsGL[n, m, d] = Reverse@NestList[levelBelow, Irreps[n, m, d], d]

BratteliDiagramGL[n_, m_, d_] := BratteliDiagramGL[n, m, d] = With[{vertices = Catenate@BratteliLevelsGL[n, m, d]},
	RelationGraph[OrderGL, vertices,
		VertexSize -> 0.2,
		VertexStyle -> Automatic,
		VertexLabels -> tooltipLabels[vertices, Identity],
		GraphLayout -> "LayeredDigraphEmbedding",
		ImagePadding -> 24,
		ImageSize -> 540
	]
]

AllGTPatterns[n_, m_, d_] := AllGTPatterns[n, m, d] = With[{graph = BratteliDiagramGL[n, m, d]},
	Table[Rest /@ allPathsOfLength[graph, {}, \[Lambda], d], {\[Lambda], Irreps[n, m, d]}]
]

IrrepDimsGL[n_, m_, d_] := IrrepDimsGL[n, m, d] = WeylDim /@ Irreps[n, m, d]

(* A GT pattern of \[Lambda] is a GT pattern of an interlacing row \[Mu] with \[Lambda] appended as the last row *)
gtPatterns[{}] = {{}};
gtPatterns[\[Lambda]_] := gtPatterns[\[Lambda]] = Catenate@Table[
	Append[pattern, \[Lambda]],
	{\[Mu], InterlacingCandidates@\[Lambda]}, {pattern, gtPatterns@\[Mu]}
]

GTPatterns[\[Lambda]_] := GTPatterns[\[Lambda]] = Reverse@Sort@gtPatterns@\[Lambda]

WeylDim[\[Lambda]_] := Product[
	(\[Lambda][[i]] - \[Lambda][[j]] + j - i) / (j - i),
	{i, Length@\[Lambda] - 1}, {j, i + 1, Length@\[Lambda]}
]

WeylDim[\[Lambda]_, d_] := With[{rows = DeleteCases[\[Lambda], 0]},
	Product[(d + j - i) / (rows[[i]] - j + TransposePartition[rows][[j]] - i + 1), {i, Length@rows}, {j, rows[[i]]}]
]

AssociationGTPatterns[\[Lambda]_] := AssociationGTPatterns[\[Lambda]] = indexAssociation@GTPatterns@\[Lambda]


(* ::Section:: *)
(*Clebsch-Gordan coefficients*)


(* ::Text:: *)
(*A Clebsch-Gordan coefficient of U(d) factorizes into reduced Wigner coefficients, one for each pair of consecutive*)
(*rows (k, k + 1) of the three GT patterns involved: P of \[Mu], w of the basis vector, and Q of \[Lambda] = \[Mu] \[PlusMinus] one cell.*)
(*In the formulas below a and b are the rows k and k + 1 of P shifted by their indices, a_i = P_(k,i) - i.*)


(* GT pattern of the basis vector e_x of C^d (x > 0), or of the basis vector e_(-x) of the dual space (x < 0):
   every row k >= Abs[x] has a single entry 1 at its front, respectively -1 at its back *)
weightVectorPattern[x_, d_] := Table[
	If[x > 0, Boole[k >= x && j == 1], -Boole[k >= -x && j == k]],
	{k, d}, {j, k}
]

RWcoef[{p1_, p2_}, {w1_, w2_}, {q1_, q2_}] := RWcoef[{p1, p2}, {w1, w2}, {q1, q2}] = Module[
	{s = Total@w2, a = p1 - Range@Length@p1, b = p2 - Range@Length@p2, i, j},

	(* the cell is added (s = 1) or removed (s = -1) at position i of the lower row and position j of the upper row *)
	i = stepPosition[p2, q2, s];
	j = stepPosition[p1, q1, s];
	Which[
		i === None, 0,

		(* only the lower row changes *)
		AllTrue[w1, # == 0 &], Which[
			p1 =!= q1, 0,
			s == 1, Sqrt[Times @@ (a - b[[i]] - 1) / productExcept[b - b[[i]], i]],
			True, Sqrt[Times @@ (a - b[[i]]) / productExcept[b - b[[i]], i]]
		],

		(* both rows change *)
		j === None, 0,
		s == 1, If[i <= j, 1, -1] Sqrt[
			productExcept[a - b[[i]] - 1, j] productExcept[b - a[[j]], i] /
			(productExcept[b - b[[i]], i] productExcept[a - a[[j]] - 1, j])
		],
		True, If[i <= j, 1, -1] Sqrt[
			productExcept[a - b[[i]], j] productExcept[b - a[[j]] + 1, i] /
			(productExcept[b - b[[i]], i] productExcept[a - a[[j]] + 1, j])
		]
	]
]

(* The rows above row Abs[x] are untouched by e_x, so they must coincide in P and Q *)
CGcoef[P_, x_, Q_] := CGcoef[P, x, Q] = With[{d = Length@P, k = Abs@x, w = weightVectorPattern[x, Length@P]},
	If[k < 1 || k > d || Length@Q =!= d ||
		stepPosition[Last@P, Last@Q, Sign@x] === None || Take[P, k - 1] =!= Take[Q, k - 1],
		0,
		Product[RWcoef[P[[i ;; i + 1]], w[[i ;; i + 1]], Q[[i ;; i + 1]]], {i, Max[k - 1, 1], d - 1}]
	]
]

(* Build Q row by row from the bottom row \[Lambda] upwards. Rows of length < x equal those of P, while every row of length >= x
   differs from that of P in a single entry, at any position, by s = Total[\[Lambda] - Last@P] = \[PlusMinus]1 *)
GTcandidates[\[Lambda]_, P_, x_] := GTcandidates[\[Lambda], P, x] = Module[{s = Total[\[Lambda] - Last@P], compatibleQ, extend},
	compatibleQ[row_] := With[{k = Length@row},
		If[k >= x, stepPosition[P[[k]], row, s] =!= None, row === P[[k]]]
	];
	extend[pattern_] := Prepend[pattern, #] & /@ Select[InterlacingCandidates@First@pattern, compatibleQ];
	Nest[Catenate[extend /@ #] &, {{\[Lambda]}}, Length@\[Lambda] - 1]
]

CG[\[Mu]_List, \[Lambda]_List] := Which[
	Length@\[Mu] != Length@\[Lambda], Message[CG::length, \[Mu], \[Lambda]]; $Failed,
	stepPosition[\[Mu], \[Lambda], 1] === None && stepPosition[\[Mu], \[Lambda], -1] === None, Message[CG::step, \[Mu], \[Lambda]]; $Failed,
	True, CG[\[Mu], \[Lambda]] = cgTensor[\[Mu], \[Lambda]]
]

CG[\[Mu]_, \[Lambda]_, d_] := CG[PadRight[\[Mu], d], PadRight[\[Lambda], d]]

cgTensor[\[Mu]_, \[Lambda]_] := With[{d = Length@\[Mu], s = Total[\[Lambda] - \[Mu]]},
	SparseArray[
		Flatten@Table[
			{x, AssociationGTPatterns[\[Mu]][P], AssociationGTPatterns[\[Lambda]][Q]} -> CGcoef[P, s x, Q],
			{P, GTPatterns@\[Mu]}, {x, d}, {Q, GTcandidates[\[Lambda], P, x]}
		],
		{d, WeylDim@\[Mu], WeylDim@\[Lambda]}
	]
]


(* ::Section:: *)
(*Mixed Schur transform*)


Weight[x_, n_, m_, d_] := Table[Count[x[[;; n]], letter] - Count[x[[n + 1 ;; n + m]], letter], {letter, d}]
Weight[x_, i_, n_, m_, d_] := Weight[PadRight[x[[;; i]], n + m], n, m, d]
Weight[x_, {n_, m_, d_}] := Weight[x, n, m, d]

SchurBasis[n_, m_, d_] := SchurBasis[n, m, d] = Catenate@MapThread[
	Tuples[{#1, #2}] &,
	{AllPathsWBA[n, m, d], GTPatterns /@ Irreps[n, m, d]}
]

(* The Schur basis is ordered by irrep l, then by path i, then by GT pattern j *)
SchurIndex[{T_, P_}, n_, m_, d_] := Module[
	{\[Lambda] = pathIrrep[T, d], dimsWBA = IrrepDimsWBA[n, m, d], dimsGL = IrrepDimsGL[n, m, d], l, i, j},
	l = AssociationIrrepsWBA[n, m, d][\[Lambda]];
	i = AssociationPathsToIrrepWBA[\[Lambda], n, m, d][T];
	j = AssociationGTPatterns[\[Lambda]][P];
	Take[dimsWBA, l - 1] . Take[dimsGL, l - 1] + dimsGL[[l]] (i - 1) + j
]

StandardBasis[n_, d_] := StandardBasis[n, d] = Tuples[Range@d, n]

(* Step k of the path couples the letter x_k to the irrep T_(k-1); the first factor is a 1 x dim(T_1) matrix *)
CGmatProduct[{}, {}] = {1};
CGmatProduct[x_List, T_List] := CGmatProduct[x, T] = With[{path = withRoot@T},
	First[Dot @@ Table[CG[path[[k]], path[[k + 1]]][[x[[k]]]], {k, Length@T}]]
]

SchurCoef[{}, {{}, P_List}] := Boole[AllTrue[Flatten@P, # === 0 &]]
SchurCoef[x_List, {T_List, P_List}] := SchurCoef[x, {T, P}] = CGmatProduct[x, T][[AssociationGTPatterns[Last@T][P]]]

(* Schur transform whose column for the string x is filled using the Schur basis vectors basisFor[x] *)
schurTransform[n_, m_, d_, basisFor_] := With[{dim = d^(n + m)},
	SparseArray[
		Flatten@Table[
			With[{x = If[d == 1, ConstantArray[1, n + m], IntegerDigits[column - 1, d, n + m] + 1]},
				Table[{SchurIndex[y, n, m, d], column} -> SchurCoef[x, y], {y, basisFor@x}]
			],
			{column, dim}
		],
		{dim, dim}
	]
]

SchurTransformSlow[n_, m_, d_] := SchurTransformSlow[n, m, d] = schurTransform[n, m, d, SchurBasis[n, m, d] &]


(* ::Subsection:: *)
(*Sparse block assembly of the Schur transform*)


(* Rows are {previous GT pattern, letter}, columns are new GT patterns; the letter varies fastest. *)
cgBranchMatrix[\[Mu]_, \[Lambda]_] := Flatten[Transpose[CG[\[Mu], \[Lambda]], {2, 1, 3}], 1]

(* Combine exact radical expressions once per distinct value, then remove canceled entries from sparse storage. *)
simplifySparseValues[matrix_] := Module[{values = matrix["NonzeroValues"], unique, replacements},
	unique = DeleteDuplicates@values;
	replacements = AssociationThread[unique -> (Together /@ unique)];
	SparseArray[Thread[matrix["NonzeroPositions"] -> Lookup[replacements, values]],
		Dimensions@matrix, Together[matrix["ImplicitValue"]]]
]

(* Each block has standard-basis rows and GT-pattern columns. Share path prefixes during this call only,
   then release the intermediate matrices; the package retains the compact CG tensors and final results. *)
schurVectorBlocks[paths_, d_] := Module[{build, blocks},
	build[{}] = Id[1];
	build[T_List] := build[T] = With[{prefix = Most@T},
		KroneckerProduct[build[prefix], Id[d]] . cgBranchMatrix[pathIrrep[prefix, d], Last@T]
	];
	blocks = build /@ paths;
	Clear[build];
	blocks
]

(* Stacking transposed path blocks keeps the original irrep, path, GT-pattern row order. *)
SchurTransform[n_, m_, d_] := SchurTransform[n, m, d] =
	simplifySparseValues[Join @@ (Transpose /@ schurVectorBlocks[Catenate@AllPathsWBA[n, m, d], d])]


(* ::Subsection:: *)
(*Bratteli diagram and basis restricted to a string*)


(* ::Text:: *)
(*The coefficient <T, P|x> vanishes unless, for every i, the irrep T_i of U(d) contains the weight of the first i letters*)
(*of x, and P has the weight of x. Restricting the Bratteli diagram accordingly leaves far fewer basis vectors to check.*)


gtWeight[P_] := Differences@Prepend[Total /@ P, 0]

(* Group once per irrep, preserving the original order within every weight. *)
gtPatternsByWeight[\[Lambda]_] := gtPatternsByWeight[\[Lambda]] = GroupBy[GTPatterns@\[Lambda], gtWeight]

GTPatternsWeight[\[Lambda]_, weight_] := Lookup[gtPatternsByWeight[\[Lambda]], Key[weight], {}]

BratteliLevelsWBAString[x_, n_, m_, d_] := BratteliLevelsWBAString[x, n, m, d] = With[{levels = BratteliLevelsWBA[n, m, d]},
	Prepend[
		Table[
			With[{weight = Weight[x, i, n, m, d]}, Select[levels[[i + 1]], GTPatternsWeight[First@#, weight] =!= {} &]],
			{i, n + m}
		],
		First@levels
	]
]

BratteliDiagramWBAString[x_, n_, m_, d_] := BratteliDiagramWBAString[x, n, m, d] =
	BratteliDiagramWBA@BratteliLevelsWBAString[x, n, m, d]

AllPathsWBAString[x_, n_, m_, d_] := DeleteCases[
	wbaPathGroups[wbaPathData@BratteliLevelsWBAString[x, n, m, d]], {}
]

SchurBasisGivenString[x_, n_, m_, d_] := With[{weight = Weight[x, n, m, d]},
	Catenate[Tuples[{#, GTPatternsWeight[pathIrrep[First@#, d], weight]}] & /@ AllPathsWBAString[x, n, m, d]]
]

(* ::Subsection:: *)
(*Matrix units*)


MatrixUnit[T_, S_] := If[If[T === {} || S === {}, T =!= S, Last@T =!= Last@S],
	Message[MatrixUnit::irrep, T, S]; $Failed,
	With[{blocks = schurVectorBlocks[{T, S}, If[T === {}, 1, Length@Last@T]]},
		blocks[[1]] . Transpose[blocks[[2]]]
	]
]


(* ::Section:: *)
(*Gelfand-Tsetlin basis of the partially transposed permutations*)


(* The walled content d - k + c of a right cell {k, c} is measured from the wall, so that it does not depend on the
   length of the staircases *)
WalledContent[T_, i_, d_ : Automatic] := With[{path = withRoot@T},
	If[MissingQ@FirstPosition[Abs[path[[i + 1]] - path[[i]]], 1],
		1,
		Replace[stepCell[path[[i]], path[[i + 1]]], {
			{"add", cell_} :> CellContent@cell,
			{"remove", cell_} :> -CellContent@cell,
			{"right", {k_, c_}} :> Replace[d, Automatic -> Length@Last@T] - k + c
		}]
	]
]

AxialDistance[T_, i_, d_ : Automatic] := WalledContent[T, i + 1, d] - WalledContent[T, i, d]

(* The path T with steps i and i + 1 performed in the opposite order *)
swapSteps[T_, i_] := ReplacePart[T, i -> withRoot[T][[i]] + T[[i + 1]] - T[[i]]]

(* The cell {row, column} that is added going from the staircase \[Mu] to the staircase \[Nu] *)
addedCell[\[Mu]_, \[Nu]_] := With[{row = First@FirstPosition[\[Nu] - \[Mu], 1]}, {row, \[Nu][[row]]}]

(* The matrix entry {index[T], index[S]} -> value, or Nothing with a message if S is not a basis path *)
matrixEntry[index_, T_, S_, value_] := If[KeyExistsQ[index, S],
	{index@T, index@S} -> value,
	Message[GeneratorsGT::path, S]; Nothing
]

(* Matrix of an operator in the basis of the given paths of one irrep. The function entries[T, index] gives the
   non-zero entries {index[T], index[S]} -> value of the row of the basis path T. *)
irrepMatrix[paths_, entries_] := With[{index = indexAssociation@paths, dim = Length@paths},
	SparseArray[Catenate[entries[#, index] & /@ paths], {dim, dim}]
]

(* Young's orthogonal form: \[Sigma]_i T = T / r + Sqrt[1 - 1 / r^2] swapSteps[T, i], with r the axial distance *)
transpositionEntries[T_, index_, i_, d_] := With[{r = AxialDistance[T, i, d]},
	If[Abs@r == 1,
		{{index@T, index@T} -> r},
		{{index@T, index@T} -> 1 / r, matrixEntry[index, T, swapSteps[T, i], Sqrt[1 - 1 / r^2]]}
	]
]

(* Non-zero only if the path adds a cell b to \[Mu] = T_(n-1) at step n and removes it again at step n + 1. It then maps
   to the paths through \[Mu] + a for all addable cells a, with coefficient Sqrt[weight[\[Mu], a] weight[\[Mu], b]]; cells
   of zero weight or beyond the length of the staircases are skipped. *)
contractionEntries[T_, index_, n_, weight_] := Module[{\[Mu] = withRoot[T][[n]], partition, wb},
	If[\[Mu] =!= T[[n + 1]],
		{},
		partition = First@ToPair@\[Mu];
		wb = weight[partition, addedCell[\[Mu], T[[n]]]];
		Table[
			With[{wa = weight[partition, a]},
				If[wa == 0 || First@a > Length@\[Mu],
					Nothing,
					matrixEntry[index, T, ReplacePart[T, n -> AddCell[\[Mu], First@a]], Sqrt[wa wb]]
				]
			],
			{a, AddableCellPositions@partition}
		]
	]
]

(* The paths of every irrep in Irreps[n, m, d], unless other paths are given. The pattern {__List} for them keeps a
   list of options from being taken for paths. *)
basisPaths[n_, m_, d_, paths_] := Replace[paths, Automatic :> AllPathsWBA[n, m, d]]

TranspositionGT[i_, n_, m_, d_, paths : ({__List} | Automatic) : Automatic] := If[i == n,
	Message[TranspositionGT::contraction, i]; $Failed,
	irrepMatrix[#, transpositionEntries[#1, #2, i, d] &] & /@ basisPaths[n, m, d, paths]
]

Options[ContractionGT] = {"Weight" -> Automatic};

ContractionGT[n_, m_, d_, paths : ({__List} | Automatic) : Automatic, OptionsPattern[]] := If[n < 1 || m < 1,
	Message[ContractionGT::none, n, m]; $Failed,
	With[{weight = Replace[OptionValue["Weight"], Automatic -> ((d + CellContent[#2]) TransitionWeight[#1, #2] &)]},
		irrepMatrix[#, contractionEntries[#1, #2, n, weight] &] & /@ basisPaths[n, m, d, paths]
	]
]

GeneratorsGT[n_, m_, d_, paths : ({__List} | Automatic) : Automatic] := With[{basis = basisPaths[n, m, d, paths]},
	Table[If[i == n, ContractionGT[n, m, d, basis], TranspositionGT[i, n, m, d, basis]], {i, n + m - 1}]
]


(* ::Subsection:: *)
(*Relations of the walled Brauer algebra*)


CheckRelationsWBA[\[Sigma]_List, n_, m_, d_] := Module[
	{k = Length@\[Sigma], transpositions, distant},
	transpositions = DeleteCases[Range@k, n];
	distant = Complement[Range@k, {n - 1, n, n + 1}];
	<|
		"\[Sigma]_i^2 = 1" -> Table[\[Sigma][[i]] . \[Sigma][[i]] == IdentityMatrix@Length@\[Sigma][[i]], {i, transpositions}],
		"\[Sigma]_i \[Sigma]_(i+1) \[Sigma]_i = \[Sigma]_(i+1) \[Sigma]_i \[Sigma]_(i+1)" -> Table[
			\[Sigma][[i]] . \[Sigma][[i + 1]] . \[Sigma][[i]] == \[Sigma][[i + 1]] . \[Sigma][[i]] . \[Sigma][[i + 1]],
			{i, Select[Range[k - 1], # <= n - 2 || # >= n + 1 &]}
		],
		"\[Sigma]_i \[Sigma]_j = \[Sigma]_j \[Sigma]_i for |i - j| > 1" -> Flatten@Table[
			If[Abs[i - j] > 1, \[Sigma][[j]] . \[Sigma][[i]] == \[Sigma][[i]] . \[Sigma][[j]], Nothing],
			{i, transpositions}, {j, transpositions}
		],
		"\[Sigma]_n^2 = d \[Sigma]_n" -> If[1 <= n <= k, {\[Sigma][[n]] . \[Sigma][[n]] == d \[Sigma][[n]]}, {}],
		"\[Sigma]_n \[Sigma]_(n\[PlusMinus]1) \[Sigma]_n = \[Sigma]_n" -> {
			If[2 <= n <= k, \[Sigma][[n]] . \[Sigma][[n - 1]] . \[Sigma][[n]] == \[Sigma][[n]], Nothing],
			If[m >= 2 && n >= 1, \[Sigma][[n]] . \[Sigma][[n + 1]] . \[Sigma][[n]] == \[Sigma][[n]], Nothing]
		},
		"\[Sigma]_n \[Sigma]_i = \[Sigma]_i \[Sigma]_n for |i - n| > 1" ->
			If[1 <= n <= k, Table[\[Sigma][[n]] . \[Sigma][[i]] == \[Sigma][[i]] . \[Sigma][[n]], {i, distant}], {}],
		"\[Sigma]_n \[Sigma]_(n+1) \[Sigma]_(n-1) \[Sigma]_n (\[Sigma]_(n-1) - \[Sigma]_(n+1)) = 0 = (\[Sigma]_(n-1) - \[Sigma]_(n+1)) \[Sigma]_n \[Sigma]_(n+1) \[Sigma]_(n-1) \[Sigma]_n" -> If[Min[n, m] >= 2,
			{
				\[Sigma][[n]] . \[Sigma][[n + 1]] . \[Sigma][[n - 1]] . \[Sigma][[n]] . \[Sigma][[n - 1]] ==
					\[Sigma][[n]] . \[Sigma][[n + 1]] . \[Sigma][[n - 1]] . \[Sigma][[n]] . \[Sigma][[n + 1]],
				\[Sigma][[n - 1]] . \[Sigma][[n]] . \[Sigma][[n + 1]] . \[Sigma][[n - 1]] . \[Sigma][[n]] ==
					\[Sigma][[n + 1]] . \[Sigma][[n]] . \[Sigma][[n + 1]] . \[Sigma][[n - 1]] . \[Sigma][[n]]
			},
			{}
		]
	|>
]


(* ::Section:: *)
(*Deprecated names*)


InterlacingCanditates = InterlacingCandidates;
transpostionGT = TranspositionGT;
contractionGT = ContractionGT;
generatorsGT = GeneratorsGT;


End[];
EndPackage[];
