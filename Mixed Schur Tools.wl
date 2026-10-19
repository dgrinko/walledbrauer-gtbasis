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
DisplayStaircase::usage = "DisplayStaircase[\[Lambda]] draws the staircase \[Lambda] as two Young diagrams separated by a thick wall: positive rows to the right of the wall, negative rows to the left.";
Id::usage = "Id[n] gives the n\[Times]n identity matrix as a SparseArray.";
Enumerate::usage = "Enumerate[list] pairs every element of list with its position: {{e1, 1}, {e2, 2}, ...}.";


(* ::Subsection:: *)
(*Walled Brauer algebra*)


BratteliLevelsWBA::usage = "BratteliLevelsWBA[n, m, d] gives the vertices {\[Lambda], level} of the Bratteli diagram of the walled Brauer algebra acting on (C^d)^n \[CircleTimes] (C^d*)^m, grouped by level 0, ..., n + m.";
OrderWBA::usage = "OrderWBA[u, v] is True if the walled Brauer Bratteli diagram has an edge from vertex u to vertex v: v is one level higher and its staircase differs from that of u in a single entry.";
BratteliDiagramWBA::usage = "BratteliDiagramWBA[n, m, d] gives the walled Brauer Bratteli diagram as a Graph. Hover over a vertex to see its staircase.";
BratteliDiagramWBALabelled::usage = "BratteliDiagramWBALabelled[n, m, d] draws the walled Brauer Bratteli diagram with every vertex labelled by its staircase.";
Irreps::usage = "Irreps[n, m, d] lists the staircases of the irreps appearing in the mixed Schur-Weyl duality on (C^d)^n \[CircleTimes] (C^d*)^m.";
PathsToIrrepWBA::usage = "PathsToIrrepWBA[\[Lambda], n, m, d] lists the paths of n + m staircases from the root of the Bratteli diagram to the irrep \[Lambda]. They label the Gelfand-Tsetlin basis of the walled Brauer irrep \[Lambda].";
IrrepDimWBA::usage = "IrrepDimWBA[\[Lambda], n, m, d] gives the dimension of the walled Brauer irrep \[Lambda].";
AllPathsWBA::usage = "AllPathsWBA[n, m, d] gives PathsToIrrepWBA for every irrep in Irreps[n, m, d].";
IrrepDimsWBA::usage = "IrrepDimsWBA[n, m, d] gives the dimensions of the walled Brauer irreps, in the order of Irreps[n, m, d].";
AssociationIrrepsWBA::usage = "AssociationIrrepsWBA[n, m, d] maps every irrep to its position in Irreps[n, m, d].";
AssociationPathsToIrrepWBA::usage = "AssociationPathsToIrrepWBA[\[Lambda], n, m, d] maps every path to \[Lambda] to its position in PathsToIrrepWBA[\[Lambda], n, m, d].";


(* ::Subsection:: *)
(*Unitary group*)


InterlacingCandidates::usage = "InterlacingCandidates[\[Lambda]] lists all rows \[Mu] of length Length[\[Lambda]] - 1 that interlace \[Lambda], i.e. \[Lambda][[i]] >= \[Mu][[i]] >= \[Lambda][[i + 1]], in reverse lexicographic order.";
OrderGL::usage = "OrderGL[\[Mu], \[Lambda]] is True if \[Mu] is one entry shorter than \[Lambda] and interlaces it.";
BratteliLevelsGL::usage = "BratteliLevelsGL[n, m, d] gives the levels of the Bratteli diagram of the chain U(0) \[Subset] U(1) \[Subset] ... \[Subset] U(d) that lead to the irreps Irreps[n, m, d].";
BratteliDiagramGL::usage = "BratteliDiagramGL[n, m, d] gives the Bratteli diagram with levels BratteliLevelsGL[n, m, d] as a Graph.";
AllGTPatterns::usage = "AllGTPatterns[n, m, d] lists, for every irrep in Irreps[n, m, d], its Gelfand-Tsetlin patterns, found as paths in BratteliDiagramGL[n, m, d].";
IrrepDimsGL::usage = "IrrepDimsGL[n, m, d] gives the dimensions of the U(d) irreps, in the order of Irreps[n, m, d].";
GTPatterns::usage = "GTPatterns[\[Lambda]] lists the Gelfand-Tsetlin patterns {P_1, ..., P_d} (row k of length k, P_d = \[Lambda]) of the U(d) irrep \[Lambda] in reverse lexicographic order. They label its Gelfand-Tsetlin basis.";
WeylDim::usage = "WeylDim[\[Lambda]] gives the dimension of the U(d) irrep \[Lambda], d = Length[\[Lambda]], by the Weyl dimension formula.";
AssociationGTPatterns::usage = "AssociationGTPatterns[\[Lambda]] maps every Gelfand-Tsetlin pattern of \[Lambda] to its position in GTPatterns[\[Lambda]].";


(* ::Subsection:: *)
(*Clebsch-Gordan coefficients*)


RWcoef::usage = "RWcoef[P, w, Q] gives the reduced Wigner coefficient for two consecutive rows P and Q of Gelfand-Tsetlin patterns, where w are the same two rows of the pattern of a basis vector of C^d or of its dual.";
CGcoef::usage = "CGcoef[P, x, Q] gives the Clebsch-Gordan coefficient <Q|(|P> \[CircleTimes] |x>) for Gelfand-Tsetlin patterns P and Q. Here |x> is the basis vector e_x of C^d if x > 0, and the basis vector e_(-x) of the dual space C^d* if x < 0.";
GTcandidates::usage = "GTcandidates[\[Lambda], P, x] lists the Gelfand-Tsetlin patterns Q of \[Lambda] for which CGcoef[P, \[PlusMinus]x, Q] can be non-zero.";
CG::usage = "CG[\[Mu], \[Lambda]] gives the Clebsch-Gordan tensor with entries C[[x, i, j]] = CGcoef[GTPatterns[\[Mu]][[i]], \[PlusMinus]x, GTPatterns[\[Lambda]][[j]]], for \[Mu] \[CircleTimes] C^d \[RightArrow] \[Lambda] if \[Lambda] has one more cell than \[Mu] (sign +), or \[Mu] \[CircleTimes] C^d* \[RightArrow] \[Lambda] if it has one cell less (sign -).\nCG[\[Mu], \[Lambda], d] first pads \[Mu] and \[Lambda] with zeros to length d.";


(* ::Subsection:: *)
(*Mixed Schur transform*)


Weight::usage = "Weight[x, n, m, d] gives the U(d) weight of the string x: how many times each letter 1, ..., d occurs among the first n letters, minus how many times it occurs among the last m letters.\nWeight[x, i, n, m, d] gives the weight of the first i letters of x.\nWeight[x, {n, m, d}] is Weight[x, n, m, d].";
SchurBasis::usage = "SchurBasis[n, m, d] lists the mixed Schur basis vectors {T, P}, where T is a path to an irrep and P a Gelfand-Tsetlin pattern of the same irrep. They are ordered by irrep (as in Irreps), then by path, then by pattern.";
SchurIndex::usage = "SchurIndex[{T, P}, n, m, d] gives the position of the Schur basis vector {T, P} in SchurBasis[n, m, d].";
StandardBasis::usage = "StandardBasis[k, d] lists the strings of length k over {1, ..., d} in lexicographic order.";
CGmatProduct::usage = "CGmatProduct[x, T] multiplies the Clebsch-Gordan tensors along the path T for the string x. Entry j of the result is the Schur transform coefficient <T, GTPatterns[Last[T]][[j]]|x>.";
SchurCoef::usage = "SchurCoef[x, {T, P}] gives the mixed Schur transform coefficient <T, P|x>.";
SchurTransformSlow::usage = "SchurTransformSlow[n, m, d] gives the d^(n+m)\[Times]d^(n+m) mixed Schur transform, computing every entry. Row i corresponds to SchurBasis[n, m, d][[i]], column j to StandardBasis[n + m, d][[j]].";
SchurTransform::usage = "SchurTransform[n, m, d] gives the same matrix as SchurTransformSlow[n, m, d], but computes only the entries that can be non-zero.";

GTPatternsWeight::usage = "GTPatternsWeight[\[Lambda], w] lists the Gelfand-Tsetlin patterns of \[Lambda] with weight w.";
BratteliLevelsWBAString::usage = "BratteliLevelsWBAString[x, n, m, d] keeps only those vertices of BratteliLevelsWBA[n, m, d] whose U(d) irrep contains the weight of the prefix of the string x of the same length.";
BratteliDiagramWBAString::usage = "BratteliDiagramWBAString[x, n, m, d] gives the Bratteli diagram with levels BratteliLevelsWBAString[x, n, m, d] as a Graph.";
AllPathsWBAString::usage = "AllPathsWBAString[x, n, m, d] lists, grouped by irrep, the paths in BratteliDiagramWBAString[x, n, m, d]: the only paths T for which <T, P|x> can be non-zero.";
SchurBasisGivenString::usage = "SchurBasisGivenString[x, n, m, d] lists the Schur basis vectors {T, P} for which <T, P|x> can be non-zero.";


(* ::Subsection:: *)
(*Gelfand-Tsetlin basis of the partially transposed permutations*)


WalledContent::usage = "WalledContent[T, i] gives the signed content of the cell added (+) or removed (-) at step i of the path T: s (\[Lambda]_r - r), where r is the row that changes, s = \[PlusMinus]1, and \[Lambda] is the staircase after adding, or before removing, the cell.";
AxialDistance::usage = "AxialDistance[T, i] gives WalledContent[T, i + 1] - WalledContent[T, i], which determines how the transposition (i, i + 1) acts on the Gelfand-Tsetlin basis vector T.";
TranspositionGT::usage = "TranspositionGT[i, n, m, d] gives, for every irrep in Irreps[n, m, d], the matrix of the transposition (i, i + 1), i != n, in the Gelfand-Tsetlin basis PathsToIrrepWBA.";
ContractionGT::usage = "ContractionGT[n, m, d] gives, for every irrep in Irreps[n, m, d], the matrix of the contraction generator (partial transpose of the swap of tensor factors n and n + 1) in the Gelfand-Tsetlin basis PathsToIrrepWBA.";
GeneratorsGT::usage = "GeneratorsGT[n, m, d] gives the Gelfand-Tsetlin basis matrices of all generators \[Sigma]_1, ..., \[Sigma]_(n+m-1): TranspositionGT for i != n and ContractionGT for i = n.";


(* ::Subsection:: *)
(*Deprecated names*)


InterlacingCanditates::usage = "InterlacingCanditates is a deprecated name of InterlacingCandidates.";
transpostionGT::usage = "transpostionGT is a deprecated name of TranspositionGT.";
contractionGT::usage = "contractionGT is a deprecated name of ContractionGT.";
generatorsGT::usage = "generatorsGT is a deprecated name of GeneratorsGT.";


ToStaircase::height = "The partitions `1` and `2` have more than `3` rows in total.";
CG::length = "The staircases `1` and `2` have different lengths.";
CG::step = "The staircase `2` is not obtained from `1` by adding or removing a single cell.";
TranspositionGT::contraction = "The generator `1` = n is the contraction, not a transposition. Use ContractionGT instead.";
ContractionGT::none = "There is no contraction generator for n = `1`, m = `2`: both must be positive.";


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

(* Staircases along a path of Bratteli diagram vertices {staircase, level}, without the root *)
pathStaircases[vertices_] := Rest[vertices][[All, 1]]

(* Vertex labels showing the staircase of every vertex as a tooltip *)
tooltipLabels[vertices_, staircaseOf_] := Table[v -> Placed[DisplayStaircase@staircaseOf@v, Tooltip], {v, vertices}]


(* ::Section:: *)
(*Staircases and Young diagrams*)


ToStaircase[{left_, right_, d_}] := If[Length@left + Length@right > d,
	Message[ToStaircase::height, left, right, d]; $Failed,
	PadRight[left, d] - PadLeft[Reverse@right, d]
]

ToPair[\[Lambda]_] := {Select[\[Lambda], # > 0 &], -Reverse@Select[\[Lambda], # < 0 &], Length@\[Lambda]}

TransposePartition[\[Lambda]_] := Table[Count[\[Lambda], row_ /; row >= i], {i, First@\[Lambda]}]

AddCell[\[Lambda]_, i_] := \[Lambda] + UnitVector[Length@\[Lambda], i]

AddableCells[\[Lambda]_] := Prepend[Select[Range[2, Length@\[Lambda]], \[Lambda][[# - 1]] > \[Lambda][[#]] &], 1]

Id[dim_] := SparseArray[{Band[{1, 1}] -> 1}, {dim, dim}]

Enumerate[list_List] := MapIndexed[{#1, First@#2} &, list]

(* Row i holds Abs[\[Lambda][[i]]] framed cells: to the right of the wall if \[Lambda][[i]] > 0, to its left if \[Lambda][[i]] < 0 *)
DisplayStaircase[\[Lambda]_] := If[AllTrue[\[Lambda], # == 0 &],
	"\[EmptySet]",
	With[{wall = Max[0, -Min@\[Lambda]]},
		Grid[
			Table[ConstantArray[" ", Abs[row] + wall], {row, \[Lambda]}],
			Dividers -> {{wall + 1 -> {Thick}}},
			Frame -> {None, None, Flatten@Table[
				{i, j + wall} -> True,
				{i, Length@\[Lambda]}, {j, Min[\[Lambda][[i]], 0] + 1, Max[\[Lambda][[i]], 0]}
			]}
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

BratteliDiagramWBA[n_, m_, d_] := BratteliDiagramWBA[n, m, d] = With[{vertices = Catenate@BratteliLevelsWBA[n, m, d]},
	RelationGraph[OrderWBA, vertices,
		VertexSize -> 0.2,
		VertexStyle -> LightBlue,
		VertexLabels -> tooltipLabels[vertices, First],
		GraphLayout -> "LayeredDigraphEmbedding",
		ImageSize -> Small
	]
]

BratteliDiagramWBALabelled[n_, m_, d_] := With[{vertices = Catenate@BratteliLevelsWBA[n, m, d]},
	RelationGraph[OrderWBA, vertices,
		VertexSize -> 0.4,
		VertexShape -> Graphics[{Transparent, Disk[]}],
		VertexStyle -> LightBlue,
		VertexLabels -> Table[v -> Placed[DisplayStaircase@First@v, Center], {v, vertices}],
		GraphLayout -> "LayeredDigraphEmbedding"
	]
]

PathsToIrrepWBA[\[Lambda]_, n_, m_, d_] := PathsToIrrepWBA[\[Lambda], n, m, d] = pathStaircases /@ FindPath[
	BratteliDiagramWBA[n, m, d], {zeroStaircase[d], 0}, {\[Lambda], n + m}, {n + m}, All
]

IrrepDimWBA[\[Lambda]_, n_, m_, d_] := IrrepDimWBA[\[Lambda], n, m, d] = Length@PathsToIrrepWBA[\[Lambda], n, m, d]

AllPathsWBA[n_, m_, d_] := AllPathsWBA[n, m, d] = PathsToIrrepWBA[#, n, m, d] & /@ Irreps[n, m, d]

IrrepDimsWBA[n_, m_, d_] := IrrepDimsWBA[n, m, d] = Length /@ AllPathsWBA[n, m, d]

AssociationIrrepsWBA[n_, m_, d_] := AssociationIrrepsWBA[n, m, d] = indexAssociation@Irreps[n, m, d]

AssociationPathsToIrrepWBA[\[Lambda]_, n_, m_, d_] := AssociationPathsToIrrepWBA[\[Lambda], n, m, d] =
	indexAssociation@PathsToIrrepWBA[\[Lambda], n, m, d]


(* ::Section:: *)
(*Unitary group: Gelfand-Tsetlin patterns and Bratteli diagram*)


InterlacingCandidates[\[Lambda]_] := Reverse@Sort@Tuples@Table[Range[\[Lambda][[i]], \[Lambda][[i + 1]], -1], {i, Length@\[Lambda] - 1}]

OrderGL[\[Mu]_, \[Lambda]_] := Length@\[Lambda] == Length@\[Mu] + 1 &&
	AllTrue[Most@\[Lambda] - \[Mu], NonNegative] && AllTrue[\[Mu] - Rest@\[Lambda], NonNegative]

(* All rows interlacing some row of the given level *)
levelBelow[level_] := Reverse@Union@Catenate[InterlacingCandidates /@ level]

BratteliLevelsGL[n_, m_, d_] := BratteliLevelsGL[n, m, d] = Reverse@NestList[levelBelow, Irreps[n, m, d], d]

BratteliDiagramGL[n_, m_, d_] := BratteliDiagramGL[n, m, d] = With[{vertices = Catenate@BratteliLevelsGL[n, m, d]},
	RelationGraph[OrderGL, vertices,
		VertexSize -> 0.2,
		VertexStyle -> LightRed,
		VertexLabels -> tooltipLabels[vertices, Identity],
		GraphLayout -> "LayeredDigraphEmbedding",
		ImageSize -> Small
	]
]

AllGTPatterns[n_, m_, d_] := AllGTPatterns[n, m, d] = With[{graph = BratteliDiagramGL[n, m, d]},
	Table[Rest /@ FindPath[graph, {}, \[Lambda], {d}, All], {\[Lambda], Irreps[n, m, d]}]
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
	If[Take[P, k - 1] =!= Take[Q, k - 1],
		0,
		Product[RWcoef[P[[i ;; i + 1]], w[[i ;; i + 1]], Q[[i ;; i + 1]]], {i, Max[k - 1, 1], d - 1}]
	]
]

(* Build Q row by row from the bottom row \[Lambda] upwards: rows of length < x equal those of P, while rows of length >= x
   differ from those of P by the same cell (s = \[PlusMinus]1) by which \[Lambda] differs from the last row of P *)
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
	{\[Lambda] = Last@T, dimsWBA = IrrepDimsWBA[n, m, d], dimsGL = IrrepDimsGL[n, m, d], l, i, j},
	l = AssociationIrrepsWBA[n, m, d][\[Lambda]];
	i = AssociationPathsToIrrepWBA[\[Lambda], n, m, d][T];
	j = AssociationGTPatterns[\[Lambda]][P];
	Take[dimsWBA, l - 1] . Take[dimsGL, l - 1] + dimsGL[[l]] (i - 1) + j
]

StandardBasis[n_, d_] := StandardBasis[n, d] = Tuples[Range@d, n]

(* Step k of the path couples the letter x_k to the irrep T_(k-1); the first factor is a 1 x dim(T_1) matrix *)
CGmatProduct[x_List, T_List] := CGmatProduct[x, T] = With[{path = withRoot@T},
	First[Dot @@ Table[CG[path[[k]], path[[k + 1]]][[x[[k]]]], {k, Length@T}]]
]

SchurCoef[x_List, {T_List, P_List}] := SchurCoef[x, {T, P}] = CGmatProduct[x, T][[AssociationGTPatterns[Last@T][P]]]

(* Schur transform whose column for the string x is filled using the Schur basis vectors basisFor[x] *)
schurTransform[n_, m_, d_, basisFor_] := With[{dim = d^(n + m)},
	SparseArray[
		Flatten@Table[
			With[{x = IntegerDigits[column - 1, d, n + m] + 1},
				Table[{SchurIndex[y, n, m, d], column} -> SchurCoef[x, y], {y, basisFor@x}]
			],
			{column, dim}
		],
		{dim, dim}
	]
]

SchurTransformSlow[n_, m_, d_] := SchurTransformSlow[n, m, d] = schurTransform[n, m, d, SchurBasis[n, m, d] &]


(* ::Subsection:: *)
(*Faster Schur transform: Bratteli diagram restricted to a string*)


(* ::Text:: *)
(*The coefficient <T, P|x> vanishes unless, for every i, the irrep T_i of U(d) contains the weight of the first i letters*)
(*of x, and P has the weight of x. Restricting the Bratteli diagram accordingly leaves far fewer basis vectors to check.*)


gtWeight[P_] := Differences@Prepend[Total /@ P, 0]

GTPatternsWeight[\[Lambda]_, weight_] := Select[GTPatterns@\[Lambda], gtWeight@# === weight &]

BratteliLevelsWBAString[x_, n_, m_, d_] := BratteliLevelsWBAString[x, n, m, d] = With[{levels = BratteliLevelsWBA[n, m, d]},
	Prepend[
		Table[
			With[{weight = Weight[x, i, n, m, d]}, Select[levels[[i + 1]], GTPatternsWeight[First@#, weight] =!= {} &]],
			{i, n + m}
		],
		First@levels
	]
]

BratteliDiagramWBAString[x_, n_, m_, d_] := BratteliDiagramWBAString[x, n, m, d] = With[
	{vertices = Catenate@BratteliLevelsWBAString[x, n, m, d]},
	RelationGraph[OrderWBA, vertices,
		GraphLayout -> "LayeredDigraphEmbedding",
		VertexLabels -> tooltipLabels[vertices, First]
	]
]

AllPathsWBAString[x_, n_, m_, d_] := With[{graph = BratteliDiagramWBAString[x, n, m, d]},
	DeleteCases[
		Table[
			pathStaircases /@ FindPath[graph, {zeroStaircase[d], 0}, irrep, {n + m}, All],
			{irrep, Last@BratteliLevelsWBAString[x, n, m, d]}
		],
		{}
	]
]

SchurBasisGivenString[x_, n_, m_, d_] := With[{weight = Weight[x, n, m, d]},
	Catenate[Tuples[{#, GTPatternsWeight[Last@First@#, weight]}] & /@ AllPathsWBAString[x, n, m, d]]
]

SchurTransform[n_, m_, d_] := SchurTransform[n, m, d] = schurTransform[n, m, d, SchurBasisGivenString[#, n, m, d] &]


(* ::Section:: *)
(*Gelfand-Tsetlin basis of the partially transposed permutations*)


WalledContent[T_, i_] := Module[{path = withRoot@T, step, s, row},
	step = path[[i + 1]] - path[[i]];
	s = Total@step;
	row = FirstPosition[Abs@step, 1];
	If[MissingQ@row, 1, s (path[[If[s > 0, i + 1, i], First@row]] - First@row)]
]

AxialDistance[T_, i_] := WalledContent[T, i + 1] - WalledContent[T, i]

(* The path T with steps i and i + 1 performed in the opposite order *)
swapSteps[T_, i_] := ReplacePart[T, i -> withRoot[T][[i]] + T[[i + 1]] - T[[i]]]

(* Matrix of an operator on the walled Brauer irrep \[Lambda] in the GT basis. The function entries[T, index] gives
   the non-zero entries {index[T], index[S]} -> value of the row of the basis path T. *)
irrepMatrix[\[Lambda]_, n_, m_, d_, entries_] := With[
	{index = AssociationPathsToIrrepWBA[\[Lambda], n, m, d], dim = IrrepDimWBA[\[Lambda], n, m, d]},
	SparseArray[Catenate[entries[#, index] & /@ PathsToIrrepWBA[\[Lambda], n, m, d]], {dim, dim}]
]

(* Young's orthogonal form: \[Sigma]_i T = T / r + Sqrt[1 - 1 / r^2] swapSteps[T, i], with r the axial distance *)
transpositionEntries[T_, index_, i_] := With[{r = AxialDistance[T, i]},
	If[Abs@r == 1,
		{{index@T, index@T} -> r},
		{{index@T, index@T} -> 1 / r, {index@T, index@swapSteps[T, i]} -> Sqrt[1 - 1 / r^2]}
	]
]

(* Non-zero only if the path returns to T_(n-1) at step n + 1; it then maps to all paths through T_(n-1) + one cell *)
contractionEntries[T_, index_, n_] := With[{\[Mu] = withRoot[T][[n]]},
	If[\[Mu] =!= T[[n + 1]],
		{},
		Table[
			{index@T, index@ReplacePart[T, n -> AddCell[\[Mu], row]]} ->
				Sqrt[WeylDim[T[[n]]] WeylDim[AddCell[\[Mu], row]]] / WeylDim[\[Mu]],
			{row, AddableCells@\[Mu]}
		]
	]
]

TranspositionGT[i_, n_, m_, d_] := If[i == n,
	Message[TranspositionGT::contraction, i]; $Failed,
	Table[irrepMatrix[\[Lambda], n, m, d, transpositionEntries[#1, #2, i] &], {\[Lambda], Irreps[n, m, d]}]
]

ContractionGT[n_, m_, d_] := If[n < 1 || m < 1,
	Message[ContractionGT::none, n, m]; $Failed,
	Table[irrepMatrix[\[Lambda], n, m, d, contractionEntries[#1, #2, n] &], {\[Lambda], Irreps[n, m, d]}]
]

GeneratorsGT[n_, m_, d_] := Table[If[i == n, ContractionGT[n, m, d], TranspositionGT[i, n, m, d]], {i, n + m - 1}]


(* ::Section:: *)
(*Deprecated names*)


InterlacingCanditates = InterlacingCandidates;
transpostionGT = TranspositionGT;
contractionGT = ContractionGT;
generatorsGT = GeneratorsGT;


End[];
EndPackage[];
