(* ::Package:: *)

(* ::Title:: *)
(*Gelfand-Tsetlin basis of the walled Brauer algebra (v1)*)


(* ::Text:: *)
(*Supporting code for arXiv:2310.02252v1. The walled Brauer algebra (algebra of partially transposed permutations)*)
(*acts on p copies of C^d and q copies of its dual. Its irreps are labelled by pairs {left, right} of partitions, and the*)
(*vertices of its Bratteli diagram are triples {left, right, level}. Gelfand-Tsetlin basis vectors are paths in the*)
(*Bratteli diagram or, equivalently, pairs of mixed Young tableaux.*)
(**)
(*All definitions live in the Global` context, so that the notebooks in this folder can use and extend them.*)


(* ::Section:: *)
(*Bratteli diagram, irreps and paths*)


(* Levels 0, ..., p hold the partitions {left, {}} of the level; level p + i holds the pairs {left, right} with
   left a partition of p - k, right a partition of i - k, k = 0, ..., Min[p, i], and at most d rows in total *)
BratteliLevels[p_, q_, d_] := BratteliLevels[p, q, d] = Join[
	Table[{left, {}, i}, {i, 0, p}, {left, IntegerPartitions[i, d]}],
	Table[
		Flatten[
			Table[
				{left, right, p + i},
				{k, 0, Min[p, i]}, {left, IntegerPartitions[p - k, d]}, {right, IntegerPartitions[i - k, d - Length@left]}
			],
			2
		],
		{i, 1, q}
	]
]

(* True if the Young diagram x contains the Young diagram y *)
Contains[x_, y_] := With[{rows = Max[Length@x, Length@y]},
	AllTrue[PadRight[x, rows] - PadRight[y, rows], NonNegative]
]

(* Edge from vertex x to vertex y: y is one level higher, and
   - in the left part of the diagram, y adds a cell to the left partition of x;
   - in the right part, y adds a cell to the right partition of x, or removes a cell from its left partition *)
OrderWBA[{left1_, right1_, level1_}, {left2_, right2_, level2_}] := Which[
	level2 != level1 + 1, False,
	Total@left1 == level1 && Total@left2 == level2, Contains[left2, left1],
	Total@left1 <= level1 && Total@left2 < level2, Which[
		Total@left2 == Total@left1, Contains[right2, right1] && Contains[left1, left2],
		Total@right2 == Total@right1, Contains[right1, right2] && Contains[left1, left2],
		True, False
	],
	True, False
]

BratteliDiagram[p_, q_, d_] := BratteliDiagram[p, q, d] =
	RelationGraph[OrderWBA, Flatten[BratteliLevels[p, q, d], 1], GraphLayout -> "LayeredDigraphEmbedding"]

(* Irreps {left, right} and, for every irrep, its paths from the root, each vertex given as {left, right} *)
Irreps[p_, q_, d_] := Irreps[p, q, d] = BratteliLevels[p, q, d][[-1, All, 1 ;; 2]]

AllPaths[p_, q_, d_] := AllPaths[p, q, d] = Table[
	#[[All, 1 ;; 2]] & /@ FindPath[BratteliDiagram[p, q, d], {{}, {}, 0}, Append[irrep, p + q], {p + q}, All],
	{irrep, Irreps[p, q, d]}
]

IrrepDims[p_, q_, d_] := IrrepDims[p, q, d] = Length /@ AllPaths[p, q, d]


(* ::Section:: *)
(*Young diagrams and mixed Young tableaux*)


DisplayYoungDiagram[YD_] := DisplayYoungDiagram[YD] = If[YD == {},
	ToString@\[EmptySet],
	Grid[
		Table[" ", {i, Length@YD}, {j, YD[[i]]}],
		Frame -> {None, None, Flatten[Table[{i, j} -> True, {i, Length@YD}, {j, YD[[i]]}], 1]}
	]
]

(* Left tableau of a path. L lists the left partitions along the path (root included, all padded to the same length)
   and L[[p]] is the left partition at the wall. Step i < p adds the cell labelled {i}; a later step i that removes
   a cell (a contraction) appends i to the label of that cell. *)
YoungTableauxFromYDPathLeft[L_, p_] := Module[{tableau, row},
	tableau = Table[Null, {i, Length@L[[p]]}, {j, L[[p, i]]}];
	Do[
		If[L[[i + 1]] =!= L[[i]],
			row = First@FirstPosition[Abs[L[[i]] - L[[i + 1]]], 1];
			If[i < p,
				tableau[[row, L[[i, row]] + 1]] = {i},
				tableau[[row, L[[i, row]]]] = Append[tableau[[row, L[[i, row]]]], i]
			]
		],
		{i, Length@L - 1}
	];
	tableau
]

(* Right tableau of a path: R lists the right partitions along the path; step i >= p that adds a cell labels it {i} *)
YoungTableauxFromYDPathRight[R_, p_] := Module[{tableau, row},
	tableau = Table[Null, {i, Length@Last@R}, {j, Last[R][[i]]}];
	Do[
		If[R[[i + 1]] =!= R[[i]],
			row = First@FirstPosition[R[[i + 1]] - R[[i]], 1];
			tableau[[row, R[[i, row]] + 1]] = {i}
		],
		{i, p, Length@R - 1}
	];
	tableau
]

(* From a path (list of vertices {left, right}, root included) to a pair of mixed Young tableaux *)
PathToYoungTableauxPair[path_] := Module[{p, L, R},
	(* path[[p]] is the vertex at the wall: after it the left partition stops growing *)
	p = First@FirstPosition[Differences[Total /@ path[[All, 1]]], growth_ /; growth <= 0, {Length@path}];
	L = PadRight[#, Length@path[[p, 1]]] & /@ path[[All, 1]];
	R = PadRight[#, Length@path[[-1, 2]]] & /@ path[[All, 2]];
	{YoungTableauxFromYDPathLeft[L, p], YoungTableauxFromYDPathRight[R, p]}
]

TransformAllPathToYT[paths_] := Map[PathToYoungTableauxPair, paths, {2}]

DisplayYoungTableaux[YT_] := If[YT == {},
	ToString@\[EmptySet],
	Grid[
		Map[StringRiffle[ToString /@ #, ","] &, YT, {2}],
		Frame -> {None, None, Flatten[Table[{i, j} -> True, {i, Length@YT}, {j, Length@YT[[i]]}], 1]}
	]
]

DisplayYoungTableauxPair[YTpair_] := DisplayYoungTableaux /@ YTpair

DisplayPathAsYT[path_] := DisplayYoungTableauxPair@PathToYoungTableauxPair@path

DisplayAllPathsAsYT[paths_] := Map[DisplayPathAsYT, paths, {2}]


(* ::Section:: *)
(*Helper functions for Young diagrams*)


(* Positions {row, column} of the cells that can be added to the Young diagram YD, including a new row *)
AddCellPositions[YD_] := With[{rows = Append[YD, 0]},
	Table[If[i == 1 || rows[[i]] < rows[[i - 1]], {i, rows[[i]] + 1}, Nothing], {i, Length@rows}]
]

(* Positions {row, column} of the cells that can be removed from the Young diagram YD *)
RemoveCellPositions[YD_] :=
	Table[If[i == Length@YD || YD[[i]] > YD[[i + 1]], {i, YD[[i]]}, Nothing], {i, Length@YD}]

(* Content of a cell and the axial (Manhattan) distance between two cells *)
Content[cell_] := cell[[2]] - cell[[1]]
HookDistance[cell1_, cell2_] := Content[cell1] - Content[cell2]

(* Walled coordinates {row, column} of a cell given as {tableau, row, column}: cells of the right tableau
   are reflected through the wall *)
wCoord[coord_, d_] := If[coord[[1]] == 1, coord[[2 ;; 3]], {d - coord[[2]] + 1, 1 - coord[[3]]}]

ConjugatePartition[\[Lambda]_] := Table[Count[\[Lambda], row_ /; row >= i], {i, First@\[Lambda]}]

(* Dimension of the irrep \[Lambda] of the unitary group U(d), by the hook-content formula *)
m[\[Lambda]_, d_] := Product[
	(d + j - i) / (\[Lambda][[i]] - j + ConjugatePartition[\[Lambda]][[j]] - i + 1),
	{i, Length@\[Lambda]}, {j, \[Lambda][[i]]}
]


(* ::Section:: *)
(*Generators in the Gelfand-Tsetlin (Young-Yamanouchi) basis*)


(* Action of the generator \[Sigma]_i on the basis vector labelled by the pair of mixed Young tableaux YT, as a list of
   rules  tableau -> coefficient. \[Sigma]_p is the contraction, all other generators are transpositions. *)
Act[i_, YT_, p_, q_, d_] := If[i == p, ActContraction[YT, p, d], ActTransposition[i, YT, p, d]]

(* The contraction is non-zero only if the cell labelled {p, p + 1} exists. It then removes this cell from the left
   tableau and puts it back at every addable position. *)
ActContraction[YT_, p_, d_] := Module[{cell, left, shape, addable, weight},
	cell = FirstPosition[YT, {p, p + 1}];
	If[MissingQ@cell,
		{YT -> 0},
		cell = Rest@cell;
		left = DeleteCases[Delete[First@YT, cell], {}];
		shape = Length /@ left;
		addable = AddCellPositions@shape;
		weight[c_] := Sqrt[
			(d + Content@c) Product[HookDistance[c, corner], {corner, RemoveCellPositions@shape}] /
			Product[HookDistance[c, other], {other, DeleteCases[addable, c]}]
		];
		Table[
			{Insert[If[First@c > Length@left, Append[left, {}], left], {p, p + 1}, c], Last@YT} -> weight[cell] weight[c],
			{c, addable}
		]
	]
]

(* Young's orthogonal form: the transposition (i, i + 1) maps YT to itself and to YT with the labels i and i + 1
   swapped, with coefficients given by the axial distance between the two cells in walled coordinates *)
ActTransposition[i_, YT_, p_, d_] := Module[{label1, label2, cell1, cell2},
	label1 = First@Position[YT, i];
	label2 = First@Position[YT, i + 1];
	cell1 = Most@label1;
	cell2 = Most@label2;
	{
		YT -> 1 / (Sign[p - i] HookDistance[wCoord[cell2, d], wCoord[cell1, d]]),
		ReplacePart[YT, {label1 -> i + 1, label2 -> i}] -> Sqrt[1 - 1 / HookDistance[wCoord[cell1, d], wCoord[cell2, d]]^2]
	}
]

(* Matrices of the generator \[Sigma]_j, one per irrep, in the Gelfand-Tsetlin basis given by paths *)
GeneratorGT[j_, p_, q_, d_, paths_] := Table[
	With[{dim = Length@block},
		SparseArray[
			Flatten@Table[
				If[#[[2]] === 0, Nothing, {Position[block, #[[1]]][[1, 1]], column} -> #[[2]]] & /@
					Act[j, block[[column]], p, q, d],
				{column, dim}
			],
			{dim, dim}
		]
	],
	{block, TransformAllPathToYT[paths]}
]

GeneneratorGT = GeneratorGT; (* deprecated name *)

AllGeneratorsGT[p_, q_, d_, paths_] := Table[GeneratorGT[j, p, q, d, paths], {j, 1, p + q - 1}]
AllGeneratorsGT[p_, q_, d_] := AllGeneratorsGT[p, q, d, AllPaths[p, q, d]]


(* ::Section:: *)
(*Relations of the walled Brauer algebra*)


(* Check the defining relations for the list \[Sigma] of matrices of the generators \[Sigma]_1, ..., \[Sigma]_(p+q-1) *)
CheckRelations[\[Sigma]_, p_, q_, d_] := Module[{n = Length@\[Sigma], transpositions, commuting},
	transpositions = Complement[Range[p + q - 1], {p}];
	commuting = Complement[Range[p + q - 1], {p - 1, p, p + 1}];
	{
		(* relations of the transpositions *)
		Table[If[i == p, Nothing, \[Sigma][[i]] . \[Sigma][[i]] == IdentityMatrix[Length@\[Sigma][[i]]]], {i, n}],
		Table[
			If[i <= p - 2 || i >= p + 1, \[Sigma][[i]] . \[Sigma][[i + 1]] . \[Sigma][[i]] == \[Sigma][[i + 1]] . \[Sigma][[i]] . \[Sigma][[i + 1]], Nothing],
			{i, n - 1}
		],
		Flatten@Table[
			If[Abs[i - j] > 1, \[Sigma][[j]] . \[Sigma][[i]] == \[Sigma][[i]] . \[Sigma][[j]], Nothing],
			{i, transpositions}, {j, transpositions}
		],
		(* relations involving the contraction \[Sigma]_p *)
		{If[n >= p >= 1, \[Sigma][[p]] . \[Sigma][[p]] == d \[Sigma][[p]], Nothing]},
		{
			If[n >= p >= 2, \[Sigma][[p]] . \[Sigma][[p - 1]] . \[Sigma][[p]] == \[Sigma][[p]], Nothing],
			If[q >= 2 && p >= 1, \[Sigma][[p]] . \[Sigma][[p + 1]] . \[Sigma][[p]] == \[Sigma][[p]], Nothing]
		},
		Table[If[n >= p >= 1, \[Sigma][[p]] . \[Sigma][[i]] == \[Sigma][[i]] . \[Sigma][[p]], Nothing], {i, commuting}],
		If[Min[p, q] >= 2,
			{
				\[Sigma][[p]] . \[Sigma][[p + 1]] . \[Sigma][[p - 1]] . \[Sigma][[p]] . \[Sigma][[p - 1]] ==
					\[Sigma][[p]] . \[Sigma][[p + 1]] . \[Sigma][[p - 1]] . \[Sigma][[p]] . \[Sigma][[p + 1]],
				\[Sigma][[p - 1]] . \[Sigma][[p]] . \[Sigma][[p + 1]] . \[Sigma][[p - 1]] . \[Sigma][[p]] ==
					\[Sigma][[p + 1]] . \[Sigma][[p]] . \[Sigma][[p + 1]] . \[Sigma][[p - 1]] . \[Sigma][[p]]
			},
			{}
		]
	}
]
