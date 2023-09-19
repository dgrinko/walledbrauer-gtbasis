(* ::Package:: *)

(*Primitives for constructing the Bratteli diagram of the Walled Brauer Algebra*)
BratteliLevels[p_,q_,d_]:=BratteliLevels[p,q,d]=Table[{x,{},i},{i,0,p},{x,IntegerPartitions[i,d]}]~Join~Table[Flatten[Table[{x,y,p+i},{k,0,Min[p,i]},{x,IntegerPartitions[p-k,d]},{y,IntegerPartitions[i-k,d-Length@x]}],2],{i,1,q}]

Contains[x_,y_]:=Module[{d,xn,yn},
	d=Max[Length[x],Length[y]];
	{xn,yn}={PadRight[x,d],PadRight[y,d]};
	AllTrue[{xn,yn}\[Transpose],#[[1]]>=#[[2]]&]
]

OrderWBA[x_,y_]:=
If[x[[3]]+1==y[[3]],
	If[(Total[x[[1]]]==x[[3]])&&(Total[y[[1]]]==y[[3]]),
		Contains[y[[1]],x[[1]]],
		If[(Total[x[[1]]]<=x[[3]])&&(Total[y[[1]]]<y[[3]]),
			If[Total[y[[1]]]==Total[x[[1]]],
				Contains[y[[2]],x[[2]]]&&Contains[x[[1]],y[[1]]],
					If[Total[y[[2]]]==Total[x[[2]]],
						Contains[x[[2]],y[[2]]]&&Contains[x[[1]],y[[1]]],
					False],
			False]
		],
	False],
False]

BratteliDiagram[p_,q_,d_]:=BratteliDiagram[p,q,d]=RelationGraph[OrderWBA,Flatten[BratteliLevels[p,q,d],1],GraphLayout->"LayeredDigraphEmbedding"]

(*List all Irreps, Paths and Irrep dimensions*)
Irreps[p_,q_,d_]:=Irreps[p,q,d]=BratteliLevels[p,q,d][[-1,All,1;;2]]
AllPaths[p_,q_,d_]:=AllPaths[p,q,d]=(#[[All,1;;2]]&/@FindPath[BratteliDiagram[p,q,d],{{},{},0},{#[[1]],#[[2]],p+q},{p+q},All])&/@Irreps[p,q,d]
IrrepDims[p_,q_,d_]:=IrrepDims[p,q,d]=Length/@AllPaths[p,q,d]


(*Display Young Diagram (YD) nicely*)
DisplayYoungDiagram[YD_]:=DisplayYoungDiagram[YD]=If[YD=={},ToString@\[EmptySet],Grid[Table[Table[" ",{i,rowLength}],{rowLength,YD}],Frame->Join[{None},{None},{Flatten[With[{cc=Range@#&/@YD},Table[Flatten[{nn,#}->True&/@cc[[nn]],1],{nn,Length@cc}]],1]}]]]

(*Functions for conversion between path and mixed Young Tableaux*)
YoungTableauxFromYDPathLeft[L_,p_]:=Module[{YTL,index,i},
YTL=Table[Table[Null,{j,i}],{i,L[[p]]}];
For[i=1,i<Length@L,i++,
If[L[[i+1]]==L[[i]],Nothing,index=Position[Abs/@(L[[i]]-L[[i+1]]),1][[1,1]]];
If[i<p,YTL[[index,L[[i,index]]+1]]={i},If[L[[i+1]]==L[[i]],Nothing,
YTL[[index,L[[i,index]]]]=YTL[[index,L[[i,index]]]]~Join~{i}]]
];YTL
]

YoungTableauxFromYDPathRight[R_,p_]:=Module[{YTR,index,i},
YTR=Table[Table[Null,{j,i}],{i,R[[-1]]}];
For[i=p,i<Length@R,i++,
If[R[[i+1]]==R[[i]],Nothing,index=Position[R[[i+1]]-R[[i]],1][[1,1]]];
If[R[[i+1]]==R[[i]],Nothing,
YTR[[index,R[[i,index]]+1]]={i}]
];YTR
]

(*From a path to a mixed Young Tableaux*)
PathToYoungTableauxPair[path_]:=Module[{p,L,R,YTL,index},
p=FirstPosition[Table[Total@path[[i+1,1]]-Total@path[[i,1]],{i, Length[path]-1}],x_/;x<=0,{Length@path}][[1]];
L=PadRight[#,Length@path[[p,1]]]&/@path[[All,1]];
R=PadRight[#,Length@path[[-1,2]]]&/@path[[All,2]];
{YoungTableauxFromYDPathLeft[L,p],YoungTableauxFromYDPathRight[R,p]}]

TransformAllPathToYT[paths_]:=(PathToYoungTableauxPair[#]&/@#)&/@paths

(*Display mixed Young tableaux*)
DisplayYoungTableaux[YT_]:=If[YT=={},ToString@\[EmptySet],Grid[((StringJoin[ToString/@Riffle[#,","]]&/@#)&/@YT),Frame->Join[{None},{None},{Flatten[With[{cc=Range@#&/@(Length/@YT)},Table[Flatten[{nn,#}->True&/@cc[[nn]],1],{nn,Length@cc}]],1]}]]]
DisplayYoungTableauxPair[YTpair_]:={DisplayYoungTableaux[YTpair[[1]]],DisplayYoungTableaux[YTpair[[2]]]}

(*Display paths as mixed Young Tableaux*)
DisplayPathAsYT[path_]:=DisplayYoungTableauxPair[PathToYoungTableauxPair[path]]
DisplayAllPathsAsYT[paths_]:=(DisplayYoungTableauxPair[PathToYoungTableauxPair[#]]&/@#)&/@paths


(*Helper functions for Young Diagrams*)
AddCellPositions[YD_]:=Module[{padYD},
padYD=PadRight[YD,Length@YD+1];
Table[If[i==1,{1,padYD[[1]]+1},If[padYD[[i]]<padYD[[i-1]],{i,padYD[[i]]+1},Nothing]],{i,Length@padYD}]
]

RemoveCellPositions[YD_]:=Module[{padYD},
Table[If[i==Length@YD,{i,YD[[i]]},If[YD[[i]]>YD[[i+1]],{i,YD[[i]]},Nothing]],{i,Length@YD}]
]

(*Standard Hook (Manhattan) distance and Content*)
Content[cell_]:=cell[[2]]-cell[[1]]
HookDistance[cell1_,cell2_]:=Content[cell1]-Content[cell2]

(*Walled coordinate and distance of a cell*)
wCoord[coord_,d_]:=If[coord[[1]]==1,coord[[2;;3]],{d-coord[[2]]+1,1-coord[[3]]}]

(*Conjugate partition*)
ConjugatePartition[\[Lambda]_]:=Table[Count[\[Lambda]-i+1,u_/;u>0],{i,\[Lambda][[1]]}]

(*Dimension of unitary group irrep*)
m[\[Lambda]_,d_]:=Times@@Flatten@Table[(d+j-i)/(\[Lambda][[i]]-j+ConjugatePartition[\[Lambda]][[j]]-i+1),{i,1,Length@\[Lambda]},{j,1,\[Lambda][[i]]}]


(*Young-Yamanouchi basis functions*)

Act[i_,YT_,p_,q_,d_]:=Module[{tmpYT,coord1,coord2,mobElemFixed,LambdaYT,LambdaYD,vec,out},
tmpYT=YT;
If[i==p,If[Position[YT,{p,p+1}]=={},{YT->0},
mobElemFixed=Position[YT,{p,p+1}][[1,2;;-1]];
LambdaYT=Select[Delete[YT[[1]],mobElemFixed],UnsameQ[#,{}]&];
LambdaYD=Length/@(LambdaYT);
vec=Table[\[Sqrt]((d+Content[mobileElem])(Product[HookDistance[mobileElem,corner],{corner,RemoveCellPositions[LambdaYD]}]/Product[HookDistance[mobileElem,mobileElem2],{mobileElem2,DeleteCases[AddCellPositions[LambdaYD],mobileElem]}])),{mobileElem,AddCellPositions[LambdaYD]}];
out=Table[{If[mobileElem[[1]]==Length[LambdaYD]+1,Insert[PadRight[LambdaYT,Length[LambdaYD]+1,{{}}],{p,p+1},mobileElem],Insert[LambdaYT,{p,p+1},mobileElem]],YT[[2]]}->vec[[Position[AddCellPositions[LambdaYD],mobElemFixed][[1,1]]]]*vec[[Position[AddCellPositions[LambdaYD],mobileElem][[1,1]]]],{mobileElem,AddCellPositions[LambdaYD]}];
out]
,
coord1=Position[tmpYT,i][[1,1;;-2]];
coord2=Position[tmpYT,i+1][[1,1;;-2]];
tmpYT=ReplacePart[tmpYT,coord1->ReplacePart[tmpYT[[Sequence@@coord1]],If[(i>=p)&&(Length[tmpYT[[Sequence@@coord1]]]==2),2,1]->i+1]];
tmpYT=ReplacePart[tmpYT,coord2->ReplacePart[tmpYT[[Sequence@@coord2]],If[(i>=p)&&(Length[tmpYT[[Sequence@@coord2]]]==2),2,1]->i]];
{YT->1/(Sign[p-i]HookDistance[wCoord[coord2,d],wCoord[coord1,d]]),tmpYT->Sqrt[1-1/HookDistance[wCoord[coord1,d],wCoord[coord2,d]]^2]}
]
]

(*Check Walled Brauer Algebra realtions for the list of representation matrices \[Sigma]*)
CheckRelations[\[Sigma]_,p_,q_,d_]:=Module[{n,transpList,contrList},
n=Length@\[Sigma];
contrList=Complement[Range[p+q-1],{p-1,p,p+1}];
transpList=Complement[Range[p+q-1],{p}];
{
(*Relations involving only Coxeter generators*)
Table[If[i==p,Nothing,\[Sigma][[i]] . \[Sigma][[i]]==IdentityMatrix[Length@\[Sigma][[i]]]],{i,n}],
Table[If[(i<=p-2)||(i>=p+1),\[Sigma][[i]] . \[Sigma][[i+1]] . \[Sigma][[i]]==\[Sigma][[i+1]] . \[Sigma][[i]] . \[Sigma][[i+1]],Nothing],{i,n-1}],
Flatten@Table[If[Abs[i-j]>1,\[Sigma][[j]] . \[Sigma][[i]]==\[Sigma][[i]] . \[Sigma][[j]],Nothing],{i, transpList},{j,transpList}],
(*Relations involving the contraction generator*)
{If[n>=p>=1,\[Sigma][[p]] . \[Sigma][[p]]==d*\[Sigma][[p]],Nothing]};
{If[n>=p>=2,\[Sigma][[p]] . \[Sigma][[p-1]] . \[Sigma][[p]]==\[Sigma][[p]],Nothing],If[(q>=2)&&(p>=1),\[Sigma][[p]] . \[Sigma][[p+1]] . \[Sigma][[p]]==\[Sigma][[p]],Nothing]},
Table[If[n>=p>=1,\[Sigma][[p]] . \[Sigma][[i]]==\[Sigma][[i]] . \[Sigma][[p]],Nothing],{i,contrList}],
Flatten@{If[Min[p,q]>=2,{\[Sigma][[p]] . \[Sigma][[p+1]] . \[Sigma][[p-1]] . \[Sigma][[p]] . \[Sigma][[p-1]]==\[Sigma][[p]] . \[Sigma][[p+1]] . \[Sigma][[p-1]] . \[Sigma][[p]] . \[Sigma][[p+1]],\[Sigma][[p-1]] . \[Sigma][[p]] . \[Sigma][[p+1]] . \[Sigma][[p-1]] . \[Sigma][[p]]==\[Sigma][[p+1]] . \[Sigma][[p]] . \[Sigma][[p+1]] . \[Sigma][[p-1]] . \[Sigma][[p]]},Nothing]}
}
]

(*Generate all irrep matrices for j-th generator*)
GeneneratorGT[j_,p_,q_,d_,paths_]:=Table[SparseArray[Flatten@Table[(If[#[[2]]=!=0,{Position[block,#[[1]]][[1,1]],pathIndex}->#[[2]],If[Position[block,#[[1]]]==={},Nothing,{pathIndex,pathIndex}->0]])&/@Act[j,block[[pathIndex]],p,q,d],{pathIndex,Length@block}]],{block,TransformAllPathToYT[paths]}]
AllGeneratorsGT[p_,q_,d_,paths_]:=Table[GeneneratorGT[j,p,q,d,paths],{j,1,p+q-1}];
AllGeneratorsGT[p_,q_,d_]:=Table[GeneneratorGT[j,p,q,d,AllPaths[p,q,d]],{j,1,p+q-1}];
