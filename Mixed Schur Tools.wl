(* ::Package:: *)

(* ::Input::Initialization:: *)
(*Tools*)
ToStaircase[{\[Lambda]left_,\[Lambda]right_,d_}]:=Catch@If[Length@\[Lambda]left+Length@\[Lambda]right>d,Throw["Height error"],PadRight[\[Lambda]left,d]-PadLeft[Reverse@\[Lambda]right,d]]
ToPair[\[Lambda]_]:={Select[\[Lambda],#>0&],-Reverse@Select[\[Lambda],#<0&],Length@\[Lambda]}
TransposePartition[\[Lambda]_]:=Table[Count[\[Lambda],u_/;u>=i],{i,\[Lambda][[1]]}]
Id[dim_]:=SparseArray[{Band[{1,1}]->1},{dim,dim}]

Enumerate[lst_List]:=MapIndexed[{#1,#2[[1]]}&,lst]

DisplayStaircase[\[Lambda]_]:=If[(Length[\[Lambda]]==Count[\[Lambda],u_/;u==0])||(\[Lambda]=={}),\[EmptySet],With[{offset=If[Min[\[Lambda]]<0, -Min[\[Lambda]],0]},Grid[Table[Table[" ",{k,Abs@rowLength+offset}],{rowLength,\[Lambda]}],Dividers->{{offset+1->{Thick}}},Frame->{None,None,Flatten@Table[{i,j+offset}->True,{i,Length@\[Lambda]},{j,Min[\[Lambda][[i]],0]+1,Max[\[Lambda][[i]],0]}]}]
]]


(* ::Input::Initialization:: *)
(*Walled Brauer algebra Bratteli diagram*)
ClearAll[BratteliLevelsWBA,BratteliDiagramWBA,BratteliDiagramWBALabelled]

BratteliLevelsWBA[n_,m_,d_]:=BratteliLevelsWBA[n,m,d]=Table[{ToStaircase[{x,{},d}],i},{i,0,n},{x,IntegerPartitions[i,d]}]~Join~Table[Flatten[Table[{ToStaircase[{x,y,d}],n+i},{k,0,Min[n,i]},{x,IntegerPartitions[n-k,d]},{y,IntegerPartitions[i-k,d-Length@x]}],2],{i,1,m}]

OrderWBA[x_,y_]:=If[x[[2]]+1==y[[2]],If[Counts[x[[1]]-y[[1]]][0]==Length[x[[1]]]-1,True,False],False]

BratteliDiagramWBA[n_,m_,d_]:=BratteliDiagramWBA[n,m,d]=With[{vertices=Flatten[BratteliLevelsWBA[n,m,d],1]},RelationGraph[OrderWBA,vertices,VertexSize->0.2,VertexStyle->LightBlue,VertexLabels->Table[v->Placed[DisplayStaircase[v[[1]]],Tooltip],{v,vertices}],GraphLayout->"LayeredDigraphEmbedding",ImageSize->Small]]

BratteliDiagramWBALabelled[n_,m_,d_]:=With[{vertices=Flatten[BratteliLevelsWBA[n,m,d],1]},RelationGraph[OrderWBA,vertices,VertexSize->0.4,VertexShape->Graphics[{Transparent,Disk[]}],VertexStyle->LightBlue,VertexLabels->Table[v->Placed[DisplayStaircase[v[[1]]],Center],{v,vertices}],GraphLayout->"LayeredDigraphEmbedding"]]


(* ::Input::Initialization:: *)
(*List all Irreps, Paths and Irrep dimensions for Walled Brauer Algebra*)
ClearAll[PathsToIrrepWBA,AllPathsWBA,IrrepDimsWBA,AssociationIrrepsWBA,AssociationPathsToIrrepWBA,Irreps]

Irreps[n_,m_,d_]:=Irreps[n,m,d]=Flatten[Table[ToStaircase[{x,y,d}],{k,0,Min[n,m]},{x,IntegerPartitions[n-k,d]},{y,IntegerPartitions[m-k,d-Length@x]}],2]

PathsToIrrepWBA[\[Lambda]_,n_,m_,d_]:=PathsToIrrepWBA[\[Lambda],n,m,d]=#[[2;;-1,1]]&/@FindPath[BratteliDiagramWBA[n,m,d],{ConstantArray[0,d],0},{\[Lambda],n+m},{n+m},All]
IrrepDimWBA[\[Lambda]_,n_,m_,d_]:=IrrepDimWBA[\[Lambda],n,m,d]=Length@PathsToIrrepWBA[\[Lambda],n,m,d]
AllPathsWBA[n_,m_,d_]:=AllPathsWBA[n,m,d]=PathsToIrrepWBA[#,n,m,d]&/@Irreps[n,m,d]
IrrepDimsWBA[n_,m_,d_]:=IrrepDimsWBA[n,m,d]=Length/@AllPathsWBA[n,m,d]

(*Make associations*)
AssociationIrrepsWBA[n_,m_,d_]:=AssociationIrrepsWBA[n,m,d]=Association[Table[Irreps[n,m,d][[i]]->i,{i,Length@Irreps[n,m,d]}]]
AssociationPathsToIrrepWBA[\[Lambda]_,n_,m_,d_]:=AssociationPathsToIrrepWBA[\[Lambda],n,m,d]=Association[Table[PathsToIrrepWBA[\[Lambda],n,m,d][[i]]->i,{i,Length@PathsToIrrepWBA[\[Lambda],n,m,d]}]]


(* ::Input::Initialization:: *)
(*Bratteli diagram of the General Linear/Unitary Groups*)
ClearAll[BratteliLevelsGL,BratteliDiagramGL,AllGTPatterns,IrrepDimsGL]

InterlacingCanditates[\[Lambda]_]:=Reverse[Sort[Tuples[Table[Table[k,{k,\[Lambda][[i]],\[Lambda][[i+1]],-1}],{i,Length[\[Lambda]]-1}]]]]
BratteliLevelsGL[n_,m_,d_]:=BratteliLevelsGL[n,m,d]=Reverse@NestList[(Reverse@Sort@Union@Flatten[InterlacingCanditates/@#,1])&,Irreps[n,m,d],d]

OrderGL[y_,x_]:=If[Length[x]==Length[y]+1,AllTrue[({x[[1;;-2]],y}\[Transpose])~Join~({y,x[[2;;-1]]}\[Transpose]),#[[1]]>=#[[2]]&],False]

BratteliDiagramGL[n_,m_,d_]:=BratteliDiagramGL[n,m,d]=With[{vertices=Flatten[BratteliLevelsGL[n,m,d],1]},RelationGraph[OrderGL,vertices,VertexSize->0.2,VertexStyle->LightRed,VertexLabels->Table[v->Placed[DisplayStaircase[v],Tooltip],{v,vertices}],GraphLayout->"LayeredDigraphEmbedding",ImageSize->Small]]

AllGTPatterns[n_,m_,d_]:=AllGTPatterns[n,m,d]=Table[#[[2;;-1]]&/@FindPath[BratteliDiagramGL[n,m,d],{},\[Lambda],{d},All],{\[Lambda],Irreps[n,m,d]}]
IrrepDimsGL[n_,m_,d_]:=Length/@AllGTPatterns[n,m,d]


(* ::Input::Initialization:: *)
(*Gelfand-Tsetlin patterns*)
ClearAll[GTPatterns,AssociationGTPatterns]

GTPatterns[\[Lambda]_]:=GTPatterns[\[Lambda]]=Reverse@Sort@With[{vertices=Flatten[Reverse@NestList[(Reverse@Sort@Union@Flatten[InterlacingCanditates/@#,1])&,{\[Lambda]},Length@\[Lambda]],1]},#[[2;;-1]]&/@FindPath[RelationGraph[OrderGL,vertices],{},\[Lambda],{Length@\[Lambda]},All]]

WeylDim[\[Lambda]_]:=Product[(\[Lambda][[i]]-\[Lambda][[j]]+j-i)/(j-i),{i,1,Length@\[Lambda]-1},{j,i+1,Length@\[Lambda]}]

AssociationGTPatterns[\[Lambda]_]:=AssociationGTPatterns[\[Lambda]]=Association[Table[GTPatterns[\[Lambda]][[i]]->i,{i,Length@GTPatterns[\[Lambda]]}]]


(* ::Input::Initialization:: *)
(*Reduced Wigner coefficients and Clebsch-Gordan coefficients*)
ClearAll[RWcoef,CGcoef]

RWcoef[M_,m_,N_]:=RWcoef[M,m,N]=Module[{j,i},
Which[
(m[[1,1]]==0)&&(m[[2,1]]==1),
If[(Count[N[[2]]-M[[2]],0]+1==Length[N[[2]]])&&(Count[N[[2]]-M[[2]],1]==1)&&(M[[1]]===N[[1]]),
i=Position[N[[2]]-M[[2]],1][[1,1]];
\[Sqrt](Product[M[[1,k]]-k-(M[[2,i]]-i)-1,{k,Length[M[[1]]]}]/Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[2,i]]-i)),{k,Length[M[[2]]]}]),0],

m[[1,1]]==m[[2,1]]==1,
If[(Count[N[[1]]-M[[1]],0]+1==Count[N[[2]]-M[[2]],0]==Length[N[[1]]])&&(Count[N[[1]]-M[[1]],1]==Count[N[[2]]-M[[2]],1]==1),
j=Position[N[[1]]-M[[1]],1][[1,1]];
i=Position[N[[2]]-M[[2]],1][[1,1]];
If[i<=j,1,-1]*
\[Sqrt]((Product[KroneckerDelta[k,j]+(1-KroneckerDelta[k,j])(M[[1,k]]-k-(M[[2,i]]-i)-1),{k,Length[M[[1]]]}]*Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[1,j]]-j)),{k,Length[M[[2]]]}])/(Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[2,i]]-i)),{k,Length[M[[2]]]}]*Product[KroneckerDelta[k,j]+(1-KroneckerDelta[k,j])(M[[1,k]]-k-(M[[1,j]]-j)-1),{k,Length[M[[1]]]}]))
,0],

(m[[1,-1]]==0)&&(m[[2,-1]]==-1),
If[(Count[N[[2]]-M[[2]],0]+1==Length[N[[2]]])&&(Count[N[[2]]-M[[2]],-1]==1)&&(M[[1]]===N[[1]]),
i=Position[N[[2]]-M[[2]],-1][[1,1]];
\[Sqrt](Product[M[[1,k]]-k-(M[[2,i]]-i),{k,Length[M[[1]]]}]/Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[2,i]]-i)),{k,Length[M[[2]]]}]),0],

m[[1,-1]]==m[[2,-1]]==-1,
If[(Count[N[[1]]-M[[1]],0]+1==Count[N[[2]]-M[[2]],0]==Length[N[[1]]])&&(Count[N[[1]]-M[[1]],-1]==Count[N[[2]]-M[[2]],-1]==1),
j=Position[N[[1]]-M[[1]],-1][[1,1]];
i=Position[N[[2]]-M[[2]],-1][[1,1]];
If[i<=j,1,-1]*
\[Sqrt]((Product[KroneckerDelta[k,j]+(1-KroneckerDelta[k,j])(M[[1,k]]-k-(M[[2,i]]-i)),{k,Length[M[[1]]]}]*Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[1,j]]-j)+1),{k,Length[M[[2]]]}])/(Product[KroneckerDelta[k,i]+(1-KroneckerDelta[k,i])(M[[2,k]]-k-(M[[2,i]]-i)),{k,Length[M[[2]]]}]*Product[KroneckerDelta[k,j]+(1-KroneckerDelta[k,j])(M[[1,k]]-k-(M[[1,j]]-j)+1),{k,Length[M[[1]]]}]))
,0]
]]

CGcoef[M_,Xsigned_,N_]:=CGcoef[M,Xsigned,N]=Module[{d,m},
d=Length[M];
m=If[Xsigned>0,Table[If[(i>=Xsigned)&&(j==1),1,0],{i,d},{j,i}],Table[If[(i>=-Xsigned)&&(j==i),-1,0],{i,d},{j,i}]];
If[Abs[Xsigned]>=2,
If[AllTrue[Table[{M[[i]],N[[i]]},{i,Abs[Xsigned]-1}],#[[1]]==#[[2]]&],
Product[RWcoef[M[[i;;i+1]],m[[i;;i+1]],N[[i;;i+1]]],{i,Abs[Xsigned]-1,d-1}],0],
Product[RWcoef[M[[i;;i+1]],m[[i;;i+1]],N[[i;;i+1]]],{i,1,d-1}]]
]


(* ::Input::Initialization:: *)
(*Construct Clebsch-Gordan tensor*)
ClearAll[CG,GTcandidates]

rowGTPatternsCandidates[NList_,M_,x_,sign_]:=Flatten[Table[
({#}~Join~N)&/@Select[InterlacingCanditates[N[[1]]],If[Length[N[[1]]]>x,(Count[#-M[[Length[N[[1]]]-1]],0]==(Length[N[[1]]]-2))&&(Plus@@(#-M[[Length[N[[1]]]-1]])==sign),Counts[#-M[[Length[N[[1]]]-1]]][0]==(Length[N[[1]]]-1)]&],{N,NList}
],1]

GTcandidates[\[Lambda]_,M_,x_]:=GTcandidates[\[Lambda],M,x]=With[{sign=Plus@@(\[Lambda]-M[[-1]])},Nest[rowGTPatternsCandidates[#,M,x,sign]&,{{\[Lambda]}},Length@\[Lambda]-1]]

CG[\[Mu]_,\[Lambda]_]:=CG[\[Mu],\[Lambda]]=Catch[Block[{d,data,sign},
d=If[Length@\[Mu]!=Length@\[Lambda],Throw["Incompatible local dims"],Length@\[Mu]];
sign=If[Counts[\[Mu]-\[Lambda]][0]!=Length[\[Mu]]-1,Throw["Incompatible irreps"],Plus@@(\[Lambda]-\[Mu])];
data=Flatten@Table[{x,AssociationGTPatterns[\[Mu]][M],AssociationGTPatterns[\[Lambda]][N]}->CGcoef[M,sign*x,N],{M,GTPatterns[\[Mu]]},{x,1,d},{N,GTcandidates[\[Lambda],M,x]}];
SparseArray[data,{d,WeylDim[\[Mu]],WeylDim[\[Lambda]]}]
]]

CG[\[Mu]_,\[Lambda]_,d_]:=CG[PadRight[\[Mu],d],PadRight[\[Lambda],d]]


(* ::Input::Initialization:: *)
Weight[x_,n_,m_,d_]:=Table[Count[x[[;;n]],i],{i,Range[d]}]-Table[Count[x[[n+1;;n+m]],i],{i,Range[d]}]
Weight[x_,i_,n_,m_,d_]:=Weight[PadRight[x[[1;;i]],n+m],n,m,d]
Weight[x_,{n_,m_,d_}]:=Weight[x,n,m,d]


(* ::Input::Initialization:: *)
ClearAll[SchurBasis,StandardBasis,SchurIndex,SchurCoef,CGmatProduct]

SchurIndex[y_,n_,m_,d_]:=Block[{\[Lambda]=y[[1,-1]],l,i,j},
l=AssociationIrrepsWBA[n,m,d][\[Lambda]];
i=AssociationPathsToIrrepWBA[\[Lambda],n,m,d][y[[1]]];
j=AssociationGTPatterns[\[Lambda]][y[[2]]];
IrrepDimsWBA[n,m,d][[;;l-1]] . IrrepDimsGL[n,m,d][[;;l-1]]+IrrepDimsGL[n,m,d][[l]]*(i-1)+j
]

SchurBasis[n_,m_,d_]:=SchurBasis[n,m,d]=Flatten[Table[Tuples[{AllPathsWBA[n,m,d][[i]]}~Join~{GTPatterns[Irreps[n,m,d][[i]]]}],{i,Length@Irreps[n,m,d]}],1]

StandardBasis[n_,d_]:=StandardBasis[n,d]=Tuples[Range[d],n]

(*Multiply CG tensors to get Schur coefficient*)
CGmatProduct[x_List,T_List]:=CGmatProduct[x,T]=With[{d=Length[T[[-1]]]},Dot@@({CG[ConstantArray[0,d],T[[1]]][[x[[1]],1,All]]}~Join~Table[CG[T[[k-1]],T[[k]]][[x[[k]],All,All]],{k,2,Length@T}])]

SchurCoef[x_List,{T_List,M_List}]:=SchurCoef[x,{T,M}]=(CGmatProduct[x,T] . SparseArray[{AssociationGTPatterns[T[[-1]]][M]}->1,{WeylDim[T[[-1]]]}])

(*Slow version of Schur transform: it goes through every matrix entry*)
SchurTransformSlow[n_,m_,d_]:=SchurTransformSlow[n,m,d]=SparseArray[Flatten@Table[{SchurIndex[y,n,m,d],x}->SchurCoef[IntegerDigits[x-1,d,n+m]+1,y],{x,d^(n+m)},{y,SchurBasis[n,m,d]}],d^(n+m)]


(* ::Input::Initialization:: *)
(*Primitives for WBA Bratteli diagram restricted to a given input string x. This gives faster Schur tranform Sparse Array.*)
ClearAll[GTPatternsWeight,BratteliLevelsWBAString,BratteliDiagramWBAString,AllPathsWBAString,SchurBasisGivenString]

GTPatternsWeight[\[Lambda]_,weight_]:=GTPatterns[\[Lambda]][[Lookup[PositionIndex[Differences[{0}~Join~(Plus@@@#)]&/@GTPatterns[\[Lambda]]],Key[weight],{}]]]

BratteliLevelsWBAString[x_,n_,m_,d_]:=BratteliLevelsWBAString[x,n,m,d]={BratteliLevelsWBA[n,m,d][[1]]}~Join~Table[If[Length@GTPatternsWeight[#[[1]],Weight[x,i,n,m,d]]==0,Nothing,#]&/@BratteliLevelsWBA[n,m,d][[i+1]],{i,n+m}]

BratteliDiagramWBAString[x_,n_,m_,d_]:=BratteliDiagramWBAString[x,n,m,d]=With[{vertices=Flatten[BratteliLevelsWBAString[x,n,m,d],1]},RelationGraph[OrderWBA,vertices,GraphLayout->"LayeredDigraphEmbedding",VertexLabels->Table[v->Placed[DisplayStaircase[v[[1]]],Tooltip],{v,vertices}]]]

AllPathsWBAString[x_,n_,m_,d_]:=DeleteCases[#[[All,2;;-1,1]]&/@With[{g=BratteliDiagramWBAString[x,n,m,d]},FindPath[g,{ConstantArray[0,d],0},#,{n+m},All]&/@BratteliLevelsWBAString[x,n,m,d][[-1]]],{}]

SchurBasisGivenString[x_,n_,m_,d_]:=With[{paths=AllPathsWBAString[x,n,m,d]},
Flatten[Table[Tuples[{paths[[i]]}~Join~{GTPatternsWeight[paths[[i,1,-1]],Weight[x,n,m,d]]}],{i,Length@paths}],1]
]


(* ::Input::Initialization:: *)
(*Schur transform (fastest version)*)
SchurTransform[n_,m_,d_]:=SchurTransform[n,m,d]=SparseArray[Flatten@Table[{SchurIndex[y,n,m,d],x}->SchurCoef[IntegerDigits[x-1,d,n+m]+1,y],{x,d^(n+m)},{y,SchurBasisGivenString[IntegerDigits[x-1,d,n+m]+1,n,m,d]}],d^(n+m)]


(* ::Input::Initialization:: *)
(*Gelfand-Tsetlin basis for Partially Transposed Permutation matrix algebra*)

WalledContent[T_,i_]:=Module[{path,pos,sign},
path={ConstantArray[0,Length@T[[-1]]]}~Join~T;
pos=PositionIndex[Abs/@(path[[i+1]]-path[[i]])];
sign=Total[path[[i+1]]-path[[i]]];
If[MissingQ[pos[1]],1,sign(path[[If[sign>0,i+1,i],pos[1][[1]]]]-pos[1][[1]])]
]

r[T_,i_]:=WalledContent[T,i+1]-WalledContent[T,i]

\[Sigma]T[T_,i_]:=ReplacePart[T,i->T[[i+1]]-T[[i]]+If[i==1,ConstantArray[0,Length@T[[-1]]],T[[i-1]]]]

transpostionGT[i_,n_,m_,d_]:=Catch[If[i==n,Throw["This generator is not a transposition. Choose i not equal to n."],Table[SparseArray[Flatten[Table[If[Abs[r[T,i]]==1,{{AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T],AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T]}->r[T,i]},{{AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T],AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T]}->1/r[T,i],{AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T],AssociationPathsToIrrepWBA[\[Lambda],n,m,d][\[Sigma]T[T,i]]}->Sqrt[1-1/r[T,i]^2]}],{T,PathsToIrrepWBA[\[Lambda],n,m,d]}],1],{IrrepDimWBA[\[Lambda],n,m,d],IrrepDimWBA[\[Lambda],n,m,d]}],{\[Lambda],Irreps[n,m,d]}]]]

AddCell[\[Lambda]_,i_]:=Table[\[Lambda][[j]]+KroneckerDelta[j,i],{j,Length@\[Lambda]}]

AddableCells[\[Lambda]_]:={1}~Join~Table[If[\[Lambda][[i-1]]>\[Lambda][[i]],i,Nothing],{i,2,Length@\[Lambda]}]

contractionGT[n_,m_,d_]:=Catch[If[m==0,Throw["There is no contraction generator. Choose m>0."],Table[SparseArray[Flatten[Table[If[T[[n-1]]==T[[n+1]],Table[{AssociationPathsToIrrepWBA[\[Lambda],n,m,d][T],AssociationPathsToIrrepWBA[\[Lambda],n,m,d][ReplacePart[T,n->AddCell[T[[n-1]],a]]]}->Sqrt[WeylDim[T[[n]]]WeylDim[AddCell[T[[n-1]],a]]]/WeylDim[T[[n-1]]],{a,AddableCells[T[[n-1]]]}],{}],{T,PathsToIrrepWBA[\[Lambda],n,m,d]}],1],{IrrepDimWBA[\[Lambda],n,m,d],IrrepDimWBA[\[Lambda],n,m,d]}],{\[Lambda],Irreps[n,m,d]}]]]

generatorsGT[n_,m_,d_]:=Table[If[i!=n,transpostionGT[i,n,m,d],contractionGT[n,m,d]],{i,n+m-1}]
