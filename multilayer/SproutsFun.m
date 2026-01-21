(* ::Package:: *)

BeginPackage["SproutsFun`"];


MyChebyshev::usage="";
DiffOperator::usage="";
MakeMatD::usage="";
MakeVec::usage="";
MakeCol::usage="";
MakeMatbc::usage="";
InfoSprouts::usage="";
BuildSparseIterate::usage="";


Begin["`Private`"];


(* ::Section:: *)
(*Chebyshev discretization*)


(* ::Text:: *)
(*based on Olver et al.*)


Needs["spectral`","../spectral.m"];


(*(* evaluate derivative of Chebyshev polynomial at one point and save result *)
ClearAll[MyChebyshev]
Options[MyChebyshev]={parity->None};
MyChebyshev[der_Integer,u0_?NumericQ,n_Integer,opts:OptionsPattern[]]:=MyChebyshev[der,u0,n,opts]=
Block[{p=OptionValue[parity]},
Which[
SameQ[p,"even"],Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,0,n-2,2}],
SameQ[p,"odd"],Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,1,n-1,2}],
True,Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,0,n-1}]
]
]*)


(* evaluate derivative of Chebyshev polynomial at one point and save result *)
ClearAll[MyChebyshev]
Options[MyChebyshev]={parity->None};
MyChebyshev[der_Integer,u0_?NumericQ,n_Integer,opts:OptionsPattern[]]:=MyChebyshev[der,u0,n,opts]=
Block[{p=OptionValue[parity]},
Which[
SameQ[p,"even"],
Table[If[SameQ[1,u0]\[Or]SameQ[-1,u0],u0^(k+der) \!\(
\*SubsuperscriptBox[\(\[Product]\), \(l = 0\), \(der - 1\)]\((
\*FractionBox[\(
\*SuperscriptBox[\(k\), \(2\)] - 
\*SuperscriptBox[\(l\), \(2\)]\), \(2  l + 1\)])\)\),D[ChebyshevT[k,u],{u,der}]/.u->u0],{k,0,n-2,2}],
SameQ[p,"odd"],
Table[If[SameQ[1,u0]\[Or]SameQ[-1,u0],u0^(k+der) \!\(
\*SubsuperscriptBox[\(\[Product]\), \(l = 0\), \(der - 1\)]\((
\*FractionBox[\(
\*SuperscriptBox[\(k\), \(2\)] - 
\*SuperscriptBox[\(l\), \(2\)]\), \(2  l + 1\)])\)\),D[ChebyshevT[k,u],{u,der}]/.u->u0],{k,1,n-1,2}],
True,Table[If[SameQ[1,u0]\[Or]SameQ[-1,u0],u0^(k+der) \!\(
\*SubsuperscriptBox[\(\[Product]\), \(l = 0\), \(der - 1\)]\((
\*FractionBox[\(
\*SuperscriptBox[\(k\), \(2\)] - 
\*SuperscriptBox[\(l\), \(2\)]\), \(2  l + 1\)])\)\),D[ChebyshevT[k,u],{u,der}]/.u->u0],{k,0,n-1}]
]
]


(* create differential operator in the variable x of the form a[x]*d^n/dx^n *)
Needs["Olveretal`"];
Options[DiffOperator]={Parity->0,MaximumDerivative->None};
DiffOperator[x_,expr_,der_Integer,dermax_Integer,n_,opts:OptionsPattern[]]:=DiffOperator[x,expr,der,opts]=
Block[{multmat,diffmat,op,mat,chop=Expand@Simplify[expr//Chop],(*options*)ip,ndiff},
	ip=OptionValue[Parity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
diffmat=D\[Lambda][der,n];
	(*multmat=Dot@@Table[S\[Lambda][m,n],{m,dermax-1,der,-1}].M\[Lambda][der,n,expr,x];*)
	multmat=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,der,-1}] . M\[Lambda][der,n,expr,x];
	If[ip!=0,
		(*op=(1-2Mod[der,2])*Piecewise[{{1,SameQ[expr,expr/.x->-x]},{-1,SameQ[expr,-expr/.x->-x]}}];*)
		op=(1-2Mod[der,2])*Piecewise[{{1,SameQ[chop,chop/.x->-x]},{-1,SameQ[chop,-chop/.x->-x]}}];
(*		Print[ip,op];*)
		If[Abs[op]!=1,Print[op," ",chop]];
		Which[
			ip==1&&op==1,mat=Drop[Drop[(multmat . diffmat)\[Transpose],{2,n,2}]\[Transpose],{2,n,2}],
			ip==1&&op==-1,mat=Drop[Drop[(multmat . diffmat)\[Transpose],{2,n,2}]\[Transpose],{1,n,2}],
			ip==-1&&op==-1,mat=Drop[Drop[(multmat . diffmat)\[Transpose],{1,n,2}]\[Transpose],{2,n,2}],
			ip==-1&&op==1,mat=Drop[Drop[(multmat . diffmat)\[Transpose],{1,n,2}]\[Transpose],{1,n,2}]
		];
		Drop[mat,-Floor[dermax/2]],
		Drop[multmat . diffmat,-dermax]
	]
];


(** optimised function to build sparsearray iteratively  **)
SetAttributes[BuildSparseIterate,HoldFirst];
BuildSparseIterate[Band[{i_Integer,j_Integer}]->{SparseArray[Automatic,{nbrows_Integer,nbcols_Integer},zero_,{1,{cumulnbelem_List,listcol_List},elem_List}]},{maxrows_Integer,maxcols_Integer}]:=
SparseArray[Automatic,{maxrows,maxcols},0,{1,{ConstantArray[0,i-1]~Join~cumulnbelem~Join~ConstantArray[Last[cumulnbelem],maxrows-i-nbrows+1],listcol+j-1},elem}];


(* assemble large discretised matrix from symbolic system matrix *)
Options[MakeMatD]={UseParity->{False}};
MakeMatD[m_,x_,der_Integer,dermax_Integer,n_,opts:OptionsPattern[]]:=
Block[{size,elem,tab,row,col,entry,dim(*,BuildSparseIterate*),(*options*)parityflag,eid,oid},
parityflag=First@OptionValue[UseParity];
If[parityflag,
	(* parity flag is up *)
eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];
	dim={n/2,n/2}-{Floor[dermax/2],0};
	elem=Most@ArrayRules[m];
	size=Length[elem];
	tab=
Table[{row,col}=elem[[i,1]];entry=elem[[i,2]];
		If[MemberQ[eid,col],SetOptions[DiffOperator,Parity->1],SetOptions[DiffOperator,Parity->-1]];
		Band[{row-1,col-1}*dim+1]->{DiffOperator[x,entry,der,dermax,n]}
	,{i,1,size}];
	If[size!=0,
		Total[SparseArray[#,Dimensions[m]dim]&/@tab],
		(*Total[BuildSparseIterate[#,Dimensions[m]dim]&/@tab],*) (* old custom function doesn't work in versions > 12 *)
		SparseArray[{},Dimensions[m]dim]
	],
	(* parity flag is down *)
	SetOptions[DiffOperator,Parity->0];
	dim={n,n}-{dermax,0};
	elem=Most@ArrayRules[m];
	size=Length[elem];
	tab=Table[{row,col}=elem[[i,1]];entry=elem[[i,2]];
	Band[{row-1,col-1}*dim+1]->{DiffOperator[x,entry,der,dermax,n]},{i,1,size}];
	If[size!=0,
		Total[SparseArray[#,Dimensions[m]dim]&/@tab],
		(*Total[BuildSparseIterate[#,Dimensions[m]dim]&/@tab],*) (* old custom function doesn't work in versions > 12 *)
		SparseArray[{},Dimensions[m]dim]
	]
	]
];


(* assemble large discretised array from symbolic array b in Ax=b problem *)
Options[MakeVec]={UseParity->{False},MaximumDerivative->None};
MakeVec[{list_},x_,dermax_,n_Integer,opts:OptionsPattern[]]:=
Block[{ind,elem,length,size,entry,tab,array,dim,(*options*)parityflag,eid,oid,ndiff,op,chop},
parityflag=First@OptionValue[UseParity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
elem=Most@ArrayRules[list];
size=Length[elem];
If[parityflag,
(* parity flag is up *)
(*eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];*)
	length=n/2;dim=length-dermax/2,
	length=n;dim=length-dermax];
tab=
Table[ind=First[elem[[i,1]]];entry=elem[[i,2]];array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}] . NChebckf[entry,x,n-1];chop=Expand@Simplify[entry//Chop];
If[parityflag,op=Piecewise[{{1,SameQ[chop,chop/.x->-x]},{-1,SameQ[chop,-chop/.x->-x]}}];
Which[
op==1,array=Drop[Drop[array,{2,n,2}],-Floor[dermax/2]],
op==-1,array=Drop[Drop[array,{1,n,2}],-Floor[dermax/2]]
],
array=Drop[array,-dermax]
];
Band[(ind-1)*dim+1,Automatic]->array
,{i,1,size}];
	If[size!=0,
		SparseArray[tab,Length[list]dim],
		SparseArray[{},Length[list]dim]
	]
];


(*(* assemble large discretised array from symbolic array b in Ax=b problem *)
Options[MakeVecOld]={UseParity->{False},MaximumDerivative->None};
MakeVecOld[{list_},x_,dermax_,n_Integer,opts:OptionsPattern[]]:=
Block[{ind,elem,length,size,entry,tab,array,dim,(*options*)parityflag,eid,oid,ndiff},
parityflag=First@OptionValue[UseParity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
elem=Most@ArrayRules[list];
size=Length[elem];
If[parityflag,
(* parity flag is up *)
eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];
	length=n/2;dim=length-dermax/2,
	length=n;dim=length-dermax
];
tab=
Table[ind=First[elem[[i,1]]];entry=elem[[i,2]];
		array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}].NChebckf[entry,x,n-1];
		If[parityflag,
			If[MemberQ[eid,ind],
				array=Drop[Drop[array,{2,n,2}],-Floor[dermax/2]],
				array=Drop[Drop[array,{1,n,2}],-Floor[dermax/2]]
			],
		array=Drop[array,-dermax]
		];
		Band[(ind-1)*dim+1,Automatic]->array
	,{i,1,size}];
	If[size!=0,
		SparseArray[tab,Length[list]dim],
		SparseArray[{},Length[list]dim]
	]
];*)


ClearAll[MakeCol]
(* assemble large discretised columns *)
Options[MakeCol]={UseParity->{False},MaximumDerivative->None};
MakeCol[{mat_},x_,dermax_,n_Integer,opts:OptionsPattern[]]:=
Block[{ind1,ind2,elem,length,size,entry,tab,array,dim,(*options*)parityflag,eid,oid,ndiff,op,chop},
parityflag=First@OptionValue[UseParity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
elem=Most@ArrayRules[mat];
size=Length[elem];
If[parityflag,
(* parity flag is up *)
(*eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];*)
length=n/2;dim=length-dermax/2,
length=n;dim=length-dermax
];
tab=
Table[ind1=First[elem[[i,1]]];ind2=Last[elem[[i,1]]];entry=elem[[i,2]];
array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}] . NChebckf[entry,x,n-1];chop=Expand@Simplify[entry//Chop];If[parityflag,op=Piecewise[{{1,SameQ[chop,chop/.x->-x]},{-1,SameQ[chop,-chop/.x->-x]}}];
Which[
op==1,array=Drop[Drop[array,{2,n,2}],-Floor[dermax/2]],
op==-1,array=Drop[Drop[array,{1,n,2}],-Floor[dermax/2]]
],
		array=Drop[array,-dermax]
];
Band[{(ind1-1)*dim+1,ind2},Automatic,{1,0}]->array,{i,1,size}];
If[size!=0,
	SparseArray[tab,Dimensions[mat]{dim,1}],
	SparseArray[{},Dimensions[mat]{dim,1}]
]
];


(*(* assemble large discretised columns *)
Options[MakeColOld]={UseParity->{False},MaximumDerivative->None};
MakeColOld[{mat_},x_,dermax_,n_Integer,opts:OptionsPattern[]]:=
Block[{ind1,ind2,elem,length,size,entry,tab,array,dim,(*options*)parityflag,eid,oid,ndiff},
parityflag=First@OptionValue[UseParity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
elem=Most@ArrayRules[mat];
size=Length[elem];
If[parityflag,
(* parity flag is up *)
eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];
	length=n/2;dim=length-dermax/2,
	length=n;dim=length-dermax
];
tab=
Table[ind1=First[elem[[i,1]]];ind2=Last[elem[[i,1]]];entry=elem[[i,2]];

array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}].NChebckf[entry,x,n-1];If[parityflag,
If[MemberQ[eid,ind1],
		array=Drop[Drop[array,{2,n,2}],-Floor[dermax/2]],
		array=Drop[Drop[array,{1,n,2}],-Floor[dermax/2]]
],
		array=Drop[array,-dermax]
];
Band[{(ind1-1)*dim+1,ind2},Automatic,{1,0}]->array,{i,1,size}];
If[size!=0,
	SparseArray[tab,Dimensions[mat]{dim,1}],
	SparseArray[{},Dimensions[mat]{dim,1}]
]
];*)


(* assemble large discretised row matrix from symbolic matrix of boundary conditions *)
ClearAll[MakeMatbc]
Options[MakeMatbc]={UseParity->{False},Side->"right"};
MakeMatbc[m_,der_Integer,n_,opts:OptionsPattern[]]:=
Block[{length,size,elem,tab,row,col,entry,array,dim,u0,(* options *)side=OptionValue[Side],parityflag,eid,oid},
parityflag=First@OptionValue[UseParity];
elem=Most@ArrayRules[m];
size=Length[elem];Which[SameQ[side,"right"],u0=1,SameQ[side,"left"],u0=-1];If[parityflag,
(* parity flag is up *)
length=n/2;
eid=First@Rest@OptionValue[UseParity];
oid=Last@Rest@OptionValue[UseParity];,
length=n];
dim={1,length};
tab=
Table[{row,col}=elem[[i,1]];entry=elem[[i,2]];
(*If[parityflag,
If[MemberQ[eid,col],
array=Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,0,n-2,2}];,array=Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,1,n-1,2}];
],
array=Table[D[ChebyshevT[k,u],{u,der}]/.u->u0,{k,0,n-1}];
];*)
If[parityflag,
If[MemberQ[eid,col],
array=MyChebyshev[der,u0,n,parity->"even"],
array=MyChebyshev[der,u0,n,parity->"odd"]
];
,
array=MyChebyshev[der,u0,n]
];
Band[{row,(col-1)*length+1},Automatic,{0,1}]->entry*array
,{i,1,size}];
	If[size!=0,
	SparseArray[tab,Dimensions[m]dim],
	SparseArray[{},Dimensions[m]dim]
	]
];


InfoSprouts[]:=Grid[{Style[#,Bold]&/@{"name","type","arraydepth"}}~Join~({Names["Sprouts`*"],Head/@ToExpression@Names["Sprouts`*"],ArrayDepth/@ToExpression@Names["Sprouts`*"]}\[Transpose]),Alignment->Left]


End[];


EndPackage[];
