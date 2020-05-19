(* ::Package:: *)

BeginPackage["fennec`"];


MyChebyshev::usage="";
DiffOperator::usage="";
MakeMatD::usage="";
MakeVec::usage="";
MakeCol::usage="";
MakeMatbc::usage="";
InfoFennec::usage="";
BuildSparseIterate::usage="";


PartitionDomain::usage="";


FennecFun::usage="";
(*AssembleMatrices::usage="";
parseDiffEq::usage="";*)


Begin["`Private`"];


(* ::Section:: *)
(*Utilities*)


(* gives information about variables in structure object "Fennec`" *)
InfoFennec[]:=Grid[{Style[#,Bold]&/@{"name","type","arraydepth"}}~Join~({Names["Fennec`*"],Head/@ToExpression@Names["Fennec`*"],ArrayDepth/@ToExpression@Names["Fennec`*"]}\[Transpose]),Alignment->Left]


(*Utilities*)
ClearAll[parseInterval,(*check indep var spec*)
validVariableQ,(*check whether an expression is a valid var*)
cullArgs(*returns arguments of vars:y'[2]\[Equal]0\[Rule]{2}*)
];

(*taken from somewhere I've lost track of*)
validVariableQ[var_]:=!NumericQ[var]&&FreeQ[var,DirectedInfinity|Indeterminate]&&(MemberQ[{Symbol,Subscript,K,C},Head[var]]||!AtomQ@Head[var]||Context[Evaluate@Head[var]]=!="System`")&&If[Head@Head[var]===Symbol,!MemberQ[Attributes[Evaluate@Head[var]],NumericFunction],validVariableQ[Head[var]]];

(*cullArgs-cull args of functions ff:{{args f1},{args f2},..}*)
(*cullArgs[{y[0]\[Equal]0,y[1]\[Equal]0,z[0]\[Equal]1},{y,z}]-->{{{0},{1}},{{0}}}*)
cullArgs[expr_,ff_]:=DeleteDuplicates/@Flatten[Last@Reap[Cases[expr,(f:Alternatives@@ff)[args__]|_Derivative[f:Alternatives@@ff][args__]:>Sow[{args},f],Infinity],ff],1];
cullArgs[ff_][expr_]:=cullArgs[expr,ff];

(*breaks down iterator {x,...} to {x,interval} and*checks that x is a valid variable*)
parseInterval[xx:{x_,a___}]:=If[!validVariableQ@x,Message[parseDiffEq::dsvar,x];
Return[$Failed],{x,{a}}];
parseInterval[x_]:=parseInterval@{x};

(* strip equations *)
SplitColumnwise[mat_,dim_]:=Module[{first=Accumulate[{1}~Join~Most@dim],last=Accumulate@dim},MapThread[mat[[All,#1;;#2]]&,{first,last}]]
AllCoefficientArrays[eq_,var__]:=Module[{bigmat,coef=CoefficientArrays[eq,Join[var]]},
If[SameQ[Length[coef],1],
coef={First@coef,SparseArray[{},{Length[First@coef],Length[Join@var]}]};
];
bigmat=SparseArray@Simplify@Last@coef;
{Most@coef,SplitColumnwise[bigmat,Length/@{var}]}]


(* ::Section:: *)
(*Call*)


FennecFun[eqns_List,yy_,xx_,nr_?EvenQ,opts:OptionsPattern[]]:=
Block[{in=parseDiffEq[eqns,yy,xx,FilterRules[opts,$parseKeys]]},
AssembleMatrices[in,nr,opts](*in*)
];


(* ::Section:: *)
(*Parsing and initialization*)


(* split computational domain and create rescaling functions *)
ClearAll[PartitionDomain]
PartitionDomain[domain_List]:=
Block[{},
(* arrange layers and check if the first one contains the origin *)
Block[{partition=Partition[Sort@Rest[domain],2,1]},
Fennec`nlayers=Length[partition];
Table[Fennec`layer[i]=partition[[i]],{i,1,Fennec`nlayers}];
]
If[SameQ[N@First[Fennec`layer[1]],0.],
Fennec`zeroInDomain=True;,
Fennec`zeroInDomain=False;
];
Echo[Table[Fennec`layer[i],{i,1,Fennec`nlayers}],"partition of the spatial domain :"];
(* rescale physical subdomains to u\[Element][0,1] or u\[Epsilon][-1,1] *)
Block[{cdom},
If[Fennec`zeroInDomain,
Fennec`rfu[1][u_]=Rescale[u,{0,1},Fennec`layer[1]];
Fennec`ufr[1][r_]=Rescale[r,Fennec`layer[1],{0,1}];,
Fennec`rfu[1][u_]=Rescale[u,{-1,1},Fennec`layer[1]];
Fennec`ufr[1][r_]=Rescale[r,Fennec`layer[1],{-1,1}];
];
Fennec`drdu[1]=Fennec`rfu[1]'[u];
Table[
Fennec`rfu[k][u_]=Rescale[u,{-1,1},Fennec`layer[k]];
	Fennec`ufr[k][r_]=Rescale[r,Fennec`layer[k],{-1,1}];
	Fennec`drdu[k]=Fennec`rfu[k]'[u]
,{k,2,Fennec`nlayers}]
];
]

$parseKeys={
(*just a way for me to remember the data structure*)
"de",(*the diff.eqns.*)
"dependentVars",(*the "X" argument*)
"independentVars",(*the "Y" argument*)
"bcs",(*boundary/initial conditions*)
"domain",(*interval of integration*)
"return",(*return expression*)
"order",(*differential orders of the DEs*)
"type" (*ODE,PDE,...-- unnecessary*)};

ClearAll[parseDiffEq];
(*SetAttributes[parseDiffEq,HoldAll];*)

Options[parseDiffEq]=Thread[$parseKeys->Automatic]~Join~Options[AssembleMatrices];
parseDiffEq::ndnl=NDSolve::ndnl;
parseDiffEq::dsvar=NDSolve::dsvar;
parseDiffEq::ndlim=NDSolve::ndlim;

(*part I:parse equation and args into parts*)
parseDiffEq[eqns_List,yy_,xx_,deOpts:OptionsPattern[]]:=Module[{x,y,endpoints,interval,conind,condep,alg,diff},x=parseInterval@xx;
If[x=!=$Failed,{x,interval}=x;(*split indep var and interval*)
y=yy/.v_[x]:>v;(*strip arguments of dep var*)
{conind,condep,alg,diff}=Internal`ProcessEquations`SeparateEquations[eqns,Flatten@{x},Flatten@{y}];
(*TBD check validity {conind,condep,alg,diff}*)
endpoints=cullArgs[condep,Flatten@{y}];
interval=Flatten[{interval,endpoints}];
If[Length@interval==0,Message[parseDiffEq::ndlim,xx];
x=$Failed,If[!VectorQ[interval,NumericQ],Message[parseDiffEq::ndnl,First@Cases[interval,x0_?(!NumericQ[#]&)],interval];
x=$Failed,interval=MinMax(*@N*)@interval (*N[] optional; use WorkingPrecision?*)]]];
parseDiffEq["de"->diff,"bcs"->(condep/.Automatic->{}),"independentVars"->Flatten@{x},"dependentVars"->Flatten@{y},"return"->yy,"domain"->interval,deOpts]/;FreeQ[x,$Failed]];

(*part II:check and process parts given as option rules*)
parseDiffEq[opts:OptionsPattern[]]:=Module[{asc,alldvars,firstordersys,foRules},(*TBD:validate option values ???*)(**set up association from options**)asc=<|Thread[$parseKeys->OptionValue@$parseKeys]|>;
(**parses indep var from eqns;NDSolve does not do this-- unnecessary**)If[asc@"independentVars"===Automatic,asc@"independentVars"=DeleteDuplicates@Cases[Flatten@{asc@"de"},_[x__Symbol]|Derivative[__][_][x__Symbol]:>x,Infinity]];
(**check type of DE-- unnecessary**)asc@"type"=Switch[Length@asc@"independentVars",0,"Algebraic"  (*unsupported*),1,"ODE",n_Integer/;n>1,"PDE"  (*unsupported*),_,$Failed];
(**parse dependend variables from equations-- unnecesary**)If[asc@"dependentVars"===Automatic,asc@"dependentVars"=Internal`ProcessEquations`FindDependentVariables[Flatten@{asc@"de"},asc@"independentVars"]];
(**store differential order-- unnecessary**)asc@"order"=Internal`ProcessEquations`DifferentialOrder@@Lookup[asc,{"de","independentVars","dependentVars"}];
asc];



(* ::Section:: *)
(*Matrix assembly*)


ClearAll[AssembleMatrices]
AssembleMatrices::ndnco=NDSolve::ndnco;
AssembleMatrices::cnobc="Some algebraic constraints do not apply at the specified boundaries.";
AssembleMatrices::nvars="The number of independent variables (here `1`) must be equal to 1.";
AssembleMatrices::coord="Please specify the set of coordinates as either 'Spherical' or 'Spheroidal'.";
AssembleMatrices::ndiff="The value of option 'maxDerivative' must be a positive integer larger or equal to the natural value infered frome the set of differential equations (`1`).";
AssembleMatrices::errpy="Error defining parity of the SH components";

Options[AssembleMatrices]={eigenvalue->Global`\[Lambda],coordinates->"Spherical",maxDerivative->Automatic,parameters->{}};
AssembleMatrices[in_,nr_?EvenQ,opts:OptionsPattern[]]:=
Block[{xx=in["independentVars"],neq=Length[in["de"]],nbc=Length[in["bcs"]],\[Lambda]\[Lambda]=OptionValue[eigenvalue],
bck(* bc kept *),bcd(* bc dropped *),
rp (*pattern for dependent variable*), Patternise
},
ClearAll["Fennec`*"];
Fennec`domain=in["domain"];
Fennec`nr=nr(* number of radial points *);
Fennec`parameters=OptionValue[parameters];
PartitionDomain[Sequence[{xx}~Join~Fennec`domain]];

Patternise[var___]:=Sequence@@(Pattern[#,_]&/@{var});
rp=Patternise[Sequence@@xx];

Catch[
(*Check[If[neq\[NotEqual]Length[eqs],Message[AssembleMatrices::ndnco,,Length[eqs]]],Throw[$Failed]];*)
Check[If[Length[xx]!=1,Message[AssembleMatrices::nvars]],Throw[$Failed]];

(* read the set of coordinates *)
Check[If[!MemberQ[{"Spherical","Spheroidal"},OptionValue[coordinates]],Message[AssembleMatrices::coord]],Throw[$Failed]];
Fennec`coordinates=OptionValue[coordinates];

(* get the maximum derivative *)
Fennec`layout=Table[in["dependentVars"],{k,1,Fennec`nlayers}];
Check[
If[IntegerQ@OptionValue[maxDerivative],
If[OptionValue[maxDerivative]>=Max[in["order"]],Fennec`ndiff=OptionValue[maxDerivative],Message[AssembleMatrices::ndiff,Max[in["order"]]]],
If[SameQ[OptionValue[maxDerivative],Automatic],Fennec`ndiff=Max[in["order"]],Message[AssembleMatrices::ndiff]]
],Throw[$Failed]
];

(* assemble list of variables *)
Fennec`listvar=Table[Table[Derivative[i][#][Sequence@@xx]&/@Fennec`layout[[k]],{i,0,Fennec`ndiff}],{k,1,Fennec`nlayers}];

(* process equations *)
Fennec`eq=Numerator@Together@Table[GatherBy[(in["de"]/.Equal[a_,b_]->a-b),Max[Internal`ProcessEquations`DifferentialOrder[#,xx,Fennec`layout[[1]]]]&],{k,1,Fennec`nlayers}];
Fennec`\[ScriptCapitalO]d=Table[Max[Internal`ProcessEquations`DifferentialOrder[#,xx,Fennec`layout[[1]]]]&/@Fennec`eq[[k]],{k,1,Fennec`nlayers}];

(* check and collect boundary conditions *)
{bck,bcd}={Part[in["bcs"],Flatten@Position[MemberQ[Fennec`domain,#]&/@Flatten[(DeleteDuplicates[cullArgs[#,in["dependentVars"]]]&/@in["bcs"]),3],True]],
Part[in["bcs"],Flatten@Position[!MemberQ[Fennec`domain,#]&/@Flatten[(DeleteDuplicates[cullArgs[#,in["dependentVars"]]]&/@in["bcs"]),3],True]]};
Check[If[!SameQ[bcd,{}],Print[bcd];Message[AssembleMatrices::cnobc]],Throw[$Failed]];

{Fennec`lbc,Fennec`rbc}={Part[in["bcs"],Flatten@Position[MemberQ[{Fennec`domain[[1]]},#]&/@Flatten[(DeleteDuplicates[cullArgs[#,in["dependentVars"]]]&/@bck),3],True]],
Part[in["bcs"],Flatten@Position[!MemberQ[{Fennec`domain[[1]]},#]&/@Flatten[(DeleteDuplicates[cullArgs[#,in["dependentVars"]]]&/@bck),3],True]]}/.Equal[a_,b_]->a-b;
Fennec`lbc={Fennec`lbc}/.f_[\[ScriptL]_,\[ScriptM]_][Fennec`domain[[1]]]->f[\[ScriptL],\[ScriptM]][Sequence@@xx];
Fennec`rbc={Fennec`rbc}/.f_[\[ScriptL]_,\[ScriptM]_][Fennec`domain[[2]]]->f[\[ScriptL],\[ScriptM]][Sequence@@xx];

(* impose regularity condition at the centre of coordinates based on parity *)
Check[
If[Fennec`zeroInDomain,
Echo["","regularity conditions will be enforced at r=0 based on indices of spherical harmonics"]
Which[
SameQ[Fennec`coordinates,"Spherical"],
(* indices of even and odd functions based on their \[ScriptL] *)
Fennec`eid=Table[(* loop layers *)
Position[Part[Fennec`listvar[[k]],1],f_[\[ScriptL]_,\[ScriptM]_][r_]/;EvenQ[\[ScriptL]]]//Flatten,{k,1,Fennec`nlayers}];
Fennec`oid=Table[(* loop layers *)
Position[Part[Fennec`listvar[[k]],1],f_[\[ScriptL]_,\[ScriptM]_][r_]/;OddQ[\[ScriptL]]]//Flatten,{k,1,Fennec`nlayers}];
,
SameQ[Fennec`coordinates,"Spheroidal"],
(* indices of even and odd functions based on their \[ScriptL] and \[ScriptM] *)
Fennec`eid=Table[(* loop layers *)
Position[Part[Fennec`listvar[[k]],1],f_[\[ScriptL]_,\[ScriptM]_][r_]/;EvenQ[\[ScriptL]+\[ScriptM]]]//Flatten,{k,1,Fennec`nlayers}];Fennec`oid=Table[(* loop layers *)
Position[Part[Fennec`listvar[[k]],1],f_[\[ScriptL]_,\[ScriptM]_][r_]/;OddQ[\[ScriptL]+\[ScriptM]]]//Flatten,{k,1,Fennec`nlayers}];
,
True,Message[AssembleMatrices::errpy];
]
];
,Throw[$Failed]];

(* check if eigenvalue problem or Ax=b *)
Fennec`\[Lambda]max=Max@(Exponent[#,\[Lambda]\[Lambda]]&/@Flatten[{Fennec`eq,Fennec`rbc}]);
If[!SameQ[Fennec`\[Lambda]max,0],
Fennec`evp=True;Echo[Plus@@Table["A"<>ToString[i] \[Lambda]\[Lambda]^ToString[i],{i,0,Fennec`\[Lambda]max}]==0,"eigenvalue problem of type : "];,
Fennec`evp=False;Echo["","linear problem of the type Ax=b"]
];

(* echo the expected size of the output matrices *)
If[Fennec`zeroInDomain,
Fennec`nColTotal=Fennec`nr*(Total[Length/@Fennec`layout]-1/2 Length[First@Fennec`layout]),Fennec`nColTotal=Fennec`nr*Total[Length/@Fennec`layout]];
Echo[ToString[Fennec`nColTotal]<>"x"<>ToString[Fennec`nColTotal],"Size of output matrices :"];

(* get symbolic matrices of equations *)
ClearAll[Fennec`coefeq,Fennec`rhseq,Fennec`coefeq\[Lambda]]
Table[
Table[
(*With[{tab=Table[Fennec`coefeq[k,i,j][\[Lambda]___][r_],{j,0,Fennec`ndiff}],leftover=Fennec`rhseq[k,i][\[Lambda]___][r_]},*)
With[{tab=Table[Fennec`coefeq[k,i,j][\[Lambda]___][rp],{j,0,Fennec`ndiff}],leftover=Fennec`rhseq[k,i][\[Lambda]___][rp]},
{leftover,tab}=AllCoefficientArrays[Fennec`eq[[k,i]]//.Fennec`parameters,Sequence@@Fennec`listvar[[k]]];
]
,{i,1,Length[Fennec`eq[[k]]]}];
(*Table[Fennec`coefeq\[Lambda][k,i,j,l][r_]=Coefficient[#,\[Lambda]\[Lambda],l]&@Fennec`coefeq[k,i,j][\[Lambda]\[Lambda]][r],{l,0,Fennec`\[Lambda]max},*)
Table[Fennec`coefeq\[Lambda][k,i,j,l][rp]=Coefficient[#,\[Lambda]\[Lambda],l]&@Fennec`coefeq[k,i,j][\[Lambda]\[Lambda]][Sequence@@xx],{l,0,Fennec`\[Lambda]max},
{j,0,Fennec`ndiff},{i,1,Length[Fennec`eq[[k]]]}];
,{k,1,Fennec`nlayers}];

(* get symbolic matrices of boundary conditions *)ClearAll[Fennec`coefrbc,Fennec`rhsrbc,Fennec`coefrbc\[Lambda],Fennec`coeflbc,Fennec`rhslbc,Fennec`coeflbc\[Lambda]];
Table[
With[{tab=Table[Fennec`coefrbc[i,j][\[Lambda]___][r_],{j,0,Fennec`ndiff}],leftover=Fennec`rhsrbc[i][\[Lambda]___][r_]},{leftover,tab}=AllCoefficientArrays[Fennec`rbc[[i]]//.Fennec`parameters,Sequence@@Fennec`listvar[[-1]]]],{i,1,Length[Fennec`rbc]}];Table[Fennec`coefrbc\[Lambda][i,j,l][r_]=Coefficient[#,\[Lambda]\[Lambda],l]&@Fennec`coefrbc[i,j][\[Lambda]\[Lambda]][r],{l,0,Fennec`\[Lambda]max},{j,0,Fennec`ndiff},{i,1,Length[Fennec`rbc]}];If[!Fennec`zeroInDomain,
Table[
With[{tab=Table[Fennec`coeflbc[i,j][\[Lambda]___][r_],{j,0,Fennec`ndiff}],leftover=Fennec`rhslbc[i][\[Lambda]___][r_]},{leftover,tab}=AllCoefficientArrays[Fennec`lbc[[i]]//.Fennec`parameters,Sequence@@Fennec`listvar[[1]]]],{i,1,Length[Fennec`lbc]}];Table[Fennec`coeflbc\[Lambda][i,j,l][r_]=Coefficient[#,\[Lambda]\[Lambda],l]&@Fennec`coeflbc[i,j][\[Lambda]\[Lambda]][r],{l,0,Fennec`\[Lambda]max},{j,0,Fennec`ndiff},{i,1,Length[Fennec`lbc]}]
];

(* assemble large discretised system without boundary conditions *)
ClearAll[Fennec`Abulk]
Table[
Fennec`Abulk[\[Lambda],layer]=
Plus@@Table[
Join@@
Table[(*! always give list of even indices first in option UseParity*)
If[Fennec`zeroInDomain&&SameQ[layer,1],
SetOptions[MakeMatD,UseParity->{True,First@Fennec`eid,First@Fennec`oid}],
SetOptions[MakeMatD,UseParity->{False}]
];
MakeMatD[(Fennec`drdu[layer])^-j Fennec`coefeq\[Lambda][layer,i,j,\[Lambda]][Fennec`rfu[layer][u]],u,j,Fennec`\[ScriptCapitalO]d[[layer,i]],Fennec`nr]
,{i,1,Length[Fennec`eq[[layer]]]}]
,{j,0,Fennec`ndiff}]
,{\[Lambda],0,Fennec`\[Lambda]max},{layer,1,Fennec`nlayers}];

(* assemble row matrices representing boundary conditions *)
ClearAll[Fennec`Arbc,Fennec`Albc]
Table[
Fennec`Arbc[l]=
Plus@@Table[
Join@@
Table[(*! always give list of even indices first in option UseParity*)
If[Fennec`zeroInDomain&&SameQ[Fennec`nlayers,1],
SetOptions[MakeMatbc,UseParity->{True,First@Fennec`eid,First@Fennec`oid}],
SetOptions[MakeMatbc,UseParity->{False}]
];
MakeMatbc[(Fennec`drdu[Fennec`nlayers])^-j Fennec`coefrbc\[Lambda][i,j,l][Fennec`rfu[Fennec`nlayers][1]],j,Fennec`nr,Side->"right"]
,{i,1,Length[Fennec`rbc]}]
,{j,0,Fennec`ndiff}]
,{l,0,Fennec`\[Lambda]max}];
(* compute left bc only if 0 is not in the domain *)
If[!Fennec`zeroInDomain,
SetOptions[MakeMatbc,UseParity->{False}];
Table[
Fennec`Albc[l]=
Plus@@Table[
Join@@Table[(*! always give list of even indices first in option UseParity*)MakeMatbc[(Fennec`drdu[1])^-j Fennec`coeflbc\[Lambda][i,j,l][Fennec`rfu[1][-1]],j,Fennec`nr,Side->"left"]
,{i,1,Length[Fennec`lbc]}]
,{j,0,Fennec`ndiff}]
,{l,0,Fennec`\[Lambda]max}];
];

(* pad block matrices to final number of columns *)
ClearAll[Fennec`AbulkPadded]
Table[
Fennec`AbulkPadded[\[Lambda],k]=(*Fennec`Abulk[\[Lambda],k]*)
Block[{pos},
pos=Total@Table[Dimensions[Fennec`Abulk[0,kk]][[2]],{kk,1,k-1}];
SparseArray[Band[{0,pos}+1]->Fennec`Abulk[\[Lambda],k],{Length[Fennec`Abulk[\[Lambda],k]],Fennec`nColTotal}]
]
,{k,1,Fennec`nlayers},{\[Lambda],0,Fennec`\[Lambda]max}];
ClearAll[Fennec`ArbcPadded,Fennec`AlbcPadded]
Table[
Fennec`ArbcPadded[\[Lambda]]=(*Fennec`Arbc[\[Lambda]]*)
Block[{pos},
pos=Total@Table[Dimensions[Fennec`Abulk[0,k]][[2]],{k,1,Fennec`nlayers-1}];
SparseArray[Band[{0,pos}+1]->Fennec`Arbc[\[Lambda]],{Length[Fennec`Arbc[\[Lambda]]],Fennec`nColTotal}]
]
,{\[Lambda],0,Fennec`\[Lambda]max}];
If[!Fennec`zeroInDomain,
Table[
Fennec`AlbcPadded[\[Lambda]]=(*Fennec`Albc[\[Lambda]]*)
SparseArray[Band[{1,1}]->Fennec`Albc[\[Lambda]],{Length[Fennec`Albc[\[Lambda]]],Fennec`nColTotal}]
,{\[Lambda],0,Fennec`\[Lambda]max}];
];

Table[
Fennec`Amat[\[Lambda]]=
If[Fennec`zeroInDomain,
(Join@@Riffle[Table[Fennec`AbulkPadded[\[Lambda],layer],{layer,1,Fennec`nlayers}],Table[Fennec`AjcPadded[\[Lambda],layer],{layer,1,Fennec`nlayers-1}]])~Join~(Fennec`ArbcPadded[\[Lambda]]),
(Fennec`AlbcPadded[\[Lambda]])~Join~(Join@@Riffle[Table[Fennec`AbulkPadded[\[Lambda],layer],{layer,1,Fennec`nlayers}],Table[Fennec`AjcPadded[\[Lambda],layer],{layer,1,Fennec`nlayers-1}]])~Join~(Fennec`ArbcPadded[\[Lambda]])
]
,{\[Lambda],0,Fennec`\[Lambda]max}];

(* assemble bulk of rhs array b if problem of type Ax=b *)
If[!Fennec`evp,
Table[
If[Fennec`zeroInDomain&&SameQ[layer,1],
	SetOptions[MakeVec,UseParity->{True,Fennec`eid,Fennec`oid}],
	SetOptions[MakeVec,UseParity->{False}]
	];
Fennec`bbulk[layer]=SparseArray[Join@@Table[
MakeVec[Fennec`rhseq[layer,i][][Fennec`rfu[layer][u]],u,Fennec`\[ScriptCapitalO]d[[layer,i]],Fennec`nr]
,{i,1,Length[Fennec`eq[[layer]]]}]];
,{layer,1,Fennec`nlayers}];
Fennec`brbc=Join@@Table[First[Fennec`rhsrbc[i][][Fennec`rfu[Fennec`nlayers][1(*Last@Fennec`layer[Fennec`nlayers]*)]]],{i,1,Length[Fennec`rbc]}];If[!Fennec`zeroInDomain,Fennec`blbc=Join@@Table[First[Fennec`rhslbc[i][][Fennec`rfu[1][-1(*First@Fennec`layer[1]*)]]],{i,1,Length[Fennec`lbc]}];
];
If[!SameQ[Fennec`nlayers,1],
Table[
Fennec`bjc[layer]=Join@@Table[SparseArray@First[(Normal[Fennec`rhsjc[layer,i,"left"][][r]]/.((#->0)&/@Flatten@Fennec`listvar))/.r->Fennec`rfu[layer][1(*Last@Fennec`layer[layer]*)]],{i,1,Length[Fennec`jc[[layer]]]}]
,{layer,1,Fennec`nlayers-1}]
];
Fennec`bvec=-SparseArray@If[Fennec`zeroInDomain,(Join@Flatten@Riffle[Table[Fennec`bbulk[layer],{layer,1,Fennec`nlayers}],Table[Fennec`bjc[layer],{layer,1,Fennec`nlayers-1}]])~Join~(Fennec`brbc),(Fennec`blbc)~Join~(Join@Flatten@Riffle[Table[Fennec`bbulk[layer],{layer,1,Fennec`nlayers}],Table[Fennec`bjc[layer],{layer,1,Fennec`nlayers-1}]])~Join~(Fennec`brbc)
];
];

If[!Fennec`evp,
{Fennec`bvec}~Join~Table[Fennec`Amat[\[Lambda]],{\[Lambda],0,Fennec`\[Lambda]max}],
Table[Fennec`Amat[\[Lambda]],{\[Lambda],0,Fennec`\[Lambda]max}]

(* catch *)
]
]
]


(* ::Section:: *)
(*Spectral discretization*)


SetDirectory[NotebookDirectory[]];
Needs["spectral`","./spectral.m"];


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
Needs["spectral`"];
Options[DiffOperator]={Parity->0,MaximumDerivative->None};
DiffOperator[x_,expr_,der_Integer,dermax_Integer,n_,opts:OptionsPattern[]]:=DiffOperator[x,expr,der,opts]=
Block[{multmat,diffmat,op,mat,chop=Expand@Simplify[expr//Chop],(*options*)ip,ndiff},
	ip=OptionValue[Parity];
ndiff=If[SameQ[OptionValue[MaximumDerivative],None],dermax,OptionValue[MaximumDerivative]];
diffmat=D\[Lambda][der,n];
	(*multmat=Dot@@Table[S\[Lambda][m,n],{m,dermax-1,der,-1}].M\[Lambda][der,n,expr,x];*)
	multmat=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,der,-1}].M\[Lambda][der,n,expr,x];
	If[ip!=0,
		(*op=(1-2Mod[der,2])*Piecewise[{{1,SameQ[expr,expr/.x->-x]},{-1,SameQ[expr,-expr/.x->-x]}}];*)
		op=(1-2Mod[der,2])*Piecewise[{{1,SameQ[chop,chop/.x->-x]},{-1,SameQ[chop,-chop/.x->-x]}}];
(*		Print[ip,op];*)
		If[Abs[op]!=1,Print[op," ",chop]];
		Which[
			ip==1&&op==1,mat=Drop[Drop[(multmat.diffmat)\[Transpose],{2,n,2}]\[Transpose],{2,n,2}],
			ip==1&&op==-1,mat=Drop[Drop[(multmat.diffmat)\[Transpose],{2,n,2}]\[Transpose],{1,n,2}],
			ip==-1&&op==-1,mat=Drop[Drop[(multmat.diffmat)\[Transpose],{1,n,2}]\[Transpose],{2,n,2}],
			ip==-1&&op==1,mat=Drop[Drop[(multmat.diffmat)\[Transpose],{1,n,2}]\[Transpose],{1,n,2}]
		];
		Drop[mat,-Floor[dermax/2]],
		Drop[multmat.diffmat,-dermax]
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
		Total[BuildSparseIterate[#,Dimensions[m]dim]&/@tab],
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
		Total[BuildSparseIterate[#,Dimensions[m]dim]&/@tab],
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
Table[ind=First[elem[[i,1]]];entry=elem[[i,2]];array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}].NChebckf[entry,x,n-1];chop=Expand@Simplify[entry//Chop];
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
array=Dot@@Table[S\[Lambda][m,n],{m,ndiff-1,0,-1}].NChebckf[entry,x,n-1];chop=Expand@Simplify[entry//Chop];If[parityflag,op=Piecewise[{{1,SameQ[chop,chop/.x->-x]},{-1,SameQ[chop,-chop/.x->-x]}}];
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


End[];


EndPackage[];
