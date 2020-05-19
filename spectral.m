(* ::Package:: *)

BeginPackage["spectral`"];


(* Chebyshev transforms and operations *)
NChebck::usage="NChebck[f, n] computes the n+1 first coefficients of the Chebyshev series for the pure scalar function of a single variable f";
NChebckf::usage="NChebck[f, x, n] computes the n+1 first coefficients of the Chebyshev series for scalar function f[x]";
NChebckList::usage="NChebckList[l, n, nel] computes the n+1 first coefficients of the Chebyshev series for every element of the list l of length nel each treated as a scalar function of a single variable";
NChebckMat::usage="NChebckMat[A, n, nrow, ncol] computes the n+1 first coefficients of the Chebyshev series for every element of (nrow x ncol) matrix A each treated as a scalar function of a single variable";
NChebeval::usage="f = NChebeval[c], y = f[x], evaluates Chebyshev series, x rescaled to -1 <= x <= 1 (numerical)";
Chebeval::usage="f = Chebeval[c], y = f[x], evaluates Chebyshev series, x rescaled to -1 <= x <= 1 (symbolic)";
DCheb::usage="dCheb[c, {a,b}] differentiates the Chebyshev series c scaled over the interval {a,b}";
ICheb::usage="ICheb[c, {a,b}] gives the indefinite integral a Chebyshev series that vanishes at a";
I0Cheb::usage="i0Cheb[c, {a,b}] integrates the Chebyshev series over {a,b}";
TimesCheb::usage="TimesCheb[ak, bk] computes the coefficients of the product of two Chebyshev series of coefficients ak and bk";
GegenbauerSeries::usage="GegenbauerSeries[\[Lambda], ck,trunc][x] computes the truncated series \!\(\*SubsuperscriptBox[\(\[Sum]\), \(0\), \(trunc\)]\)\!\(\*SubscriptBox[\(c\), \(k\)]\) \!\(\*SubscriptBox[\(C\), \(k\)]\)[\[Lambda], x] with \!\(\*SubscriptBox[\(C\), \(k\)]\)[\[Lambda],x], the ultraspherical polynomials of order \[Lambda] in x (The Chebyshev polynomials being a special case with \[Lambda]=0)";


D\[Lambda]::usage="D\[Lambda][\[Lambda], n] creates the (n x n) matrix representation of the \[Lambda]-order derivative in the spectral Ultraspherical representation";
S\[Lambda]::usage="S\[Lambda][\[Lambda], n] creates the (n x n) matrix operator transforming Gegenbauer coefficients of order \[Lambda] to order \[Lambda]+1";
M\[Lambda]::usage="M\[Lambda][\[Lambda], ck] creates the matrix operator representing multiplication by a function with coefficients ck in the Gegenbauer basis of order \[Lambda].
The resulting matrix has dimensions (n x n) with n the length of array ck";
M\[Lambda]ChebN::usage="M\[Lambda]ChebN[f, x, N, \[Lambda], n] creates the matrix operator representing multiplication by the scalar function f[x] in the Gegenbauer basis of order \[Lambda] projected to order N.
The resulting matrix has dimensions (n x n) with n the number of coefficients in the polynomial series";


(*M\[Lambda]old*)


Begin["`Private`"];


(* Chebyshev transforms and operations *)


NChebck[f_,n_Integer,prec_:MachinePrecision]:=
Module[{ck,chebnodes},
chebnodes=N[Cos[\[Pi] Range[0,n]/n],prec];
ck=Sqrt[2/n] FourierDCT[f/@chebnodes,1];
ck[[{1,-1}]]/=2;
Chop[N[ck,prec],10^-15]
]
NChebckf[f_,x_,n_Integer,prec_:MachinePrecision]:=
Module[{ck,chebnodes},
chebnodes=N[Cos[\[Pi] Range[0,n]/n],prec];
ck=Sqrt[2/n] FourierDCT[(f/.{x->#})&/@chebnodes,1];
ck[[{1,-1}]]/=2;
Chop[N[ck,prec],10^-15]
]
(*NChebckList[list_,n_Integer,nel_]:=
Module[{ck,chebnodes,prec=MachinePrecision},
chebnodes=N[Cos[\[Pi] Range[0,n]/n],prec];
ck=N@Table[Sqrt[2/n] FourierDCT[(list[x][[i]]/.{x->#})&/@chebnodes,1],{i,1,nel}];
Table[ck[[i,{1,-1}]]/=2,{i,1,nel}];
Chop@N[ck,prec]
]*)
NChebckList[list_,n_Integer,nel_,prec_:MachinePrecision]:=
Module[{ck,chebnodes},
chebnodes=N[Cos[\[Pi] Range[0,n]/n],prec];
ck=N@Table[
If[NumericQ[list[x][[i]]],
list[x][[i]] UnitVector[n+1,1],
Sqrt[2/n] FourierDCT[(list[x][[i]]/.{x->#})&/@chebnodes,1]]
,{i,1,nel}];
Table[
If[!NumericQ[list[x][[i]]],
ck[[i,{1,-1}]]/=2],{i,1,nel}];
N[ck,prec]
]
NChebckMat[mat_,n_Integer,nrow_Integer,ncol_Integer,prec_:MachinePrecision]:=
Module[{ck,chebnodes},
chebnodes=N[Cos[\[Pi] Range[0,n]/n],prec];
ck=N@Table[Sqrt[2/n] FourierDCT[(mat[x][[i,j]]/.{x->#})&/@chebnodes,1],{i,1,nrow},{j,1,ncol}];
Table[ck[[i,j,{1,-1}]]/=2,{i,1,nrow},{j,1,ncol}];
N[ck,prec]
]

NChebeval[c0:{__Real?MachineNumberQ}]:=With[{c1=Reverse[c0],deg=Length@c0-1},Compile[{x},Block[{c=c1,s=0.,s1=0.,s2=0.},Do[s=c[[i]]+2 x*s1-s2;
s2=s1;
s1=s,{i,deg}];
Last@c+x*s1-s2],RuntimeAttributes->{Listable}]];

Chebeval[c0_][x_]:=
With[{c1=Reverse[c0],deg=Length@c0-1},
	Block[{c=c1,s=0.,s1=0.,s2=0.},
		Do[
			(*s=c[[i]]+2 x*s1-s2;*)
			s=Simplify[c[[i]]+2 x*s1-s2];
			s2=s1;
		s1=s,{i,deg}];
	Last@c+x*s1-s2]
];

DCheb[c_]:=DCheb[c,{-1,1}];
DCheb[c_,{a_,b_}]:=Module[{c1=0,c2=0,c3},2/(b-a) MapAt[#/2&,Reverse@Table[c3=c2;c2=c1;c1=2 (n+1)*c[[n+2]]+c3,{n,Length[c]-2,0,-1}],1]];

ICheb[ck_?VectorQ]:=ICheb[ck,{-1,1}];
ICheb[ck_?VectorQ,{a_,b_}]:=
Module[{c=ck,Ck,C0,n=Length[ck]}, 
c[[1]]*=2;
Ck=Table[(c[[i-1]]-c[[i+1]])/(2(i-1)),{i,2,n-1}]~Join~{c[[n-1]]/(2(n-1))};
C0=Ck.Table[(-1)^i,{i,2,n}];
((b-a)/2)({C0}~Join~Ck)
]

I0Cheb[c_]:=I0Cheb[c,{-1,1}];
I0Cheb[c_,{a_,b_}]:=Total[(b-a)/(1-Range[0,Length@c-1,2]^2) c[[1;; ;;2]]];

TimesCheb[aa_?VectorQ,bb_?VectorQ]:=Module[{cc},cc=ConstantArray[0,Length[aa]+Length[bb]-1];
Do[cc[[1+Abs[i+j-2]]]+=aa[[i]] bb[[j]]/2;
cc[[1+Abs[i-j]]]+=aa[[i]] bb[[j]]/2,{i,Length@aa},{j,Length@bb}];
cc];

GegenbauerSeries[\[Lambda]_Integer,ck_,truncation_Integer][x_]:=
Module[{n=truncation},
If[\[Lambda]==0,
Sum[ck[[k]]ChebyshevT[k-1,x],{k,1,n}],
Sum[ck[[k]]GegenbauerC[k-1,\[Lambda],x],{k,1,n}]
]
]


(* ::Text:: *)
(*The following operators are taken from Olver, S., & Townsend, A. (2013). A fast and well-conditioned spectral method. SIAM Review, 55(3), 462\[Dash]489. https://doi.org/10.1137/120865458*)


D\[Lambda][\[Lambda]_Integer,n_Integer]:=D\[Lambda][\[Lambda],n]=
Switch[\[Lambda],0,
SparseArray[IdentityMatrix[n]],
_,
2^(\[Lambda]-1) (\[Lambda]-1)!SparseArray[{Band[{1,\[Lambda]+1}]->Table[i,{i,\[Lambda],n-1}]},{n,n}]
]

S\[Lambda][\[Lambda]_Integer,n_Integer]:=S\[Lambda][\[Lambda],n]=
Switch[\[Lambda],0,
SparseArray[{{1,1}->1,{i_,i_}->1/2,{i_,j_}/;j-i==2->-(1/2)},{n,n}],
-1,
SparseArray[IdentityMatrix[n]],
_,
SparseArray[{{1,1}->1,{i_,i_}->\[Lambda]/(i+\[Lambda]-1),{i_,j_}/;j-i==2->-(\[Lambda]/(j+\[Lambda]-1))},{n,n}]
]

cs=Compile[{{\[Lambda],_Integer},{s,_Integer},{j,_Integer},{k,_Integer}},
((j+k+\[Lambda]-2s)/(j+k+\[Lambda]-s) (\!\(
\*SubsuperscriptBox[\(\[Product]\), \(t = 0\), \(s - 1\)]
\*FractionBox[\(\[Lambda] + t\), \(1 + t\)]\))(\!\(
\*SubsuperscriptBox[\(\[Product]\), \(t = 0\), \(j - s - 1\)]
\*FractionBox[\(\[Lambda] + t\), \(1 + t\)]\))(\!\(
\*SubsuperscriptBox[\(\[Product]\), \(t = 0\), \(s - 1\)]
\*FractionBox[\(2  \[Lambda] + j + k - 2  s + t\), \(\[Lambda] + j + k - 2  s + t\)]\))(\!\(
\*SubsuperscriptBox[\(\[Product]\), \(t = 0\), \(j - s - 1\)]
\*FractionBox[\(k - s + 1 + t\), \(k - s + \[Lambda] + t\)]\)))
,RuntimeAttributes->{Listable},Parallelization->True,CompilationTarget->"C"];
M\[Lambda][\[Lambda]_Integer,n_Integer,expr_/;MatchQ[expr,Plus[_,__]],var_]:=M\[Lambda][\[Lambda],n,#,var]&/@Expand[expr]
M\[Lambda][\[Lambda]_Integer,n_Integer,Times[c_?NumericQ, expr_],var_]:=c M\[Lambda][\[Lambda],n,Expand[expr],var]
M\[Lambda][\[Lambda]_Integer,n_Integer,expr_?NumericQ,var_]:=SparseArray[Band[{1,1}]->expr,n]
M\[Lambda][\[Lambda]_Integer,n_Integer,expr_,var_]:=M\[Lambda][\[Lambda],n,Expand[expr],var]=
Module[{ck=N[Dot@@Table[S\[Lambda][l,n],{l,\[Lambda]-1,0,-1}].NChebckf[expr,var,n-1]]},
M\[Lambda][\[Lambda],ck]
];
M\[Lambda][\[Lambda]_Integer,ak:{(__Real?MachineNumberQ|__Complex?MachineNumberQ)}]:=
Module[{n=Length[ak],bw=Position[ak,_?(#!=0&)]//Flatten//Last,mat},
Switch[
\[Lambda],0,
(* simplest case *)mat=SparseArray[1/2 (ToeplitzMatrix[Table[If[i==1,2ak[[i]],ak[[i]]],{i,1,n}],Table[If[i==1,2ak[[i]],ak[[i]]],{i,1,n}]]+PadLeft[HankelMatrix[PadRight[ak[[2;;n]],n]][[1;;n-1]],{n,n}])],
_,
(* complex case is evaluated in parallel *)
DistributeDefinitions[bw,n,cs];
mat=Quiet@ParallelTable[
Block[{cs=cs[\[Lambda],Max[0,k-j],k,2Max[0,k-j]+j-k]//N,entry},
entry=0.;
Quiet@Do[
If[2s+j-k+1>bw,Break[]];
If[(1+j-k+s!=0)(*&&(-1+k-s+\[Lambda]!=0)*),
entry+=ak[[2s+j-k+1]]cs;
cs*=((k-s) (s+\[Lambda]) (j-k+s+\[Lambda]) (j+s+2 \[Lambda]))/((1+s) (1+j-k+s) (-1+k-s+\[Lambda]) (1+j+s+\[Lambda]));
];
,{s,Max[0,k-j],k}
];
{j+1,k+1}->entry
]
,{j,0,n-1},{k,Max[0,j-bw-1],Min[n-1,j+bw+1]}];
SparseArray[Flatten[mat,1],{n,n}]
]
]


(*M\[Lambda]old[\[Lambda]_Integer,ack_]:=
Module[{n=Length[ack],mat,m,cs\[Lambda],csvec,elem},
(* integer function (3.9) of Olver et al. *)
cs\[Lambda][\[Lambda],s_Integer,j_Integer,k_Integer]:=
((j+k+\[Lambda]-2s)/(j+k+\[Lambda]-s) Product[(\[Lambda]+t)/(1+t),{t,0,s-1}]Product[(\[Lambda]+t)/(1+t),{t,0,j-s-1}]Product[(2\[Lambda]+j+k-2s+t)/(\[Lambda]+j+k-2s+t),{t,0,s-1}]Product[(k-s+1+t)/(k-s+\[Lambda]+t),{t,0,j-s-1}])/.{Indeterminate->0,ComplexInfinity->0};
If[\[Lambda]==0,
(* simplest case *)
mat=SparseArray[1/2 (ToeplitzMatrix[Table[If[i==1,2ack[[i]],ack[[i]]],{i,1,n}],Table[If[i==1,2ack[[i]],ack[[i]]],{i,1,n}]]+PadLeft[HankelMatrix[PadRight[ack[[2;;n]],n]][[1;;n-1]],{n,n}])];,
(* sparse matrix *)
mat=SparseArray[{Band[{1,1}]->0},{n,n}];
m=Position[ack,_?(#!=0&)]//Flatten//Last;
Table[
elem=0;
Module[{cs,cs0},
With[{s=Max[0,k-j]},cs=cs\[Lambda][\[Lambda],s,k,2s+j-k]];
cs0=cs;
elem=0;
Quiet@Do[
elem=elem+ack[[2s+j-k+1]]cs;
cs=cs ((k-s) (s+\[Lambda]) (j-k+s+\[Lambda]) (j+s+2 \[Lambda]))/((1+s) (1+j-k+s) (-1+k-s+\[Lambda]) (1+j+s+\[Lambda]));
If[2s+j-k+1>m,Break[]]
,{s,Max[0,k-j],k}];
mat[[j+1,k+1]]=elem/.{Indeterminate->0,ComplexInfinity->0}
];
,{j,0,n-1},{k,Max[0,j-m-1],Min[n-1,j+m+1]}]
(*end if*)];
mat
]*)

M\[Lambda]ChebN[f_,x_,N_Integer,\[Lambda]_Integer,n_Integer]:=
Module[{SN\[Lambda],S\[Lambda]0,ack},
ack=NChebckf[f,x,n-1];
SN\[Lambda]=Dot@@Table[S\[Lambda][m-1,n],{m,N,\[Lambda]+1,-1}].
M\[Lambda][\[Lambda],Dot@@Table[S\[Lambda][m-1,n],{m,\[Lambda],1,-1}].ack]
]


End[];


EndPackage[];
