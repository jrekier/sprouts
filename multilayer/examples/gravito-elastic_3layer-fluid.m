(* ::Package:: *)

Needs["TenGSHui`","../TenGSHui.m"];
FastMode=True;


(* ::Section:: *)
(*Initialisation*)


Sprouts`coordinates="Spherical"


Rm=1;Rc=1/2;Ri=2/5;


(* radial physical domain: {innerb,...,outerb} *)
domain={r,0,Ri,Rc,Rm};                        


(* resolution: *)
\[ScriptM]min=0;\[ScriptM]max=\[ScriptM]min;
\[ScriptL]min=2;\[ScriptL]max=2;
Sprouts`n={100,100,100};


range\[ScriptL]\[ScriptM]=With[{\[ScriptM]=\[ScriptM]min},Table[{\[ScriptL],\[ScriptM]},{\[ScriptL],\[ScriptL]min,\[ScriptL]max}]]


(* ::Subsection:: *)
(*Equilibrium configuration*)


(* ::Subsubsection:: *)
(*Spherical shape*)


$n=0;
Rank[\[CurlyEpsilon]]^=0;
MaxDegree[\[CurlyEpsilon]]^=0;
\[CurlyEpsilon][][0,0][q_]:=0


(* ::Subsubsection:: *)
(*equilibrium density*)


Rank[\[Rho]01]^=0;(* mass density *)
MaxDegree[\[Rho]01]^=0;
\[Rho]01[][0,0][r_]:=\[Rho]i
Rank[\[Rho]02]^=0;(* mass density *)
MaxDegree[\[Rho]02]^=0;
\[Rho]02[][0,0][r_]:=\[Rho]c
Rank[\[Rho]03]^=0;(* mass density *)
MaxDegree[\[Rho]03]^=0;
\[Rho]03[][0,0][r_]:=\[Rho]m
Rank[\[Phi]01]^=0;(* gravity potential *)
MaxDegree[\[Phi]01]^=0;
\[Phi]01[][0,0][r_]= 2/3 G \[Pi] (3 Ri^2 (\[Rho]c-\[Rho]i)+r^2 \[Rho]i-3 Rc^2 (\[Rho]c-\[Rho]m)-3 Rm^2 \[Rho]m); (* interior solution *)
Rank[\[Phi]02]^=0;(* gravity potential *)
MaxDegree[\[Phi]02]^=0;
\[Phi]02[][0,0][r_]= (2 G \[Pi] (r^3 \[Rho]c+2 Ri^3 (\[Rho]c-\[Rho]i)-3 r (Rc^2 (\[Rho]c-\[Rho]m)+Rm^2 \[Rho]m)))/(3 r);
Rank[\[Phi]03]^=0;(* gravity potential *)
MaxDegree[\[Phi]03]^=0;
\[Phi]03[][0,0][r_]= (2 G \[Pi] (2 Ri^3 (\[Rho]c-\[Rho]i)-2 Rc^3 (\[Rho]c-\[Rho]m)+r (r^2-3 Rm^2) \[Rho]m))/(3 r); 


(* ::Section:: *)
(*Problem*)


(* ::Subsection:: *)
(*list of scalar fields*)


(* list of scalar fields *)
Sprouts`scalars={{\[Delta]\[Phi]1,q1,c1},{\[Delta]\[Phi]2,pol2},{\[Delta]\[Phi]3,q3,c3}};
(* layer 1 *)
Rank[q1]^=0;
MaxDegree[q1]^=\[ScriptL]max;
q1[][\[ScriptL]_,\[ScriptM]_][r_]:=q1f[\[ScriptL],\[ScriptM]][r]
Rank[c1]^=0;
MaxDegree[c1]^=\[ScriptL]max;
c1[][\[ScriptL]_,\[ScriptM]_][r_]:=c1f[\[ScriptL],\[ScriptM]][r]
Rank[t1]^=0;
MaxDegree[t1]^=\[ScriptL]max;
t1[][\[ScriptL]_,\[ScriptM]_][r_]:=t1f[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]1]^=0;
MaxDegree[\[Delta]\[Phi]1]^=\[ScriptL]max;
\[Delta]\[Phi]1[][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]1f[\[ScriptL],\[ScriptM]][r]
Rank[S1]^=1;
MaxDegree[S1]^=\[ScriptL]max;
S1[0][\[ScriptL]_,\[ScriptM]_][r_]:=q1[][\[ScriptL],\[ScriptM]][r]/r
S1[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c1[][\[ScriptL],\[ScriptM]][r]/r)
S1[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c1[][\[ScriptL],\[ScriptM]][r]/r)
(* layer 2 *)
Rank[pol2]^=0;
MaxDegree[pol2]^=\[ScriptL]max;
pol2[][\[ScriptL]_,\[ScriptM]_][r_]:=pol2f[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]2]^=0;
MaxDegree[\[Delta]\[Phi]2]^=\[ScriptL]max;
\[Delta]\[Phi]2[][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]2f[\[ScriptL],\[ScriptM]][r]
Rank[S2]^=1;
MaxDegree[S2]^=\[ScriptL]max;
S2[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](pol2[][\[ScriptL],\[ScriptM]][r]/r+pol2[][\[ScriptL],\[ScriptM]]'[r])
S2[0][\[ScriptL]_,\[ScriptM]_][r_]:=\[ScriptL](\[ScriptL]+1) pol2[][\[ScriptL],\[ScriptM]][r]/r
S2[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](pol2[][\[ScriptL],\[ScriptM]][r]/r+pol2[][\[ScriptL],\[ScriptM]]'[r])
Rank[p2]^=0;
MaxDegree[p2]^=\[ScriptL]max;
p2[][\[ScriptL]_,\[ScriptM]_][r_]:=p2f[\[ScriptL],\[ScriptM]][r]
(* layer 3 *)
Rank[q3]^=0;
MaxDegree[q3]^=\[ScriptL]max;
q3[][\[ScriptL]_,\[ScriptM]_][r_]:=q3f[\[ScriptL],\[ScriptM]][r]
Rank[c3]^=0;
MaxDegree[c2]^=\[ScriptL]max;
c3[][\[ScriptL]_,\[ScriptM]_][r_]:=c3f[\[ScriptL],\[ScriptM]][r]
Rank[t3]^=0;
MaxDegree[t3]^=\[ScriptL]max;
t3[][\[ScriptL]_,\[ScriptM]_][r_]:=t3f[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]3]^=0;
MaxDegree[\[Delta]\[Phi]3]^=\[ScriptL]max;
\[Delta]\[Phi]3[][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]3f[\[ScriptL],\[ScriptM]][r]
Rank[S3]^=1;
MaxDegree[S3]^=\[ScriptL]max;
S3[0][\[ScriptL]_,\[ScriptM]_][r_]:=q3[][\[ScriptL],\[ScriptM]][r]/r
S3[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c3[][\[ScriptL],\[ScriptM]][r]/r)
S3[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c3[][\[ScriptL],\[ScriptM]][r]/r)


(* ::Subsection:: *)
(*auxiliary fields*)


ClearAll[\[CapitalDelta]\[Sigma]1,\[Delta]\[Rho]1]
\[CapitalDelta]\[Sigma]1\[DotEqual](\[Kappa]i\[Star](TDiv[S1])\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]i\[Star]SymmetricTraceless[\[Del]S1]))
\[Delta]\[Rho]1\[DotEqual](-1)\[Star](TDiv[(\[Rho]01\[CircleTimes]S1)])
ClearAll[\[CapitalDelta]\[Sigma]2,\[Delta]\[Rho]2]
\[CapitalDelta]\[Sigma]2\[DotEqual]((-1)\[Star]p2\[CircleTimes]\[DoubleStruckG])
\[Delta]\[Rho]2\[DotEqual](-1)\[Star](TDiv[(\[Rho]02\[CircleTimes]S2)])
ClearAll[\[CapitalDelta]\[Sigma]3,\[Delta]\[Rho]3]
\[CapitalDelta]\[Sigma]3\[DotEqual](\[Kappa]m\[Star](TDiv[S3])\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]m\[Star]SymmetricTraceless[\[Del]S3]))
\[Delta]\[Rho]3\[DotEqual](-1)\[Star](TDiv[(\[Rho]03\[CircleTimes]S3)])


mom1\[DotEqual]((-\[Lambda]^2)\[Star]\[Rho]01\[CircleTimes]S1\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]1])\[CirclePlus]\[Del]((\[Rho]01\[CircleTimes]S1)\[CenterDot]\[Del]\[Phi]01)\[CirclePlus](\[Rho]01\[CircleTimes]\[Del]\[Delta]\[Phi]1)\[CirclePlus](\[Delta]\[Rho]1\[CircleTimes]\[Del]\[Phi]01))
mom2\[DotEqual]((-\[Lambda]^2)\[Star]\[Rho]02\[CircleTimes]S2\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]2])\[CirclePlus]\[Del]((\[Rho]02\[CircleTimes]S2)\[CenterDot]\[Del]\[Phi]02)\[CirclePlus](\[Rho]02\[CircleTimes]\[Del]\[Delta]\[Phi]2)\[CirclePlus](\[Delta]\[Rho]2\[CircleTimes]\[Del]\[Phi]02))
mom3\[DotEqual]((-\[Lambda]^2)\[Star]\[Rho]03\[CircleTimes]S3\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]3])\[CirclePlus]\[Del]((\[Rho]03\[CircleTimes]S3)\[CenterDot]\[Del]\[Phi]03)\[CirclePlus](\[Rho]03\[CircleTimes]\[Del]\[Delta]\[Phi]3)\[CirclePlus](\[Delta]\[Rho]3\[CircleTimes]\[Del]\[Phi]03))


(* ::Subsection:: *)
(*list of equations*)


(* list of scalar equations per layer *)
Sprouts`eq=
{
(* layer 1 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]1]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]1)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom1,List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom1,List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 2 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]2]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]2)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[TCurl[TCurl[mom2]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
(*Flatten@Table[Numerator[Together[Component[TLaplacian[pol2],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]*)
},
(* layer 3 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]3]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]3)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom3,List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom3,List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};
(* differential order per equation *)
(* gives number of rows to elliminate and replace by bc/jc *)
Sprouts`\[ScriptCapitalO]d={{2,2,2},{2,2},{2,2,2}};
Sprouts`ndiff=Max@Sprouts`\[ScriptCapitalO]d


(* ::Subsection:: *)
(*list of boundary conditions*)


rulep2=Flatten@Table[Solve[(Component[mom2,List[con],List[Sequence@@ind]][r])==0,p2f[Sequence@@ind][r]],{ind,range\[ScriptL]\[ScriptM]}]//Simplify//Chop;


(* list of junction conditions per layer *)
Sprouts`jc=
{
(* layer 1-2 *)
{
Flatten@Table[Numerator[Together[\!\(\*UnderscriptBox[\((\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2)\[CirclePlus](4\[Pi] G)\[Star](\[Rho]01\[CircleTimes]S1\[CircleMinus]\[Rho]02\[CircleTimes]S2)),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S1\[CircleMinus]S2),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.rulep2,
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 2-3 *)
{
Flatten@Table[Numerator[Together[\!\(\*UnderscriptBox[\((\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]3)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]3)\[CirclePlus](4\[Pi] G)\[Star](\[Rho]02\[CircleTimes]S2\[CircleMinus]\[Rho]03\[CircleTimes]S3)),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S2\[CircleMinus]S3),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]2\[CircleMinus]\[CapitalDelta]\[Sigma]3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.rulep2,
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]2\[CircleMinus]\[CapitalDelta]\[Sigma]3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};


(* ::Subsubsection:: *)
(*Free surface*)


(* ::Text:: *)
(*Vacuum solution (for gravity potential)*)


ClearAll[\[Delta]\[Phi]ext]
Rank[\[Delta]\[Phi]ext]^=0;(* increment of potential *)
MaxDegree[\[Delta]\[Phi]ext]^=\[ScriptL]max;
\[Delta]\[Phi]ext[][\[ScriptL]_,\[ScriptM]_][r_]:=Cext[\[ScriptL],\[ScriptM]]r^-(\[ScriptL]+1)


vacuum=Flatten@Table[Solve[\!\(\*UnderscriptBox[\((\[Delta]\[Phi]3\[CircleMinus]\[Delta]\[Phi]ext)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][1]==0,Cext[\[ScriptL],\[ScriptM]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.\[Delta]\[Phi]3f[\[ScriptL]_,\[ScriptM]_][1]->\[Delta]\[Phi]3f[\[ScriptL],\[ScriptM]][r];


(* ::Text:: *)
(*conditions*)


(* list of boundary conditions per equation *)
Sprouts`rbc=
{
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]3\[CircleMinus]\[Delta]\[Phi]ext)\[CirclePlus](4\[Pi] G)\[Star]\[Rho]03\[CircleTimes]S3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.vacuum,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]3,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]3,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
};


(* ::Subsection:: *)
(*free parameters*)


(* value of free parameters *)
parameters={G -> 0.130, \[Rho]i -> 13/3, \[Kappa]i -> 7.5, \[Mu]i -> 1, \[Rho]c -> 10/3, \[Rho]m -> 1, \[Kappa]m -> 2, \[Mu]m -> 1};
