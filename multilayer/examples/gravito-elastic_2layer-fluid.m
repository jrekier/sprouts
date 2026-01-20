(* ::Package:: *)

Needs["TenGSHui`","../TenGSHui.m"];
FastMode=True;


(* ::Section:: *)
(*Initialisation*)


Sprouts`coordinates="Spherical"


Rm=1;Rc=50/61;


(* radial physical domain: {innerb,...,outerb} *)
domain={r,0,Rc,Rm};                        


(* resolution: *)
\[ScriptM]min=0;\[ScriptM]max=\[ScriptM]min;
\[ScriptL]min=2;\[ScriptL]max=2;
Sprouts`n={20,20};


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
\[Rho]01[][0,0][r_]:=\[Rho]c
Rank[\[Rho]02]^=0;(* mass density *)
MaxDegree[\[Rho]02]^=0;
\[Rho]02[][0,0][r_]:=\[Rho]m
Rank[\[Phi]01]^=0;(* gravity potential *)
MaxDegree[\[Phi]01]^=0;
\[Phi]01[][0,0][r_]= -2 G \[Pi] (\[Rho]m Rm^2+(\[Rho]c-\[Rho]m)Rc^2-\[Rho]c/3 r^2); (* interior solution *)
Rank[\[Phi]02]^=0;(* gravity potential *)
MaxDegree[\[Phi]02]^=0;
\[Phi]02[][0,0][r_]= -2 G \[Pi] \[Rho]m(Rm^2-r^2/3)-(4 \[Pi] G)/3 (\[Rho]c-\[Rho]m) Rc^3/r;


(* ::Section:: *)
(*Problem*)


(* ::Subsection:: *)
(*list of scalar fields*)


(* list of scalar fields *)
Sprouts`scalars={{\[Delta]\[Phi]1,pol1},{\[Delta]\[Phi]2,q2,c2}};
(* layer 1 *)
Rank[pol1]^=0;
MaxDegree[pol1]^=\[ScriptL]max;
pol1[][\[ScriptL]_,\[ScriptM]_][r_]:=pol1f[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]1]^=0;
MaxDegree[\[Delta]\[Phi]1]^=\[ScriptL]max;
\[Delta]\[Phi]1[][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]1f[\[ScriptL],\[ScriptM]][r]
Rank[S1]^=1;
MaxDegree[S1]^=\[ScriptL]max;
S1[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](pol1[][\[ScriptL],\[ScriptM]][r]/r+pol1[][\[ScriptL],\[ScriptM]]'[r])
S1[0][\[ScriptL]_,\[ScriptM]_][r_]:=\[ScriptL](\[ScriptL]+1) pol1[][\[ScriptL],\[ScriptM]][r]/r
S1[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](pol1[][\[ScriptL],\[ScriptM]][r]/r+pol1[][\[ScriptL],\[ScriptM]]'[r])
Rank[p1]^=0;
MaxDegree[p1]^=\[ScriptL]max;
p1[][\[ScriptL]_,\[ScriptM]_][r_]:=p1f[\[ScriptL],\[ScriptM]][r]
(* layer 2 *)
Rank[q2]^=0;
MaxDegree[q2]^=\[ScriptL]max;
q2[][\[ScriptL]_,\[ScriptM]_][r_]:=q2f[\[ScriptL],\[ScriptM]][r]
Rank[c2]^=0;
MaxDegree[c2]^=\[ScriptL]max;
c2[][\[ScriptL]_,\[ScriptM]_][r_]:=c2f[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]2]^=0;
MaxDegree[\[Delta]\[Phi]2]^=\[ScriptL]max;
\[Delta]\[Phi]2[][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]2f[\[ScriptL],\[ScriptM]][r]
Rank[S2]^=1;
MaxDegree[S2]^=\[ScriptL]max;
S2[0][\[ScriptL]_,\[ScriptM]_][r_]:=q2[][\[ScriptL],\[ScriptM]][r]/r
S2[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c2[][\[ScriptL],\[ScriptM]][r]/r)
S2[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c2[][\[ScriptL],\[ScriptM]][r]/r)


(* ::Subsection:: *)
(*auxiliary fields*)


ClearAll[\[CapitalDelta]\[Sigma]1,\[Delta]\[Rho]1]
\[CapitalDelta]\[Sigma]1\[DotEqual]((-1)\[Star]p1\[CircleTimes]\[DoubleStruckG])
\[Delta]\[Rho]1\[DotEqual](-1)\[Star](TDiv[(\[Rho]01\[CircleTimes]S1)])
ClearAll[\[CapitalDelta]\[Sigma]2,\[Delta]\[Rho]2]
\[CapitalDelta]\[Sigma]2\[DotEqual](\[Kappa]m\[Star](TDiv[S2])\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]m\[Star]SymmetricTraceless[\[Del]S2]))
\[Delta]\[Rho]2\[DotEqual](-1)\[Star](TDiv[(\[Rho]02\[CircleTimes]S2)])


mom1\[DotEqual]((-\[Omega]^2)\[Star]\[Rho]01\[CircleTimes]S1\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]1])\[CirclePlus]\[Del]((\[Rho]01\[CircleTimes]S1)\[CenterDot]\[Del]\[Phi]01)\[CirclePlus](\[Rho]01\[CircleTimes]\[Del]\[Delta]\[Phi]1)\[CirclePlus](\[Delta]\[Rho]1\[CircleTimes]\[Del]\[Phi]01))
mom2\[DotEqual]((-\[Omega]^2)\[Star]\[Rho]02\[CircleTimes]S2\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]2])\[CirclePlus]\[Del]((\[Rho]02\[CircleTimes]S2)\[CenterDot]\[Del]\[Phi]02)\[CirclePlus](\[Rho]02\[CircleTimes]\[Del]\[Delta]\[Phi]2)\[CirclePlus](\[Delta]\[Rho]2\[CircleTimes]\[Del]\[Phi]02))


(* ::Subsection:: *)
(*list of equations*)


(* list of scalar equations per layer *)
Sprouts`eq=
{
(* layer 1 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]1]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]1)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[TCurl[TCurl[mom1]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 2 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]2]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]2)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom2,List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[mom2,List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};
(* differential order per equation *)
(* gives number of rows to elliminate and replace by bc/jc *)
Sprouts`\[ScriptCapitalO]d={{2,2},{2,2,2}};
Sprouts`ndiff=Max@Sprouts`\[ScriptCapitalO]d


(* ::Subsection:: *)
(*list of boundary conditions*)


rulep1=Flatten@Table[Solve[(Component[mom1,List[con],List[Sequence@@ind]][r])==0,p1f[Sequence@@ind][r]],{ind,range\[ScriptL]\[ScriptM]}]//Simplify//Chop;


(* list of junction conditions per layer *)
Sprouts`jc=
{
(* layer 1-2 *)
{
Flatten@Table[Numerator[Together[\!\(\*UnderscriptBox[\((\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2)\[CirclePlus](4\[Pi] G)\[Star](\[Rho]01\[CircleTimes]S1\[CircleMinus]\[Rho]02\[CircleTimes]S2)),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S1\[CircleMinus]S2),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.rulep1,
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};


(* ::Subsubsection:: *)
(*Free surface*)


(* ::Text:: *)
(*Vacuum solution (for gravity potential)*)


ClearAll[\[Delta]\[Phi]ext]
Rank[\[Delta]\[Phi]ext]^=0;(* increment of potential *)
MaxDegree[\[Delta]\[Phi]ext]^=\[ScriptL]max;
\[Delta]\[Phi]ext[][\[ScriptL]_,\[ScriptM]_][r_]:=Cext[\[ScriptL],\[ScriptM]]r^-(\[ScriptL]+1)+KroneckerDelta[\[ScriptL],2]r^\[ScriptL]


vacuum=Flatten@Table[Solve[\!\(\*UnderscriptBox[\((\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]ext)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][1]==0,Cext[\[ScriptL],\[ScriptM]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.\[Delta]\[Phi]2f[\[ScriptL]_,\[ScriptM]_][1]->\[Delta]\[Phi]2f[\[ScriptL],\[ScriptM]][r];


(* ::Text:: *)
(*conditions*)


(* list of boundary conditions per equation *)
Sprouts`rbc=
{
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]ext)\[CirclePlus](4\[Pi] G)\[Star]\[Rho]02\[CircleTimes]S2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.vacuum,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]2,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]2,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
};


(* ::Subsection:: *)
(*free parameters*)


(* value of free parameters *)
parameters={\[Omega] -> 1, G -> 2.21 10^6, \[Rho]c -> 0.31, \[Rho]m -> 0.14, \[Kappa]m -> 1.63 10^6, \[Mu]m -> 7.61 10^5};
