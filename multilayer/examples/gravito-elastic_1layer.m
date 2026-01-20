(* ::Package:: *)

Needs["TenGSHui`","../TenGSHui.m"];
FastMode=True;


(* ::Section:: *)
(*Initialisation*)


(* radial physical domain: {innerb,...,outerb} *)
domain={r,0,1};                        


Sprouts`coordinates="Spherical";


(* resolution: *)
\[ScriptM]min=0;\[ScriptM]max=\[ScriptM]min;
\[ScriptL]min=0;\[ScriptL]max=\[ScriptL]min;
n=100;


range\[ScriptL]\[ScriptM]=With[{\[ScriptL]=\[ScriptL]min},Table[{\[ScriptL],\[ScriptM]},{\[ScriptM],\[ScriptM]min,\[ScriptM]max}]];


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


Rank[\[Rho]0]^=0;(* mass density *)
MaxDegree[\[Rho]0]^=0;
\[Rho]0[][0,0][r_]:=\[Rho]c
Rank[\[Phi]0]^=0;(* gravity potential *)
MaxDegree[\[Phi]0]^=0;
Rank[p0]^=0;(* pressure *)
MaxDegree[p0]^=0;


g0\[Congruent](-1)\[Star]\[Del]\[Phi]0;(* gravity *)


ClearAll[\[Sigma]0];
\[Sigma]0\[Congruent](-1)\[Star]p0\[CircleTimes]\[DoubleStruckG]


\[Phi]0[][0,0][r_]=2/3 G \[Pi] \[Rho]c(r^2-3); (* interior solution *)


(*p0[][0,0][r_]=pc-2/3 G \[Pi] r^2 \[Rho]c^2;(* interior solution *)*)


(* ::Section:: *)
(*Problem*)


(* ::Subsection:: *)
(*list of scalar fields*)


(* list of scalar fields *)
Sprouts`scalars={{\[Delta]\[Phi],q(*,c*)(*,t*)}};
Rank[q]^=0;
MaxDegree[q]^=\[ScriptL]max;
q[][\[ScriptL]_,\[ScriptM]_][r_]:=Rad[\[ScriptL],\[ScriptM]][r]
Rank[c]^=0;
MaxDegree[c]^=\[ScriptL]max;
c[][\[ScriptL]_,\[ScriptM]_][r_]:=Con[\[ScriptL],\[ScriptM]][r]
Rank[t]^=0;
MaxDegree[t]^=\[ScriptL]max;
t[][\[ScriptL]_,\[ScriptM]_][r_]:=Tor[\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi]]^=0;
MaxDegree[\[Delta]\[Phi]]^=\[ScriptL]max;
\[Delta]\[Phi][][\[ScriptL]_,\[ScriptM]_][r_]:=\[CapitalPhi][\[ScriptL],\[ScriptM]][r]
Rank[S]^=1;
MaxDegree[S]^=\[ScriptL]max;
(*S[-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](c[][\[ScriptL],\[ScriptM]][r]/r(*-I t[][\[ScriptL],\[ScriptM]][r]*))*)
S[0][\[ScriptL]_,\[ScriptM]_][r_]:=q[][\[ScriptL],\[ScriptM]][r]/r
(*S[1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2](c[][\[ScriptL],\[ScriptM]][r]/r(*+I t[][\[ScriptL],\[ScriptM]][r]*))*)
S[\[Alpha]_][\[ScriptL]_,\[ScriptM]_][r_]:=0


(* ::Subsection:: *)
(*auxiliary fields*)


ClearAll[\[CapitalDelta]\[Sigma],\[Delta]\[Rho]]
\[CapitalDelta]\[Sigma]\[DotEqual](\[Kappa]\[Star](TDiv[S])\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]\[Star]SymmetricTraceless[\[Del]S]))
(*\[CapitalDelta]\[Sigma]\[DotEqual](\[Lambda]\[Star](\[EmptyDownTriangle]\[CenterDot]S)\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]\[Star]Overscript[\[Del]S, \[OverParenthesis]]))*)
\[Delta]\[Rho]\[DotEqual](-1)\[Star](TDiv[(\[Rho]0\[CircleTimes]S)])


(* ::Subsection:: *)
(*list of equations*)


(* list of scalar equations per layer *)
Sprouts`eq=
{
(* layer 1 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho])[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]0\[CircleTimes]S\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]])\[CirclePlus]\[Del]((\[Rho]0\[CircleTimes]S)\[CenterDot]\[Del]\[Phi]0)\[CirclePlus](\[Rho]0\[CircleTimes]\[Del]\[Delta]\[Phi])\[CirclePlus](\[Delta]\[Rho]\[CircleTimes]\[Del]\[Phi]0)),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}](*,
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]0\[CircleTimes]S\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]])\[CirclePlus]\[Del]((\[Rho]0\[CircleTimes]S)\[CenterDot]\[Del]\[Phi]0)\[CirclePlus](\[Rho]0\[CircleTimes]\[Del]\[Delta]\[Phi])\[CirclePlus](\[Delta]\[Rho]\[CircleTimes]\[Del]\[Phi]0)),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]*)(*,
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]0\[CircleTimes]S\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]])\[CirclePlus]\[Del]((\[Rho]0\[CircleTimes]S)\[CenterDot]\[Del]\[Phi]0)\[CirclePlus](\[Rho]0\[CircleTimes]\[Del]\[Delta]\[Phi])\[CirclePlus](\[Delta]\[Rho]\[CircleTimes]\[Del]\[Phi]0)),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]*)
}
};
(* differential order per equation *)
(* gives number of rows to elliminate and replace by bc/jc *)
Sprouts`\[ScriptCapitalO]d={{2,2(*,2*)(*,2*)}};
Sprouts`ndiff=2;


(*(\[Rho]0\[CircleTimes]((-\[Lambda]^2)\[Star]S\[CirclePlus]\[Del]\[Delta]\[Phi])\[CircleMinus](TDiv[\[CapitalDelta]\[Sigma]])\[CirclePlus]\[Del](\[Rho]0\[CircleTimes](S\[CenterDot]\[Del]\[Phi]0))\[CirclePlus]\[Rho]0\[CircleTimes]\[Del]\[Delta]\[Phi]\[CircleMinus]TDiv[(\[Rho]0\[CircleTimes]S)]\[CircleTimes]\[Del]\[Phi]0)*)


(* ::Subsection:: *)
(*list of boundary conditions*)


(* list of junction conditions per layer *)
Sprouts`jc=
{
};


(* ::Subsubsection:: *)
(*Free surface*)


(* ::Text:: *)
(*Vacuum solution (for gravity potential)*)


ClearAll[\[Delta]\[Phi]ext]
Rank[\[Delta]\[Phi]ext]^=0;(* increment of potential *)
MaxDegree[\[Delta]\[Phi]ext]^=\[ScriptL]max;
\[Delta]\[Phi]ext[][\[ScriptL]_,\[ScriptM]_][r_]:=Cext[\[ScriptL],\[ScriptM]]r^-(\[ScriptL]+1)


vacuum=Flatten@Table[Solve[


\!\(\*UnderscriptBox[\((\[Delta]\[Phi]\[CircleMinus]\[Delta]\[Phi]ext)\), \(\[CurlyEpsilon]\)]\)[][\[ScriptL],\[ScriptM]][1]==0,Cext[\[ScriptL],\[ScriptM]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.\[CapitalPhi][\[ScriptL]_,\[ScriptM]_][1]-> \[CapitalPhi][\[ScriptL],\[ScriptM]][r];


(* ::Text:: *)
(*conditions*)


(* list of boundary conditions per equation *)
Sprouts`rbc=
{
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]\[CircleMinus]\[Delta]\[Phi]ext)\[CirclePlus](4\[Pi] G)\[Star]\[Rho]0\[CircleTimes]S),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.vacuum,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma],\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}](*,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma],\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]*)(*,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma],\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]*)
};


(* ::Subsection:: *)
(*free parameters*)


(* value of free parameters *)
parameters={G -> 1, \[Rho]c -> 1, (*\[Lambda] \[Rule] 1*) \[Kappa] -> 1, \[Mu] -> 1(*, \[Zeta] -> 10^-3, \[Eta] -> 10^-3*)};
