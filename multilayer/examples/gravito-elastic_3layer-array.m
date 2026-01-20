(* ::Package:: *)

Needs["TenGSHui`","../TenGSHui.m"];
FastMode=True;


(* ::Section:: *)
(*Initialisation*)


Sprouts`coordinates="Spherical"


(* radial physical domain: {innerb,...,outerb} *)
domain={r,0,1/2,3/4,1};                        


(* resolution: *)
\[ScriptM]min=0;\[ScriptM]max=\[ScriptM]min;
\[ScriptL]min=2;\[ScriptL]max=2;
Sprouts`n={40,20,10};


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


Rank[\[Rho][1]]^=0;(* mass density *)
MaxDegree[\[Rho][1]]^=0;
\[Rho][1][][0,0][r_]:=\[Rho]c1
Rank[\[Rho][2]]^=0;(* mass density *)
MaxDegree[\[Rho][2]]^=0;
\[Rho][2][][0,0][r_]:=\[Rho]c2
Rank[\[Rho][3]]^=0;(* mass density *)
MaxDegree[\[Rho][3]]^=0;
\[Rho][3][][0,0][r_]:=\[Rho]c3
Rank[\[Phi][1]]^=0;(* gravity potential *)
MaxDegree[\[Phi][1]]^=0;
\[Phi][1][][0,0][r_]= 1/24 G \[Pi] (4 (-3+4 r^2) \[Rho]c1-3 (5 \[Rho]c2+7 \[Rho]c3)); (* interior solution *)
Rank[\[Phi][2]]^=0;(* gravity potential *)
MaxDegree[\[Phi][2]]^=0;
\[Phi][2][][0,0][r_]= (G \[Pi] (-4 \[Rho]c1+(4-27 r+16 r^3) \[Rho]c2-21 r \[Rho]c3))/(24 r);
Rank[\[Phi][3]]^=0;(* gravity potential *)
MaxDegree[\[Phi][3]]^=0;
\[Phi][3][][0,0][r_]= (G \[Pi] (-8 \[Rho]c1-19 \[Rho]c2+(27-96 r+32 r^3) \[Rho]c3))/(48 r); 


(* ::Section:: *)
(*Problem*)


(* ::Subsection:: *)
(*list of scalar fields*)


(* list of scalar fields *)
(*Sprouts`scalars={{\[Delta]\[Phi]1,q1,c1,t1},{\[Delta]\[Phi]2,q2,c2,t2},{\[Delta]\[Phi]3,q3,c3,t3}};*)
Sprouts`scalars=Table[{\[Delta]\[Phi][i],q[i],c[i],t[i]},{i,1,3}]
Rank[q[i_]]^=0;
MaxDegree[q[i_]]^=\[ScriptL]max;
q[i_][][\[ScriptL]_,\[ScriptM]_][r_]:=qf[i][\[ScriptL],\[ScriptM]][r]
Rank[c[i_]]^=0;
MaxDegree[c[i_]]^=\[ScriptL]max;
c[i_][][\[ScriptL]_,\[ScriptM]_][r_]:=cf[i][\[ScriptL],\[ScriptM]][r]
Rank[t[i_]]^=0;
MaxDegree[t[i_]]^=\[ScriptL]max;
t[i_][][\[ScriptL]_,\[ScriptM]_][r_]:=tf[i][\[ScriptL],\[ScriptM]][r]
Rank[\[Delta]\[Phi][i_]]^=0;
MaxDegree[\[Delta]\[Phi][i_]]^=\[ScriptL]max;
\[Delta]\[Phi][i_][][\[ScriptL]_,\[ScriptM]_][r_]:=\[Delta]\[Phi]f[i][\[ScriptL],\[ScriptM]][r]
Rank[S[i_]]^=1;
MaxDegree[S[i_]]^=\[ScriptL]max;
S[i_][0][\[ScriptL]_,\[ScriptM]_][r_]:=q[i][][\[ScriptL],\[ScriptM]][r]/r
S[i_][-1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c[i][][\[ScriptL],\[ScriptM]][r]/r-t[i][][\[ScriptL],\[ScriptM]][r])
S[i_][1][\[ScriptL]_,\[ScriptM]_][r_]:=Sqrt[(\[ScriptL](\[ScriptL]+1))/2] (c[i][][\[ScriptL],\[ScriptM]][r]/r+t[i][][\[ScriptL],\[ScriptM]][r])


(* ::Subsection:: *)
(*auxiliary fields*)


ClearAll[\[CapitalDelta]\[Sigma],\[Delta]\[Rho]]
\[CapitalDelta]\[Sigma][i_]\[DotEqual](\[Kappa]\[Star](TDiv[S[i]])\[CircleTimes]\[DoubleStruckG])\[CirclePlus](2\[Star](\[Mu]\[Star]SymmetricTraceless[\[Del]S[i]]))
\[Delta]\[Rho][i_]\[DotEqual](-1)\[Star](TDiv[(\[Rho][i]\[CircleTimes]S[i])])


(* ::Subsection:: *)
(*list of equations*)


(*(* list of scalar equations per layer *)
Sprouts`eq=
{
(* layer 1 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]1]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]1)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]01\[CircleTimes]S1\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]1])\[CirclePlus]\[Del]((\[Rho]01\[CircleTimes]S1)\[CenterDot]\[Del]\[Phi]01)\[CirclePlus](\[Rho]01\[CircleTimes]\[Del]\[Delta]\[Phi]1)\[CirclePlus](\[Delta]\[Rho]1\[CircleTimes]\[Del]\[Phi]01)),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]01\[CircleTimes]S1\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]1])\[CirclePlus]\[Del]((\[Rho]01\[CircleTimes]S1)\[CenterDot]\[Del]\[Phi]01)\[CirclePlus](\[Rho]01\[CircleTimes]\[Del]\[Delta]\[Phi]1)\[CirclePlus](\[Delta]\[Rho]1\[CircleTimes]\[Del]\[Phi]01)),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]01\[CircleTimes]S1\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]1])\[CirclePlus]\[Del]((\[Rho]01\[CircleTimes]S1)\[CenterDot]\[Del]\[Phi]01)\[CirclePlus](\[Rho]01\[CircleTimes]\[Del]\[Delta]\[Phi]1)\[CirclePlus](\[Delta]\[Rho]1\[CircleTimes]\[Del]\[Phi]01)),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 2 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]2]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]2)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]02\[CircleTimes]S2\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]2])\[CirclePlus]\[Del]((\[Rho]02\[CircleTimes]S2)\[CenterDot]\[Del]\[Phi]02)\[CirclePlus](\[Rho]02\[CircleTimes]\[Del]\[Delta]\[Phi]2)\[CirclePlus](\[Delta]\[Rho]2\[CircleTimes]\[Del]\[Phi]02)),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]02\[CircleTimes]S2\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]2])\[CirclePlus]\[Del]((\[Rho]02\[CircleTimes]S2)\[CenterDot]\[Del]\[Phi]02)\[CirclePlus](\[Rho]02\[CircleTimes]\[Del]\[Delta]\[Phi]2)\[CirclePlus](\[Delta]\[Rho]2\[CircleTimes]\[Del]\[Phi]02)),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]02\[CircleTimes]S2\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]2])\[CirclePlus]\[Del]((\[Rho]02\[CircleTimes]S2)\[CenterDot]\[Del]\[Phi]02)\[CirclePlus](\[Rho]02\[CircleTimes]\[Del]\[Delta]\[Phi]2)\[CirclePlus](\[Delta]\[Rho]2\[CircleTimes]\[Del]\[Phi]02)),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 3 *)
{
Flatten@Table[Numerator[Together[(TLaplacian[\[Delta]\[Phi]3]\[CircleMinus](4\[Pi] G)\[Star]\[Delta]\[Rho]3)[][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]03\[CircleTimes]S3\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]3])\[CirclePlus]\[Del]((\[Rho]03\[CircleTimes]S3)\[CenterDot]\[Del]\[Phi]03)\[CirclePlus](\[Rho]03\[CircleTimes]\[Del]\[Delta]\[Phi]3)\[CirclePlus](\[Delta]\[Rho]3\[CircleTimes]\[Del]\[Phi]03)),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]03\[CircleTimes]S3\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]3])\[CirclePlus]\[Del]((\[Rho]03\[CircleTimes]S3)\[CenterDot]\[Del]\[Phi]03)\[CirclePlus](\[Rho]03\[CircleTimes]\[Del]\[Delta]\[Phi]3)\[CirclePlus](\[Delta]\[Rho]3\[CircleTimes]\[Del]\[Phi]03)),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[((-\[Lambda]^2)\[Star]\[Rho]03\[CircleTimes]S3\[CirclePlus](-1)\[Star](TDiv[\[CapitalDelta]\[Sigma]3])\[CirclePlus]\[Del]((\[Rho]03\[CircleTimes]S3)\[CenterDot]\[Del]\[Phi]03)\[CirclePlus](\[Rho]03\[CircleTimes]\[Del]\[Delta]\[Phi]3)\[CirclePlus](\[Delta]\[Rho]3\[CircleTimes]\[Del]\[Phi]03)),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};
(* differential order per equation *)
(* gives number of rows to elliminate and replace by bc/jc *)
Sprouts`\[ScriptCapitalO]d={{2,2,2,2},{2,2,2,2},{2,2,2,2}};
Sprouts`ndiff=Max@Sprouts`\[ScriptCapitalO]d*)


(* ::Subsection:: *)
(*list of boundary conditions*)


(*(* list of junction conditions per layer *)
Sprouts`jc=
{
(* layer 1-2 *)
{
Flatten@Table[Numerator[Together[
Underscript[(\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2), \[CurlyEpsilon]][][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]1\[CircleMinus]\[Delta]\[Phi]2)\[CirclePlus](4\[Pi] G)\[Star](\[Rho]01\[CircleTimes]S1\[CircleMinus]\[Rho]02\[CircleTimes]S2)),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S1\[CircleMinus]S2),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S1\[CircleMinus]S2),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S1\[CircleMinus]S2),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]1\[CircleMinus]\[CapitalDelta]\[Sigma]2),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
},
(* layer 2-3 *)
{
Flatten@Table[Numerator[Together[
Underscript[(\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]3), \[CurlyEpsilon]][][\[ScriptL],\[ScriptM]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]2\[CircleMinus]\[Delta]\[Phi]3)\[CirclePlus](4\[Pi] G)\[Star](\[Rho]02\[CircleTimes]S2\[CircleMinus]\[Rho]03\[CircleTimes]S3)),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S2\[CircleMinus]S3),List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S2\[CircleMinus]S3),List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[(S2\[CircleMinus]S3),List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]2\[CircleMinus]\[CapitalDelta]\[Sigma]3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]2\[CircleMinus]\[CapitalDelta]\[Sigma]3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[CapitalDelta]\[Sigma]2\[CircleMinus]\[CapitalDelta]\[Sigma]3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
}
};*)


(* ::Subsubsection:: *)
(*Free surface*)


(* ::Text:: *)
(*Vacuum solution (for gravity potential)*)


(*ClearAll[\[Delta]\[Phi]ext]
Rank[\[Delta]\[Phi]ext]^=0;(* increment of potential *)
MaxDegree[\[Delta]\[Phi]ext]^=\[ScriptL]max;
\[Delta]\[Phi]ext[][\[ScriptL]_,\[ScriptM]_][r_]:=Cext[\[ScriptL],\[ScriptM]]r^-(\[ScriptL]+1)*)


(*vacuum=Flatten@Table[Solve[Underscript[(\[Delta]\[Phi]3\[CircleMinus]\[Delta]\[Phi]ext), \[CurlyEpsilon]][][\[ScriptL],\[ScriptM]][1]==0,Cext[\[ScriptL],\[ScriptM]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.\[Delta]\[Phi]3f[\[ScriptL]_,\[ScriptM]_][1]->\[Delta]\[Phi]3f[\[ScriptL],\[ScriptM]][r];*)


(* ::Text:: *)
(*conditions*)


(*(* list of boundary conditions per equation *)
Sprouts`rbc=
{
Flatten@Table[Numerator[Together[Component[ProjectESD[(\[Del](\[Delta]\[Phi]3\[CircleMinus]\[Delta]\[Phi]ext)\[CirclePlus](4\[Pi] G)\[Star]\[Rho]03\[CircleTimes]S3),\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]/.vacuum,
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]3,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[rad],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]3,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[con],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}],
Flatten@Table[Numerator[Together[Component[ProjectESD[\[CapitalDelta]\[Sigma]3,\[DoubleStruckCapitalN][\[CurlyEpsilon]],\[CurlyEpsilon]],List[tor],List[\[ScriptL],\[ScriptM]]][r]]],{\[ScriptL],\[ScriptL]min,\[ScriptL]max},{\[ScriptM],Max[\[ScriptM]min,-\[ScriptL]],Min[\[ScriptM]max,\[ScriptL]]}]
};*)


(* ::Subsection:: *)
(*free parameters*)


(*(* value of free parameters *)
parameters={G -> 1, \[Rho]c1 -> 20, \[Kappa]1 -> 1, \[Mu]1 -> 1, \[Rho]c2 -> 10, \[Kappa]2 -> 1, \[Mu]2 -> 1, \[Rho]c3 -> 1, \[Kappa]3 -> 1, \[Mu]3 -> 1};*)
