(* ::Package:: *)

BeginPackage["Riccati`"]
RiccatiSystem::usage="something"
Begin["`Private`"]
RiccatiSystem[aa_,bb_,cc_,dd_,ff_,gg_]:=Module[{},a[t_]:=aa;b[t_]:=bb;c[t_]:=cc;d[t_]:=dd;f[t_]:=ff;g[t_]:=gg;\[Tau][t_]:=a'[t]/a[t]+2*c[t]-4*d[t];\[Sigma][t_]:=a[t]*b[t]+c[t]*d[t]-(d[t])^2+d[t]/2*(a'[t]/a[t]-d'[t]/If[d[t]==0,1,d[t]]);Clear[\[Mu]];cdiffeq[\[Tau]_,\[Sigma]_]:={\[Mu]''[t]-\[Tau]*\[Mu]'[t]-4*\[Sigma]*\[Mu][t]==0,\[Mu][0]==0,\[Mu]'[0]==2*a[0]};\[Mu][t_]=\[Mu][t]/.DSolve[cdiffeq[\[Tau][t],\[Sigma][t]],\[Mu],t];A[t_]:=Simplify[1/Sqrt[2*\[Pi]*\[Mu][t]]];\[Alpha][t_]:=Simplify[-1/(4*a[t])*\[Mu]'[t]/\[Mu][t]-d[t]/(2*a[t])];\[Beta][t_]:=Simplify[1/\[Mu][t]*
\!\(\*SuperscriptBox[\(\[ExponentialE]\), \(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\((c[\[Tau]] - 2*d[\[Tau]])\) \[DifferentialD]\[Tau]\)]\)];\[Gamma][t_]:=Simplify[-a[t]/(\[Mu][t]*\[Mu]'[t])*E^(2*Integrate[(c[\[Tau]]-2*d[\[Tau]]),{\[Tau],0,t}])-4*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*FractionBox[\(a[\[Tau]]*\[Sigma][\[Tau]]\), 
SuperscriptBox[\((\(\[Mu]'\)[\[Tau]])\), \(2\)]]*
\*SuperscriptBox[\(E\), \(2*\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(\[Tau]\)]\((c[\[Lambda]] - 2*d[\[Lambda]])\) \[DifferentialD]\[Lambda]\)\)] \[DifferentialD]\[Tau]\)\)];\[Delta][t_]:=Simplify[1/\[Mu][t]*
\!\(\*SuperscriptBox[\(\[ExponentialE]\), \(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\((c[\[Tau]] - 2*d[\[Tau]])\) \[DifferentialD]\[Tau]\)]\)*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*SuperscriptBox[\(E\), \(-\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(\[Tau]\)]\((c[\[Lambda]] - 2*d[\[Lambda]])\) \[DifferentialD]\[Lambda]\)\)] \((\((f[\[Tau]] + 
\*FractionBox[\(d[\[Tau]]\), \(a[\[Tau]]\)]*g[\[Tau]])\) \[Mu][\[Tau]] + 
\*FractionBox[\(g[\[Tau]]\), \(2*a[\[Tau]]\)]*\(\[Mu]'\)[\[Tau]])\) \[DifferentialD]\[Tau]\)\)];\[Epsilon][t_]:=Simplify[(-2*a[t])/\[Mu]'[t]*\[Delta][t]*
\!\(\*SuperscriptBox[\(\[ExponentialE]\), \(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\((c[\[Tau]] - 2*d[\[Tau]])\) \[DifferentialD]\[Tau]\)]\)-8*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*FractionBox[\(a[\[Tau]]*\[Sigma][\[Tau]]\), 
SuperscriptBox[\((\(\[Mu]'\)[\[Tau]])\), \(2\)]]*
\*SuperscriptBox[\(E\), \(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(\[Tau]\)]\((c[\[Lambda]] - 2*d[\[Lambda]])\) \[DifferentialD]\[Lambda]\)]*\[Mu][\[Tau]]*\[Delta][\[Tau]] \[DifferentialD]\[Tau]\)\)+2*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*FractionBox[\(a[\[Tau]]\), \(\(\[Mu]'\)[\[Tau]]\)]*
\*SuperscriptBox[\(E\), \(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(\[Tau]\)]\((c[\[Lambda]] - 2*d[\[Lambda]])\) \[DifferentialD]\[Lambda]\)] \((f[\[Tau]] + 
\*FractionBox[\(d[\[Tau]]\), \(a[\[Tau]]\)]*g[\[Tau]])\) \[DifferentialD]\[Tau]\)\)];\[Kappa][t_]:=Simplify[-a[t]/(\[Mu][t]*\[Mu]'[t])*(\[Delta][t])^2-4*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*FractionBox[\(a[\[Tau]]*\[Sigma][\[Tau]]\), 
SuperscriptBox[\((\(\[Mu]'\)[\[Tau]])\), \(2\)]]*\((\[Mu][\[Tau]]*\[Delta][\[Tau]])\)^2 \[DifferentialD]\[Tau]\)\)+2*\!\(
\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(t\)]\(
\*FractionBox[\(a[\[Tau]]\), \(\(\[Mu]'\)[\[Tau]]\)]*\((\[Mu][\[Tau]]*\[Delta][\[Tau]])\)*\((f[\[Tau]] + 
\*FractionBox[\(d[\[Tau]]\), \(a[\[Tau]]\)]*g[\[Tau]])\) \[DifferentialD]\[Tau]\)\)];u[x_,t_]:=Simplify[A[t]*E^(\[Alpha][t]*x^2+\[Beta][t]*x*y+\[Gamma][t]*y^2+\[Delta][t]*x+\[Epsilon][t]*y+\[Kappa][t])];{Normal[u[x,t],ConditionalExpression],\[Alpha][t],\[Beta][t],\[Gamma][t],\[Delta][t],\[Epsilon][t],\[Kappa][t]}]
End[]
EndPackage[]



