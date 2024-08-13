(* ::Package:: *)

Get["utils.m"]

(* ::Subsubsection::Closed:: *)
(*Exterior algebra*)

ClearAll[d];
d[x_ w:(_Wedge | _d)] := Wedge[d[x] // Collect[#, _d]&, w];
(*Alternative*)
(*d[x_ w:(_Wedge | _d)] := Wedge[d[x] // Expand, w];*)
d[x_Plus] := x // Map[d];
d[x_?NumericQ | x_d] := 0;
d[Power[x_, n_]] := n Power[x, n - 1] d[x] + Power[x, n] Log[x] d[n];
d[h_[xs__]] /; !MemberQ[{Wedge, d, Pattern}, h] && FreeQ[{xs}, Pattern] := {xs} // RightComposition[
    Length,
    IdentityMatrix,
    Map[Apply[Derivative[##][h][xs]&]],
    Dot[#, {xs} // Map[d]]&,
    Identity
];

ClearAll[Wedge];
(* TODO: investigate behavior of `Wedge` inside patterns *)
SetAttributes[Wedge,{Flat, OneIdentity}];
Wedge[xs___, x_Plus, ys___] := x // Map[Wedge[xs, #, ys]&]
Wedge[xs___, n_ x:(_d | _Wedge), ys___] := n Wedge[xs, x, ys];
Wedge[___, 0, ___] := 0;
Wedge[xs___, x_Times, ys___] := Wedge[xs, x // Expand, ys];
(*Format[Wedge[d[x_]]] := Wedge["", d[x]];*)
(*Wedge[xs__] /; UnsameQ[{xs} // Sort, {xs}] := {xs} // Times[*)
(*    # // Signature,                                         *)
(*    # // Sort // Apply[Wedge]                               *)
(*]&;                                                         *)
(* Format[Wedge[xs__]] := {xs} // Map[InputForm] // Apply[MkString["(", ##, ")"]&]; *)
Format[Wedge[xs__]] := {xs} // Map[InputForm] // Riffle[#, "/\\"]& // MkString["(", ##, ")"]&;
sortWedge[w_Wedge] := w // Times[# // Signature, # // Sort]&;
cleanWedge := RightComposition[
    ReplaceAll[w_Wedge :> Map[Expand, w]],
    ReplaceAll @ RuleDelayed[
        w_Wedge,
        w // Times[# // Signature, # // Sort]&
    ],
    Collect[#, _Wedge]&,
    Identity
];
