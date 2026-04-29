(* ::Package:: *)

BeginPackage["exterior`"]

Get[FileNameJoin[{DirectoryName[$InputFileName], "utils.m"}]];

d::usage = "d[expr] computes the exterior derivative of `expr`, distributing over sums and using the product and chain rules on expressions built from `wedge` and scalar functions.";
wedge::usage = "wedge[x1, x2, ...] represents the exterior, or wedge, product. It is multilinear and has attributes `Flat` and `OneIdentity`.";
sortWedge::usage = "sortWedge[w] rewrites a wedge product into sorted order and multiplies by the corresponding signature.";
cleanWedge::usage = "cleanWedge[expr] expands wedge-product arguments, sorts each wedge factor canonically, and collects the result by wedge monomials.";

Begin["`Private`"]

With[
    {
        dHead = Symbol["exterior`d"],
        wedgeHead = Symbol["exterior`wedge"]
    },
    (* Exterior derivative. *)
    ClearAll[dHead];
    dHead[Times[x_, w:(_wedgeHead | _dHead)]] := wedgeHead[Collect[dHead[x], _dHead], w];
    dHead[x_Plus] := Map[dHead, x];
    dHead[x_?NumericQ | x_dHead] := 0;
    dHead[Power[x_, n_]] := n Power[x, n - 1] dHead[x] + Power[x, n] Log[x] dHead[n];
    dHead[h_[xs__]] /; !MemberQ[{wedgeHead, dHead, Pattern}, h] && FreeQ[{xs}, Pattern] := {xs} // RightComposition[
        Length,
        IdentityMatrix,
        Map[Apply[Derivative[##][h][xs]&]],
        Dot[#, Map[dHead, {xs}]]&,
        Identity
    ];

    (* Exterior product. *)
    ClearAll[wedgeHead];
    SetAttributes[wedgeHead, {Flat, OneIdentity}];
    wedgeHead[xs___, x_Plus, ys___] := Map[wedgeHead[xs, #, ys]&, x];
    wedgeHead[xs___, Times[n_, x:(_dHead | _wedgeHead)], ys___] := n wedgeHead[xs, x, ys];
    wedgeHead[___, 0, ___] := 0;
    wedgeHead[xs___, x_Times, ys___] := wedgeHead[xs, Expand[x], ys];
    Format[wedgeHead[xs__]] := {xs} // Map[InputForm] // Riffle[#, "/\\"]& // utils`MkString["(", ##, ")"]&;
    Format[wedgeHead[xs__], StandardForm] := Interpretation[System`Wedge[xs], wedgeHead[xs]];
    Format[wedgeHead[xs__], OutputForm] := {xs} // Map[ToString[#, OutputForm]&] // Riffle[#, " /\\ "]& // utils`MkString;
    (* Alternative notebook-style display using the generic ASCII formatter instead. *)
    (* Format[wedgeHead[xs__], StandardForm] := {xs} // Map[InputForm] // Riffle[#, "/\\"]& // utils`MkString["(", ##, ")"]&; *)
    (* Alternative terminal display with a Unicode wedge symbol instead of ASCII. *)
    (* Format[wedgeHead[xs__], OutputForm] := {xs} // Map[ToString[#, OutputForm]&] // Riffle[#, " \[Wedge] "]& // utils`MkString; *)

    (* Canonicalize a single wedge product by sorting its factors. *)
    ClearAll[sortWedge];
    sortWedge[w_wedgeHead] := Times[Signature[w], Apply[wedgeHead, Sort[w]]];

    (* Expand, canonicalize, and collect wedge expressions. *)
    ClearAll[cleanWedge];
    cleanWedge := RightComposition[
        ReplaceAll[w_wedgeHead :> Map[Expand, w]],
        ReplaceAll[
            RuleDelayed[
                w_wedgeHead,
                Times[Signature[w], Apply[wedgeHead, Sort[w]]]
            ]
        ],
        Collect[#, _wedgeHead]&,
        Identity
    ];
];


SetAttributes[
    {
        d,
        wedge,
        sortWedge,
        cleanWedge
    },
    ReadProtected
];

End[]

EndPackage[]
