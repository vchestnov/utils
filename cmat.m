Get["utils.m"];

(* ::Subsection::Closed:: *)
(*stds*)


ClearAll @ stds;
stds::usage = "stds[gb, vars] for a Groebner basis `gb` in vars `vars` compute the standard (aka irreducible) monomials."
Options @ stds = {
    "MonomialOrder" -> DegreeLexicographic,
    Nothing
};
(* Adapted `CanonicalAndDualBases` from `MultivariateResidue.m` 1701.01040 *)
stds[gb_List, vars_List, opts:OptionsPattern[]] := stds[gb, vars, opts] = Module[{leadingexps, maxexp, basis},
    leadingexps = MonomialList[gb, vars, OptionValue["MonomialOrder"]][[All, 1]] // Map[Exponent[#, vars]&];
    maxexp = leadingexps // Flatten // Max;
    basis = leadingexps // RightComposition[
        Map[Function[exp,
            Select[
                Tuples[Range[0, maxexp], {Length[vars]}],
                Thread[Less[#, exp]]& /* Apply[Or]
            ]
        ]],
        Apply[Intersection],
        Map[vars^#& /* Apply[Times]],
        Total,
        MonomialList[#, vars, OptionValue["MonomialOrder"]]&,
        Reverse,
        Identity
    ]
];
stds[args__] := Error[MkString["Wrong arguments: ", {args} // InputForm]];



(* ::Subsection::Closed:: *)
(*cmat*)


ClearAll @ cmat;
cmat::usage = "cmat[gb, vars][fun] for a Groebner basis `gb` in vars `vars` compute the companion matrix representation of function `fun`."
cmat[gb_List, vars_List][fun_] := stds[gb, vars] // RightComposition[
    Map[fun],
    Map[PolynomialReduce[#, gb, vars]&],
    Part[#, All, 2]&,
    subjs[vars],
    CoefficientArrays[#, stds[gb, vars] // subjs[vars]]&,
    Switch[Length[#],
        2, # // Last,
        1, SparseArray[{}, # // Last // Length // {#, #}&],
        _, Error["wrong dimension in cmat"]
    ]&,
    Transpose,
    Identity
];
cmat[args__][_] := Error[MkString["Wrong arguments: ", {args} // InputForm]];


(* ::Subsection::Closed:: *)
(*dmat*)


(* matrix connection n-forms *)
ClearAll @ dmat;
dmat[xs_Plus, mat_] := xs // Map[dmat[#, mat]&];
dmat[c_ x:(_d | _Wedge), mat_] /; FreeQ[c, _d | _Wedge] := dmat[x, c mat];
HoldPattern[dmat[x_, mat1_] + dmat[x_, mat2_]] /; SameQ[Dimensions[mat1], Dimensions[mat2]] ^:= dmat[x, mat1 + mat2];
HoldPattern[c_ dmat[x_, mat_]] /; FreeQ[c, _d | _Wedge] ^:= dmat[x, c mat];
Wedge[dmat[x_, mat_]] ^:= dmat[Wedge[x], mat];
Wedge[dmat[x1_, mat1_], dmat[x2_, mat2_]] /; SameQ[Dimensions[mat1][[-1]], Dimensions[mat2][[1]]] ^:= dmat[Wedge[x1, x2], Dot[mat1, mat2]];
(* dmat /: HoldPattern[RuleDelayed[x_dmat, rhs_]] := RuleDelayed[HoldPattern[x], rhs] *)
(* dmat[x_, ___] /; !MemberQ[{d, Wedge}, x // Head] := Error[MkString["First argument ", x, " should be a differential form!"]]; *)
dmat[0, ___] := 0;
(* dmat[x_, ___] /; FreeQ[x, _d | _Wedge | _Blank | _Pattern] := Error[MkString["First argument ", x, " should be a differential form (or a pattern)!"]]; *)
(* dmat[_, mat_?(MatrixQ /* Not)] := Error[MkString["Second argument ", mat, " should be a matrix!"]]; *)
dmat[_, mat_] /; ContainsOnly[mat // Flatten, {0}] := 0;
dmat[x_Times, mat_] := dmat[x // Expand, mat];
Format[HoldPattern[dmat[x_, mat_]]] := x MatrixForm[mat];
