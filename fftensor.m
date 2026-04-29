(* ::Package:: *)

BeginPackage["fftensor`"]

Get[FileNameJoin[{DirectoryName[$InputFileName], "utils.m"}]];

blockmat::usage = "blockmat[ms] builds a block Toeplitz matrix from a rank-3 array `ms`, interpreted as the first block column.";
blockmat2::usage = "blockmat2[mss] builds a generalized block Toeplitz matrix from a rank-4 array `mss` of consecutive block columns.";
sylvester1::usage = "sylvester1[ps, np, qs, nq] returns the two block rows used to form a Sylvester-type matrix. sylvester1[ps, qs] uses the default shifts determined by the input lengths.";
todata::usage = "todata[xs] converts a sparse tensor or matrix into FiniteFlow-style coordinate data `{positions, values}`.";
todataDense::usage = "todataDense[xs] converts a tensor or matrix into dense FiniteFlow-style data with row-major positions and flattened values.";
relabel::usage = "relabel[m] replaces the nonzero entries of `m` by consecutive labels in row-major order, preserving the sparsity pattern.";
keepnz::usage = "keepnz[learn][m] keeps only the entries of `m` selected by the sparsity information stored in `learn`. Option `\"Filter\"` preprocesses the coordinate-value list.";
laurent::usage = "laurent[learn][m] expands sparse data into an additional Laurent-coefficient axis according to the exponent ranges stored in `learn`.";
sparsesol::usage = "sparsesol[learn][m] reconstructs a sparse solution matrix from learned dependent-variable relations.";
densesol::usage = "densesol[learn, needed][m] reconstructs a dense solution matrix from learned dependent-variable relations, keeping `needed` leading variables.";
sepIndep::usage = "sepIndep[indep][m] splits the last dimension of `m` into trailing independent entries and the remaining dependent entries.";
reconstruct::usage = "reconstruct[data][values] rebuilds a sparse tensor from the coordinate tensor `data` and a matching array of `values`.";
add::usage = "add[datas] merges several sparse data rule lists by common coordinates.";
dot::usage = "dot[dataLeft, dataRight] contracts two sparse data tensors along their shared dimension and returns grouped sparse product data.";
joinSys::usage = "joinSys[main, phil, phir] embeds three block matrices into one larger coupled linear system layout.";
plot::usage = "plot[topMargin, rightMargin, size][data] renders a debugging view of sparse block structure as ASCII art.";

Begin["`Private`"]

(* Block Toeplitz matrix with `ms` as the first block column. *)
ClearAll[blockmat];
blockmat[ms:(_List | _SparseArray)] /; SameQ[Dimensions[ms] // Length, 3] := ms // RightComposition[
    Length,
    Range,
    Map[ms[[;; -#]]& /* (PadLeft[#, Dimensions[ms]]&)],
    SparseArray,
    Flatten[#, {{2, 3}, {1, 4}}]&,
    Identity
];

(* Generalized block Toeplitz matrix with `mss` as consecutive block columns. *)
ClearAll[blockmat2];
blockmat2[mss:(_List | _SparseArray)] /; And[
    SameQ[Dimensions[mss] // Length, 4],
    Dimensions[mss][[;; 2]] // Apply[SameQ],
    True
] := mss // RightComposition[
    MapIndexed[#1[[;; -#2[[1]]]]& /* (PadLeft[#, Rest[Dimensions[mss]]]&)],
    SparseArray,
    Flatten[#, {{2, 3}, {1, 4}}]&,
    Identity
];


(* Sylvester-type block rows for polynomial coefficient lists. *)
ClearAll[sylvester1];
sylvester1[
    ps:(_List | _SparseArray), np_Integer,
    qs:(_List | _SparseArray), nq_Integer
] /; Length[ps] + np <= Length[qs] + nq := {
    np // RightComposition[
        Range,
        Map[PadLeft[ps, Length[ps] + # - 1]&],
        Reverse,
        PadRight,
        PadLeft[#, Dimensions[#] // utils`Add[{0, Length[qs] + nq - (Length[ps] + np)}]]&,
        PadRight[#, Dimensions[#] // utils`Add[{nq, 0}]]&,
        Identity
    ],
    nq // RightComposition[
        Range,
        Map[PadLeft[qs, Length[qs] + # - 1]&],
        PadRight,
        PadLeft[#, Dimensions[#] // utils`Add[{np, 0}]]&,
        Identity
    ]
};
sylvester1[ps:(_List | _SparseArray), qs:(_List | _SparseArray)] := sylvester1[
    ps, Length[qs] - 1,
    qs, Length[ps] - 1
];


(* Sparse tensor data in the format expected by FiniteFlow. *)
ClearAll[todata, todataDense];
todata[xs:(_List | _SparseArray)] := xs // RightComposition[
    ArrayRules,
    Most,
    SortBy[First],
    Map[Apply[List]],
    Transpose,
    If[SameQ[#, {}], {{}, {}}, #]&,
    MapAt[
        Rule[#, Length[#] // Range]& /* Thread /* (SparseArray[#, Dimensions[xs]]&),
        #,
        {1}
    ]&,
    Identity
];

todataDense[xs:(_List | _SparseArray)] := xs // RightComposition[
    {
        # // RightComposition[
            Dimensions,
            Apply[Times],
            Range,
            ArrayReshape[#, Dimensions[xs]]&,
            SparseArray,
            Identity
        ],
        Normal[Flatten[#]]
    }&,
    Identity
];


(* Relabel each nonzero entry by its row-major position among nonzeros. *)
ClearAll[relabel];
relabel[m:(_List | _SparseArray)] := m // RightComposition[
    ArrayRules,
    Part[#, ;;-2, 1]&,
    (* this should enforce row-major order *)
    Sort,
    Rule[#, Length[#] // Range]&,
    Thread,
    SparseArray[#, Dimensions[m]]&,
    Identity
];

ClearAll @ keepnz;
Options @ keepnz = {
    (* kinda a duct tape due to `FFAlgSparseMatMul` returning dense output *)
    "Filter" -> Identity,
    Nothing
};
keepnz[learn_, OptionsPattern[]][m:(_List | _SparseArray)] := m // RightComposition[
    Normal,
    MapIndexed[#2 -> #1&, #, {Length[Dimensions[#]]}]&,
    Flatten,
    OptionValue["Filter"],
    Part[#, All, 1]&,
    Extract[#, learn[[2, 2]] // Map[List]]&,
    Rule[#, Length[#] // Range]&,
    Thread,
    SparseArray[#, Dimensions[m]]&,
    Identity
];


(* Expand sparse data into a Laurent-coefficient axis. *)
ClearAll[laurent];
laurent[learn_][m:(_List | _SparseArray)] := Module[{min, max},
    {min, max} = utils`zipWith[{Min, Max}, learn];
    m // RightComposition[
        ArrayRules,
        Most,
        (* sorting just in case, shouldn't be needed *)
        SortBy[Last],
        Part[#, All, 1]&,
        {
            #,
            learn // RightComposition[
                utils`Add[-min + 1],
                Transpose,
                Map[Apply[Range]],
                Identity
            ]
        }&,
        Transpose,
        Map[Apply[Function[{x, xs}, Map[Append[x, #]&, xs]]]],
        Flatten[#, 1]&,
        Rule[#, Length[#] // Range]&,
        Thread,
        SparseArray[#, Append[Dimensions[m], Max[max - min + 1, 0]]]&,
        Identity
    ]
];


(* Reconstruct sparse or dense solution matrices from learned relations. *)
ClearAll[sparsesol, densesol];
sparsesol[learn_][m:(_List | _SparseArray)] := learn // RightComposition[
    Part[#, 1 ;; 2, 2]&,
    Thread,
    Map[Thread],
    Apply[Join],
    Rule[#, Length[#] // Range]&,
    Thread,
    SparseArray[
        #,
        {Length[learn[[1, 2]]], Dimensions[m][[-1]]}
    ]&,
    (* Remove the leading `DepVars` columns *)
    Part[#, All, Span[learn[[1, 2]] // Length // Add[1], All]]&,
    Identity
];

densesol[learn_, needed_Integer][m:(_List | _SparseArray)] := learn // RightComposition[
    Outer[List, #[[1, 2]], #[[2, 2]]]&,
    Flatten[#, 1]&,
    Rule[#, Length[#] // Range]&,
    Thread,
    SparseArray[
        #,
        {needed, Dimensions[m][[-1]]}
    ]&,
    Part[#, All, Span[needed + 1, All]]&,
    Identity
];


(* Split the trailing independent variables from the rest. *)
ClearAll[sepIndep];
sepIndep[indep_Integer] := RightComposition[
    Internal`PartitionRagged[
        #,
        {
            {Length[#]},
            {
                Dimensions[#][[-1]] - indep,
                indep
            }
        }
    ]&,
    First,
    Reverse,
    Identity
];


(* Reconstruct a sparse tensor from stored coordinates and new values. *)
ClearAll[reconstruct];
reconstruct[data_] := RightComposition[
    Rule[
        data // RightComposition[
            ArrayRules,
            Most,
            SortBy[Last],
            Part[#, All, 1]&,
            Identity
        ],
        #
    ]&,
    Thread,
    SparseArray[#, Dimensions[data]]&,
    Identity
];


(* Group sparse data from multiple tensors by common coordinates. *)
ClearAll[add];
add[datas_List] := datas // RightComposition[
    Transpose[#, RotateRight[Range[Length[Dimensions[#]]]]]&,
    ArrayRules,
    Most,
    Map[#[[1, ;; -2]] -> {#[[1, -1]], #[[2]]}&],
    GatherBy[#, First]&,
    Map[#[[1, 1]] -> #[[All, 2]]&],
    SortBy[First],
    Identity
];


(* Contract two sparse data tensors along one matching dimension. *)
ClearAll[dot];
dot[dataLeft_SparseArray, dataRight_SparseArray] /; SameQ[
    Dimensions[dataLeft][[-1]],
    Dimensions[dataRight][[1]]
] := {dataLeft, dataRight} // RightComposition[
    Map[ArrayRules /* Most],
    MapIndexed[Function[{list, index}, MapAt[{index[[1]], #}&, list, {All, 2}]], #]&,
    MapAt[GatherBy[#, Part[#, 1, -1]&]&, #, 1]&,
    MapAt[GatherBy[#, Part[#, 1, 1]&]&, #, 2]&,
    MapAt[Prepend[#[[;; -2]], #[[-1]]]&, #, {1, All, All, 1}]&,
    Apply[Join],
    GatherBy[#, Part[#, 1, 1, 1]&]&,
    Cases[x_ /; Length[x] === 2],
    Map[Apply[Outer[
        Rule[
            Join[#1[[1, 2 ;;]], #2[[1, 2 ;;]]],
            Join[#1[[2]], #2[[2]]]
        ]&,
        ##]&
    ]],
    Flatten,
    GatherBy[#, First]&,
    Map[#[[1, 1]] -> #[[All, 2]]&],
    SortBy[First],
    Map[MapAt[Sort, #, 2]&],
    Identity
];


(* Embed a main block system together with left and right couplings. *)
ClearAll[joinSys];
joinSys[main_, phil_, phir_] := Module[{dimm, diml, dimr},
    dimm = Dimensions[main];
    diml = Dimensions[phil][[-1]];
    dimr = Dimensions[phir][[1]];
    {
        main // RightComposition[
            PadRight[#, Dimensions[#] // utils`Add[{0, diml}]]&,
            PadLeft[#, Dimensions[#] // utils`Add[{dimr, dimr}]]&,
            Identity
        ],
        PadLeft[phil, Dimensions[phil] + {dimr, dimm[[2]] + dimr}],
        phir // RightComposition[
            PadLeft[#, Dimensions[#] // utils`Add[{0, dimr}]]&,
            PadRight[#, Dimensions[#] // utils`Add[{dimm[[1]], diml}]]&,
            Identity
        ]
    }
];


(* Temporary ASCII visualization helper for debugging sparse layouts. *)
ClearAll[plot];
plot[topMargin_Integer, rightMargin_Integer, size_Integer][data_] := Internal`PartitionRagged[
    data,
    {
        Flatten[{
            topMargin,
            ConstantArray[
                Quotient[Dimensions[data][[1]] - topMargin, size],
                size
            ],
            {}
        }],
        Flatten[{
            topMargin,
            ConstantArray[
                Quotient[Dimensions[data][[-1]] - topMargin - rightMargin, size],
                size
            ],
            rightMargin,
            {}
        }]
    }
] // utils`msS1;


SetAttributes[
    {
        blockmat,
        blockmat2,
        sylvester1,
        todata,
        todataDense,
        relabel,
        keepnz,
        laurent,
        sparsesol,
        densesol,
        sepIndep,
        reconstruct,
        add,
        dot,
        joinSys,
        plot
    },
    ReadProtected
];

End[]

EndPackage[]
