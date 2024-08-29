(* ::Subsubsection::Closed:: *)
(*tools for companion matrices*)

getLC[poly_] := Coefficient[poly, z, Exponent[poly, z]];

ClearAll[stdjs, cycles, cmats, cmatdz];
stdjs[poly_] := stdjs[poly] = poly // Exponent[#, z]& // Range[0, # - 1]& // Map[j];
(* `m`-cycles of the list `x`. Try
 *  Alphabet[] // cycles[5]
 *)
cycles[m_Integer][x:(_List | _SparseArray)] := Range[0, m - 1] // RightComposition[
    Map[RotateLeft[x, #]&],
    Transpose,
    Part[#, ;;Length[x] - m + 1]&,
    Identity
];
cmats[poly_] := cmats[poly] = poly // RightComposition[
    Exponent[#, z]&,
    z^Range[0, 2 # - 2]&,
    Map[FQuolyMod[#, poly, z]&],
    subjs[z],
    CoefficientArrays[#, stdjs[poly]]&,
    Last,
    cycles[# // Dimensions // Last][#]&,
    Transpose[#, {1, 3, 2}]&,
    Identity
];
cmatdz[poly_] := cmatdz[poly] = poly // RightComposition[
    stdjs,
    ReplaceAll[j[n_] :> z^n],
    D[#, z]&,
    subjs[z],
    CoefficientArrays[#, stdjs[poly]]&,
    Last,
    (* edge case for linear `poly` *)
    If[# // Dimensions // Length // # < 2&, {#} // SparseArray, #]&,
    Transpose,
    Identity
];

(* ::Subsubsection::Closed:: *)
(*block Toeplitz matrices*)

(* Block Toeplitz matrix with `ms` as the first block column *)
blockmat[ms:(_List | _SparseArray)] /; SameQ[ms // Dimensions // Length, 3] := ms // RightComposition[
    Length,
    Range,
    Map[ms[[;;-#]]& /* (PadLeft[#, ms // Dimensions]&)],
    SparseArray,
    Flatten[#, {{2, 3}, {1, 4}}]&,
    (* ArrayRules, *)
    (* Most, *)
    Identity
];

(* Generalized block Toeplitz matrix with `mss` as consecutive block columns *)
blockmat2[mss:(_List | _SparseArray)] /; And[
    SameQ[mss // Dimensions // Length, 4],
    mss // Dimensions // Part[#, ;;2]& // Apply[SameQ],
    True
] := mss // RightComposition[
    MapIndexed[#1[[;;-#2[[1]]]]& /* (PadLeft[#, mss // Dimensions // Rest]&)],
    SparseArray,
    Flatten[#, {{2, 3}, {1, 4}}]&,
    (* ArrayRules, *)
    (* Most, *)
    Identity
];

(* ::Subsubsection::Closed:: *)
(*Sylvester matrix*)


ClearAll[sylvester1, sylvester0];
sylvester1[
    ps:(_List | _SparseArray), np_Integer,
    qs:(_List | _SparseArray), nq_Integer
] /; Length[ps] + np <= Length[qs] + nq:= List[
    np // RightComposition[
        Range,
        Map[PadLeft[ps, Length[ps] + # - 1]&],
        Reverse,
        PadRight,
        (* PadRight[#, #[[1]] // Length // {#, #}&]&, *)
        PadLeft[#, # // Dimensions // Add[{0, Length[qs] + nq - (Length[ps] + np)}]]&,
        PadRight[#, # // Dimensions // Add[{nq, 0}]]&,
        (* MatrixForm, *)
        Identity
    ],
    nq // RightComposition[
        Range,
        Map[PadLeft[qs, Length[qs] + # - 1]&],
        PadRight,
        (* PadLeft[#, #[[1]] // Length // {#, #}&]&, *)
        PadLeft[#, # // Dimensions // Add[{np, 0}]]&,
        (* MatrixForm, *)
        Identity
    ],
    Nothing
];
sylvester1[ps:(_List | _SparseArray), qs:(_List | _SparseArray)] := sylvester1[
    ps, Length[qs] - 1,
    qs, Length[ps] - 1
]
(* FIXME old version, remove *)
sylvester0[ps:(_List | _SparseArray), qs:(_List | _SparseArray)] := List[
    qs // RightComposition[
        Length,
        Add[-1],
        Range,
        Map[PadLeft[ps, Length[ps] + # - 1]&],
        (* PadRight, *)
        Reverse,
        PadRight[#, #[[1]] // Length // {#, #}&]&,
        (* PadLeft[#, # // Dimensions // Add[{0, Length[qs] - 1}]]&, *)
        (* MatrixForm, *)
        Identity
    ],
    ps // RightComposition[
        Length,
        Add[-1],
        Range,
        Map[PadLeft[qs, Length[qs] + # - 1]&],
        PadRight,
        PadLeft[#, #[[1]] // Length // {#, #}&]&,
        (* PadLeft[#, # // Dimensions // Add[{0, Length[qs] - 1}]]&, *)
        (* (1* MatrixForm, *1) *)
        Identity
    ],
    Nothing
    (* (1* qs // RightComposition[ *1) *)
    (* (1*     Length, *1) *)
    (* (1*     Add[-1], *1) *)
    (*     Range, *)
    (*     DiagonalMatrix, *)
    (*     (1* PadRight[#, # // Dimensions // Add[Length[ps] + Length[qs] - 2 // {#, *1) *)
    (*     (1* #}&] // Add[{-Length[qs] + 1, 0}]]&, *1) *)
    (*     (1* MatrixForm, *1) *)
    (*     Identity *)
    (* ] *)
];

SameQ[
    sylvester1[Range[8], 4, Alphabet[][[;;5]], 7],
    sylvester0[Range[8], Alphabet[][[;;5]]]
]

SameQ[
    sylvester1[Range[8], Alphabet[][[;;5]]],
    sylvester0[Range[8], Alphabet[][[;;5]]]
]

(* ::Subsubsection::Closed:: *)
(*tensor `data` for `FiniteFlow`*)

todata[xs:(_List | _SparseArray)] := xs // RightComposition[
    ArrayRules,
    Most,
    SortBy[First],
    Map[Apply[List]],
    Transpose,
    (* edge case for empty `data` *)
    If[SameQ[#, {}], {{}, {}}, #]&,
    MapAt[
        Rule[#, # // Length // Range]& /* Thread /* (SparseArray[#, xs // Dimensions]&),
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
            ArrayReshape[#, xs // Dimensions]&,
            SparseArray,
            Identity
        ],
        # // Flatten // Normal,
        Nothing
    }&,
    Identity
];

ClearAll @ relabel;
relabel[m:(_List | _SparseArray)] := m // RightComposition[
    ArrayRules,
    Part[#, ;;-2, 1]&,
    (* this should enforce row-major order *)
    Sort,
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[#, m // Dimensions]&,
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
    MapIndexed[#2 -> #1&, #, # // Dimensions // Length // List]&,
    Flatten,
    OptionValue["Filter"],
    Part[#, All, 1]&,
    Extract[#, learn[[2, 2]] // Map[List]]&,
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[#, m // Dimensions]&,
    Identity
];

(* ClearAll @ keepnz1 *)
(* Options @ keepnz1 = { *)
(*     (1* kinda a duct tape due to `FFAlgSparseMatMul` returning dense output *1) *)
(*     "Filter" -> Identity, *)
(*     Nothing *)
(* }; *)
(* keepnz1[learn_, OptionsPattern[]][m:(_List | _SparseArray)] := m // RightComposition[ *)
(*     Normal, *)
(*     MapIndexed[#2 -> #1&, #, # // Dimensions // Length // List]&, *)
(*     Flatten, *)
(*     OptionValue["Filter"], *)
(*     SortBy[#, Last]&, *)
(*     (1* Part[#, All, 1]&, *1) *)
(*     Extract[#, learn[[2, 2]] // Map[List]]&, *)
(*     (1* Rule[#, # // Length // Range]&, *1) *)
(*     (1* Thread, *1) *)
(*     (1* SparseArray[#, m // Dimensions]&, *1) *)
(*     Identity *)
(* ]; *)

(* TODO avoid `Module` here? *)
ClearAll @ laurent;
laurent[learn_][m:(_List | _SparseArray)] := Module[{min, max},
    {min, max} = zipWith[{Min, Max}, learn];
    m // RightComposition[
        ArrayRules,
        Most,
        (* sorting just in case, shouldn't be needed *)
        SortBy[Last],
        Part[#, All, 1]&,
        {
            #,
            learn // RightComposition[
                Add[-min + 1],
                Transpose,
                Map[Apply[Range]],
                Identity
            ],
            Nothing
        }&,
        Transpose,
        Map[Apply[Function[{x, xs}, xs // Map[Append[x, #]&]]]],
        Flatten[#, 1]&,
        (* Extract[#, learn[[2, 2]] // Map[List]]&, *)
        Rule[#, # // Length // Range]&,
        Thread,
        SparseArray[#, Append[m // Dimensions, Max[max - min + 1, 0]]]&,
        Identity
    ]
];

ClearAll @ sparsesol;
sparsesol[learn_][m:(_List | _SparseArray)] := learn // RightComposition[
    Part[#, 1;;2, 2]&,
    Thread,
    Map[Thread],
    Apply[Join],
    (* this works not as expected when the 2nd arg is a tensor, see
     * Inner[f, {2, 1}, {{1}, {1}}, g]
     *)
    (* Inner[List /* Thread, #[[1, 2]], #[[2, 2]], Join]&, *)
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[
        #,
        {learn[[1, 2]] // Length, m // Dimensions // Last}
    ]&,
    (* Remove the leading `DepVars` columns *)
    Part[#, All, Span[learn[[1, 2]] // Length // Add[1], All]]&,
    Identity
];

ClearAll @ densesol;
densesol[learn_, needed_Integer][m:(_List | _SparseArray)] := learn // RightComposition[
    Outer[List, #[[1, 2]], #[[2, 2]]]&,
    Flatten[#, 1]&,
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[
        #,
        {needed, m // Dimensions // Last}
    ]&,
    (* Remove the leading `DepVars` columns *)
    Part[#, All, Span[needed + 1, All]]&,
    Identity
];

ClearAll @ sepIndep;
sepIndep[indep_Integer] := RightComposition[
    Internal`PartitionRagged[
        #,
        {
            {# // Length},
            {
                # // Dimensions // Last // Add[-indep],
                indep
            }
        }
    ]&,
    First,
    Reverse,
    Identity
];

ClearAll @ reconstruct;
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
    SparseArray[#, data // Dimensions]&,
    Identity
];

ClearAll @ add;
add[datas_List] := datas // RightComposition[
    Transpose[#, # // Dimensions // Length // Range // RotateRight]&,
    ArrayRules,
    Most,
    Map[#[[1, ;;-2]] -> {#[[1, -1]], #[[2]]}&],
    GatherBy[#, First]&,
    Map[#[[1, 1]] -> #[[All, 2]]&],
    SortBy[First],
    Identity
];

(* FIXME edge case when both datas are vectors *)
ClearAll @ dot;
Condition[
    dot[dataLeft_SparseArray, dataRight_SparseArray],
    And[
        SameQ[
            dataLeft  // Dimensions // Last,
            dataRight // Dimensions // First
        ],
        True
    ]
] := {dataLeft, dataRight} // RightComposition[
    Map[ArrayRules /* Most],
    MapIndexed[Function[{list, index}, MapAt[{index[[1]], #}&, list, {All, 2}]], #]&,
    MapAt[GatherBy[#, Part[#, 1, -1]&]&, #, 1]&,
    MapAt[GatherBy[#, Part[#, 1,  1]&]&, #, 2]&,
    (* move the contracted index to the leftmost position in `dataLeft` *)
    MapAt[Prepend[#[[;;-2]], #[[-1]]]&, #, {1, All, All, 1}]&,
    Apply[Join],
    (* first we do the multiplication *)
    (* group by the contracted index value *)
    GatherBy[#, Part[#, 1, 1, 1]&]&,
    (* only these groups correspond to non-zero contractions *)
    Cases[x_ /; Length[x] === 2],
    Map[Apply[Outer[Rule[
        Join[#1[[1, 2;;]], #2[[1, 2;;]]]
    ,
        Join[#1[[2]], #2[[2]]]
    ]&, ##]&]],
    Flatten,
    (* now we do the addition *)
    GatherBy[#, First]&,
    Map[Rule[
        #[[1, 1]]
    ,
        #[[All, 2]]
    ]&],
    SortBy[First],
    Map[MapAt[Sort, #, 2]&],
    Identity
];

ClearAll @ joinSys;
joinSys[main_, phil_, phir_] := Module[{dimm, diml, dimr},
    dimm = main // Dimensions;
    diml = phil // Dimensions // Last;
    dimr = phir // Dimensions // First;
    {
        main // RightComposition[
            PadRight[#, # // Dimensions // Add[{0, diml}]]&,
            PadLeft[#, # // Dimensions // Add[{dimr, dimr}]]&,
            Identity
        ],
        phil // PadLeft[#, # // Dimensions // Add[{dimr, dimm[[2]] + dimr}]]&,
        phir // RightComposition[
            PadLeft[#, # // Dimensions // Add[{0, dimr}]]&,
            PadRight[#, # // Dimensions // Add[{dimm[[1]], diml}]]&,
            Identity
        ],
        Nothing
    }
];

(* ClearAll @ addIndex; *)
(* addIndex[n_Integer] /; n > 0 := RightComposition[ *)
(*     ArrayRules, *)
(*     Most, *)
(*     Map[#[[1]] -> {n, #[[2]]}&], *)
(*     Identity *)
(* ]; *)

(* (1* https://mathematica.stackexchange.com/a/222572 *1) *)
(* getcols[xs_SparseArray] := Internal`PartitionRagged[ *)
(*     xs["ColumnIndices"], *)
(*     Differences[xs["RowPointers"]] *)
(* ]; *)

(* ::Subsubsection::Closed::*)
(*plot*)

(* This is just a temporary helper function for debugging *)
ClearAll @ plot;
plot[topMargin_Integer, rightMargin_Integer, size_Integer][data_] := Internal`PartitionRagged[data, {
    Flatten[{
        topMargin,
        ConstantArray[
            data // Dimensions // First // Add[-topMargin] // Quotient[#, size]&,
            size
        ],
        {}
    }],
    Flatten[{
        topMargin,
        ConstantArray[
            data // Dimensions // Last // Add[-topMargin - rightMargin] // Quotient[#, size]&,
            size
        ],
        rightMargin,
        {}
    }]
}] // msS1;

