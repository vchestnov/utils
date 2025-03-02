(* ::Package:: *)

BeginPackage["utils`"]

filter::usage = "The filter function."

save::usage = "Memoize arguments for future inspection."
dvals::usage = "Inspect `DownValues`."
Hide::usage = "Hide arguments as a \"...\" string."
Unhide::usage = "Unhide hidden arguments."
zipWith::usage = "zipWith :: {a -> b} -> {a} -> {b}"
zipList::usage = "zipList :: {a -> b} -> {a} -> {b}"
Lengths::usage = "..."
Firsts::usage = "..."
Lasts::usage = "..."
Multiply::usage = "..."
Add::usage = "..."
Map2::usage = "..."
Map3::usage = "..."
Map4::usage = "..."
Apply1::usage = "..."
Apply2::usage = "..."

PlusToList::usage = "..."
PowerToList::usage = "..."
TimesToList::usage = "..."

deleteZeroRows::usage = "..."
rowReduce::usage = "..."
getNullSpace::usage = "..."
slicer::usage = "Slice a list into sublists of length up to `n`."
mS::usage = "mS :: Matrix -> String"
msS::usage = "msS :: {Matrix} -> String"
msS1::usage = "msS1 :: {{Matrix}} -> String"
eForm::usage = "..."

submons::usage = "Substitute monomials in `vars` with symbols `head` with exponents in the arguments."
subjs::usage = "Substitute `vars` using the `j`-notation. Backward compatibility version."
sym2ind::usage = "Convert a symbol to an indexed object."
ind2sym::usage = "Convert an indexed object to a symbol."
mseries1::usage = "Series expansion of tensors."

clearDownValues::usage = "..."

TM::usage = "Measure timing."
ClipCopy::usage = "Copy an expression to the clipboard, and return it."
MkString::usage = "Convert arguments to one string."
LeadingSign::usage = "Return the sign of the leading term of a polynomial. Which term is considered \"leading\" is up to Mathematica term ordering."
WrString::usage = "..."
MkFile::usage = "..."
MkTemp::usage = "..."
MkTempDirectory::usage = "..."
EnsureDirectory::usage = "..."
EnsureNoDirectory::usage = "..."
EnsureCleanDirectory::usage = "..."
EnsureNoFile::usage = "..."

colorANSICode::usage = "..."
resetANSICode::usage = "..."
abbr::usage = "..."
Restore::usage = "..."

addValidation::usage = "..."

Begin["`Private`"]

(* From `AMFlow.m` *)
$j = Symbol["Global`j"];

(* ::Section::Closed:: *)
(* Till's stuff *)


(* Compute the leading term in series expansion *)
ClearAll[seriesleader];
seriesleader[{x_, x0_}] := seriesleader[#, {x, x0}]&
seriesleader[f_List, {x_, x0_}] := seriesleader[#, {x, x0}]& /@ f
seriesleader[f_, {x_, x0_}] := seriesleader[f, {x, x0, -2}]
seriesleader[f_, {x_, x0_, startord_}] := Module[{tmp, ord=startord},
    tmp = Series[f, {x, x0, ord}];
    (* Print[ord, ": ", tmp]; *)
    If[Head[tmp]==SeriesData,
        While[tmp[[3]]==={},
            ord += 1;
            tmp = Series[f, {x, x0, ord}];
            (* Print[ord, ": ", tmp]; *)
        ];
    ];
    tmp /. chopseries[x]
];
ClearAll[rseriesleader];
rseriesleader[x_List] := { f_ :> seriesleader[f, x] };

chopseries[var_] := {
    HoldPattern[SeriesData[var, var0_, coeffs_, nmin_, nmax_, den_]] :>
        coeffs[[1]] If[var0==DirectedInfinity[1], 1/var, (var - var0)]^(nmin/den)
}

logexpand = {Log[x_] :> Plus @@ (#2 Log[#1] & @@@ FactorList[x])};

filter[pattern_] := Union @ Flatten @ Cases[#, pattern, -1]&;

(* ::Section:: *)
(* My stuff *)


save[xs___] := save[xs] = Nothing;
dvals[n_Integer] := RightComposition[
    DownValues,
    Part[#, ;;-n]&,
    Map[Replace[_[_[_[xs__]], y_] :> {xs, y}]],
    Identity
];
dvals[ex_] := dvals[2][ex];


(*zipWith :: {a -> b} -> {a} -> {b}*)
(*zipWith :: N -> N -> N in terms of length*)
(*This version doesn't work well when xs is a nested List xs :: {{a}}*)
(*zipWith[fs_List, xs_List] /; SameQ[fs // Length, xs // Length] := Inner[Compose, fs, xs, List];*)
zipWith[fs_List, xs_List] /; SameQ[fs // Length, xs // Length] := MapThread[Compose, {fs, xs}];

(*zipList :: {a -> b} -> {a} -> {b}*)
(*zipList :: N -> M -> N*M in terms of length*)
(* zipList[fs_List, xs_List] := Outer[Compose, fs, xs, 1] // Flatten[#, 1]&; *)
(* Is this version better? *)
zipList[fs_List, xs_List] := Outer[Compose, fs, xs, 1] // Flatten[#, {1}]&;
zipList[fs_List] := zipList[fs, #]&;
zipListP[fs_List, xs_List, size_Integer] := xs // slicer[size] // ParallelMap[zipList[fs, #]&, #]& // Flatten[#, 1]&;
pureList = List;

Attributes[Hide] = {Flat, OneIdentity, Constant};
Format[Hide[xs:(_List | _SparseArray)]] := MkString["...", xs // Dimensions // ToString];
Format[Hide[xs__]] := "...";
Unhide = ReplaceAll[Hide -> Identity]

Lengths = Map[Length];
Firsts  = Map[First];
Lasts   = Map[Last];
Multiply[xs__] = Times[xs, #]&;
Add[xs__] = Plus[xs, #]&;
Map2[f_] = Map[f, #, {2}]&;
Map3[f_] = Map[f, #, {3}]&;
Map4[f_] = Map[f, #, {4}]&;
Apply1[f_] = Apply[f, #, {1}];
Apply2[f_] = Apply[f, #, {2}];


PlusToList[expr_Plus] := expr // Apply[List];
PlusToList[expr_] := expr // List;


PowerToList[Power[expr_, n_Integer]] := ConstantArray[expr^Sign[n], Abs[n]];
PowerToList[expr_] := expr // List;


TimesToList[expr_Times] := expr // Apply[List] // Map[PowerToList] // Flatten;
TimesToList[expr_Power] := expr // PowerToList;
TimesToList[expr_] := expr // List;

TimesToList2[expr_Times] := expr // Apply[List];
TimesToList2[expr_] := expr // List;



eForm = RightComposition[
    (*N[#, 3]&,*)
    N,
    EngineeringForm[#, NumberFormat -> (Row[{#1, "e", If[SameQ[#3, ""], "0", #3]}]&)]&,
    Identity
];

deleteZeroRows = Apply[List] /* DeleteCases[x_ /; SameQ[x["Density"], 0.]] /* SparseArray;
rowReduce[{}] := {};
rowReduce[x_] := x // RowReduce // SparseArray // deleteZeroRows;
getNullSpace[{}] := {};
getNullSpace[x_] := x // NullSpace // If[SameQ[#, {}], {}, # // SparseArray]&;


ClearAll[mS, msS, msS1];
(* mS :: Matrix -> String *)
mS = RightComposition[
    Normal,
    Map[ReplaceAll[x_ /; Not[MemberQ[{0, 1}, x]] :> "*"], #, {2}]&,
    (* Map[ *)
    (*     ReplaceAll[x_ /; Not[MemberQ[Join[Range[0, 9], Alphabet[] // ToExpression], x]] :> "*"], *)
    (*     #, *)
    (*     {2} *)
    (* ]&, *)
    ReplaceAll[0 -> " "],
    Prepend[#, ConstantArray["=", # // Dimensions // Last]]&,
    Append[#, ConstantArray["=", # // Dimensions // Last]]&,
    Map[MkString],
    Map["|" <> # <> "|"&],
    Riffle[#, "\n"]&,
    MkString,
    Identity
];
(* msS :: {Matrix} -> String *)
msS = RightComposition[
    Map[mS /* (StringSplit[#, "\n"]&) /* (StringTake[#, {2, -2}]&)],
    Transpose,
    Map[Riffle[#, "|"]&],
    Map[MkString],
    Map["|" <> # <> "|"&],
    Riffle[#, "\n"]&,
    MkString,
    Identity
];
(* msS1 :: {{Matrix}} -> String *)
msS1 = RightComposition[
    Map[msS /* (StringSplit[#, "\n"]&) /* Most],
    MapAt[Append[#, #[[1]]]&, #, {-1}]&,
    Map[Riffle[#, "\n"]&],
    Riffle[#, "\n"]&,
    MkString,
    Identity
];

(* ::Subsubsection::Closed:: *)
(*submons and subjs*)

submons[vars_List, head_:$j] := RightComposition[
    Collect[#, vars, $coeff]&,
    Expand,
    ReplaceAll[$coeff[h_] mon_. :> Times[h, mon // Exponent[#, vars]& // Apply[head]]],
    Identity
];
submons[var_, head_:$j] := submons[{var}, head];
subjs[vars_] := submons[vars, $j];

(* ::Subsubsection::Closed:: *)
(*sym2ind, ind2sym*)
(*
 * For "good" input: `sym2ind /* ind2sym == Identity` and `ind2sym /* sym2ind == Identity`
 * Edge case (due to Henrik): `t0012 // sym2ind --> t[12]`, i.e. trailing zeros are removed by Mathematica
 *)
sym2ind = RightComposition[
    MkString,
    StringCases[#, Alternatives[LetterCharacter.., DigitCharacter..]]&,
    Map[ToExpression],
    Apply[Construct],
    (*Edgecase of no arguments*)
    Replace[x_[] :> x],
    Identity
];
ind2sym = MkString /* StringDelete[{"[", "]", ",", " "}] /* ToExpression;

(* ::Subsubsection::Closed:: *)
(*mseries*)
(*
 * Expand a tensor in `var` around `0`, convert it to `j`-notation in `{var, dvar}`
 * To restore the original tensor in `j`-notation: `Apply[Dot]`
 *)
ClearAll[mySeries, mseries, mseries1, mseries2];

mySeries[xs_List, args__] := xs // Map[mySeries[#, args]&];
(* mySeries[x_, {var_, pt_, max_}] /; And[max < 0, FreeQ[x, var]] := 0; *)
mySeries[x_, {var_, pt_, max_}] /; And[max < 0, FreeQ[x, var]] := SeriesData[var, 0, {}, 0, 0, 1];
mySeries[x_, args__] := Series[x, args];

mseries[{var_, dvar_}, max_] := RightComposition[
    (*unwrap `SparseArray` as it conflicts with `Series`*)
    Normal,
    Series[#, {var, 0, max}]&,
    Normal,
    subjs[{var, dvar}],
    (*TODO: PadRight until `j[_, max]`?*)
    {#, # // filter[_$j] // SortBy[#, Last /* Multiply[-1]]&}&,
    {
        # // Apply[CoefficientArrays] // Last,
        #[[2]]
    }&,
    Identity
];
mseries1[var_, max_] := RightComposition[
    Series[#, {var, 0, max}]&,
    Normal,
    subjs[{var}],
    (* Order args for `Apply[CoefficientArrays]` *)
    (* {#, # // filter[_$j] // SortBy[#, Last /* Multiply[-1]]&}&, *)
    {#, # // filter[_$j]}&,
    {
        #[[2]],
        # // RightComposition[
            Apply[CoefficientArrays],
            Last,
            (* Bring `j`'s index to the left *)
            Transpose[#, # // Dimensions // Length // Range // List // Cycles]&,
            Identity
        ]
    }&,
    Identity
];
mseries2[var_, max_] := RightComposition[
    mySeries[#, {var, 0, max}]&,
    Normal,
    subjs[{var}],
    (* Order args for `Apply[CoefficientArrays]` *)
    (* {#, # // filter[_$j] // SortBy[#, Last /* Multiply[-1]]&}&, *)
    {
        #,
        # // filter[_$j]
        // Part[#, All, 1]&
        // extendRange[max]
        // Map[j]
    }&,
    {
        #[[2]],
        # // RightComposition[
            Apply[CoefficientArrays],
            Last,
            (* Bring `j`'s index to the left *)
            Transpose[#, # // Dimensions // Length // Range // List // Cycles]&,
            Identity
        ]
    }&,
    Identity
];



(* ::Subsection::Closed:: *)
(*slicer*)

ClearAll @ slicer
(* Slice list into sublist of length up to `n` *)
slicer[n_Integer] /; n > 0 := Append[
    Partition[#, n] // Apply[List],
    Part[#, -Mod[Length @ #, n];;]
]&;
slicer[list:(_List | _SparseArray), n_Integer] /; n > 0 := list // slicer[n];
(* FIXME ugh *)
slicer[n1_Integer, n2_Integer][m:(_List | _SparseArray)] := m // RightComposition[
    Normal,
    Internal`PartitionRagged[#, m // Dimensions // {
        Append[ConstantArray[n1, Quotient[#[[1]], n1]], Mod[#[[1]], n1]],
        Append[ConstantArray[n2, Quotient[#[[2]], n2]], Mod[#[[2]], n2]],
        Nothing
    }& // Map[DeleteCases[0]]]&,
    Identity
];
(* /; With[{dims = m // Dimensions}, *)
(* Print[dims]; *)
(* And[ *)
(*     SameQ[dims, 2], *)
(*     dims[[1]] >= n1, *)
(*     dims[[2]] >= n2, *)
(*     True *)
(* ]] *)

(* ::Subsection::Closed:: *)
(*getDens*)

(*
 * Get all unique denominators in `x`
 *)
ClearAll[getDens, getDens1];
getDens[x_List] := x // RightComposition[
    Flatten,
    Together,
    Denominator,
    Factor,
    Map[FactorList /* Rest /* Map[First]],
    Flatten,
    Union,
    (* TODO: fix this ducktape
     * `{x (1 - x + y), y (-1 + x - y)} // Expand  // 1 / #& // getDens`
     * gives
     * `{x, -1 + x - y, y, 1 - x + y}`
     *)
    Map[FactorList /* Rest /* Map[First]],
    Flatten,
    Union,
    Identity
];
getDens[x_] := getDens[{x}];
(*Older version without `FactorList`*)
getDens1[x_List] := RightComposition[
    Flatten,
    Together,
    Denominator,
    Factor,
    Map[TimesToList],
    Flatten,
    Union,
    DeleteCases[n_ /; NumericQ[n]],
    Expand,
    Map[RightComposition[
        PlusToList,
        (*TODO: use some built-in mma function?*)
        # / (#[[1]] // Replace[(n_ | n_. _) /; NumericQ[n] :> n])&,
        Apply[Plus],
        Identity
    ]],
    Union,
    Identity
];

(* ::Subsection::Closed:: *)
(*addValidation*)

SetAttributes[addValidation, HoldAll];
addValidation[symbol_Symbol] := CompoundExpression[
	symbol::badargs = "`1` wrong arguments `2`",
	symbol[xs___] := Module[{},
		Message[symbol::badargs, SymbolName[symbol], {xs}];
		Throw[$Failed]
	]
];

(* ::Section:: *)
(* From Thomas Hahn *)

$AbbrPrefix = "c";
abbr[expr_] := abbr[expr] = Unique[$AbbrPrefix];
Structure[expr_, x_] := Collect[expr, x, abbr];
AbbrList[] := Cases[DownValues[abbr], _[_[_[f_]], s_Symbol] -> s -> f];
Restore[expr_] := expr /. AbbrList[]
clearDownValues[head_] := Set[
    DownValues[head],
    DownValues[head] // DeleteCases[#, _[_[_[x_, ___]], _] /; UnsameQ[Head[x], Pattern]]&
];

(* ::Section:: *)
(* From Vitaly Magerya's utils.m, which will eventually be released under
 * GPL-3, right? ;P
 * https://github.com/magv/alibrary
 *)

SetAttributes[TM, HoldFirst];
TM[ex_] := AbsoluteTiming[ex] // (Print[HoldForm[ex], ": ", #[[1]], " sec"]; #[[2]])&;
TM[str_String] := Function[ex, AbsoluteTiming[ex] // (Print[str, ": ", #[[1]], " sec"]; #[[2]])&, HoldFirst];

(* Return the lowest power of a series expression. *)
SeriesLowestPower[l_List] := Map[SeriesLowestPower, l]
SeriesLowestPower[Verbatim[SeriesData][x_, x0_, l_List, n1_, n2_, d_]] := n1/d

(* Fail the computation unless a condition is met. Useful for
 * assetions and unit tests. *)
FailUnless[tests___] := Module[{test, idx, result},
  Do[
    test = Extract[Hold[tests], {idx}, HoldForm];
    If[test === HoldForm[Null], Continue[]];
    result = ReleaseHold[test];
    If[result =!= True,
      If[MatchQ[Extract[test, {1,0}, HoldForm], HoldForm[_Symbol]],
        Print["!!! Test: ", Extract[test, {1,0}, HoldForm], " => ", result];
        Print["!!! 1: ", Extract[test, {1,1}, HoldForm]];
        Print["!!! == ", Extract[test, {1,1}]];
        Print["!!! 2: ", Extract[test, {1,2}, HoldForm]];
        Print["!!! == ", Extract[test, {1,2}]];
        ,
        Print["!!! Test: ", test];
        Print["!!!    => ", result];
      ];
      Error["Test failed!"];
    ];
    ,
    {idx, Length[Hold[tests]]}];
];
SetAttributes[FailUnless, {HoldAll}]

(* Return the sign of the leading term of a polynomial. Which
 * term is considered "leading" is up to Mathematica term ordering.
 *)
LeadingSign[ex_List] := Map[LeadingSign, ex]
LeadingSign[ex_ /; (FactorTermsList[ex] // First // Negative)] := -1
LeadingSign[ex_] := 1

(* Copy an expression to the clipboard, and return it. *)
ClipCopy[ex_] := (
  Put[ex, "/tmp/clipboard.txt"];
  Run["xclip -i -selection clipboard /tmp/clipboard.txt"];
  ex
);

MkString = RightComposition[
    List,
    Flatten,
    Map[ToString],
    StringJoin
];

Error[msg__] := If[Length[Cases[$CommandLine, "-script"]] > 0,
    Print["ERROR: ", msg]; Exit[1];
    ,
    Print[Style["ERROR: ", Red, Bold], msg]; Throw[$Failed];
];

(* Convert the items into a string, and write it into a given file object. *)
WrString[f_, items__] := {items} // Flatten // Map[BinaryWrite[f, # // ToString]&]

(* Convert the items into a string and write it into the file. *)
MkFile[filename_, items__] := Module[{fd},
  (* The BinaryFormat is needed for the BinaryWrite in WrString. *)
  fd = OpenWrite[MkString[filename], BinaryFormat->True];
  If[fd === $Failed, Error["MkFile: failed to open ", filename, " for writing"]];
  WrString[fd, {items}];
  Close[fd];
]

(* Return a random name of a fresh file of the form prefix.XXXXsuffix.
 * Make sure no file with this name exists.
 *)
MkTemp[prefix_, suffix_] := Module[{i, fn, alphabet},
  alphabet = Characters["abcdefghijklmnopqrstuvwxyz0123456789"];
  While[True,
    i = RandomSample[alphabet, 8];
    fn = FileNameJoin[{$TemporaryDirectory, MkString[prefix, ".", Environment["USER"], ".", $ProcessID, ".", i, suffix]}];
    If[Not[FileExistsQ[fn]], Return[fn]];
  ]
]

(* Create a new temporary directory, with the name of the form
 * prefix.XXXXsuffix.
 *)
MkTempDirectory[prefix_, suffix_] := Module[{dirname},
  dirname = MkTemp[prefix, suffix];
  EnsureDirectory[dirname];
  dirname
]

(* Make sure a directory exists. Create it if it doesn’t. *)
EnsureDirectory[dirs__] := Module[{dir},
  Do[Quiet[CreateDirectory[dir], {CreateDirectory::filex, CreateDirectory::eexist}];, {dir, {dirs}}];
]

(* Make sure a directory doesn’t exist. Remove it if it does. *)
EnsureNoDirectory[dirs__] := Module[{dir},
  Do[Quiet[DeleteDirectory[dir, DeleteContents->True], {DeleteDirectory::nodir}];, {dir, {dirs}}];
]

(* Make sure a directory exists and has no files inside. *)
EnsureCleanDirectory[dirs__] := (
  EnsureNoDirectory[dirs];
  EnsureDirectory[dirs];
);

(* Make sure a file doesn’t exist. Remove it if it does. *)
EnsureNoFile[files__] := Module[{file},
  Do[Quiet[DeleteFile[file], {DeleteFile::fdnfnd}];, {file, {files}}];
]

(* Read a Maple file created by 'save(var, "filename")'. Strip
 * the var name, only return the content.
 *)
MapleGet[filename_String] := Module[{text},
    text = ReadString[filename];
    If[text === $Failed,
        Error["! Failed to read from ", filename];
    ];
    FromMaple[text]
]

(* Convert a string in the Maple format into a Mathematica expression. *)
FromMaple[text_String] := text // RightComposition[
    (* Drop the final '\' on a line. *)
    StringReplace[RegularExpression["(?m)\\\\$"] -> ""],
    (* Drop the whitespace. *)
    StringReplace[RegularExpression["\\s"] -> ""],
    (* Drop the enclosing 'var := ' and ';'. *)
    StringReplace[RegularExpression["^[\\w]+:=|[;:]$"] -> ""],
    (* Transform simple indices like 'zeta[2]' into function
     * calls like 'zeta(2)'. Note that if index arguments contain
     * '[]', this regex will fail.
     *)
    StringReplace[RegularExpression["(\\w)\\[([^]]+)\\]"] -> "$1($2)"],
    (* Every other occurrence of '[' and ']' are lists. *)
    StringReplace[{"[" -> "{", "]" -> "}"}],
    (* Maple's array rules: '(1,2)=x' -> '{1,2}->x' *)
    StringReplace[
        "(" ~~ x:(DigitCharacter | ",").. ~~ ")=" ~~ y:Except[","].. ~~ z:("," | "}")
        :>
        "{" ~~ x ~~ "}" ~~ "->" ~~ y ~~ z
    ],
    (* Maple's array dimensions *)
    StringReplace[
        "1.." ~~ x:DigitCharacter.. ~~ ",1.." ~~ y:DigitCharacter..
        :>
        "{" ~~ x ~~ "," ~~ y ~~ "}"
    ],
    StringReplace[
        "array(" ~~ x__ ~~ ")"
        :>
        "array[" ~~ x ~~ "]"
    ],
    ToExpression[#, TraditionalForm, Hold] &,
    ReplaceAll[O->OO],
    ReplaceAll[FromMaple$Map],
    ReleaseHold,
    Identity
];

FromMaple$Map = {
    HoldPattern[psi[x_]] :> PolyGamma[x],
    HoldPattern[psi[n_, x_]] :> PolyGamma[n, x],
    (* Note that HyperInt uses the original Goncharov notation
     * for Li and MZV, unlike HPL/HypExp, which use the reverse
     * one.
     *)
    (*HoldPattern[zeta[n__]] :> MZV[Reverse[{n}]],*)
    HoldPattern[zeta[n__]] :> Mzv @@ Reverse[{n}],
    HoldPattern[polylog[n_, x_]] :> PolyLog[n, x],
    HoldPattern[Complex[yy_]] :> Complex[0, yy],
    HoldPattern[Complex[xx_, yy_]] :> Complex[xx, yy],
    HoldPattern[array[dims_, rules_]] :> SparseArray[rules, dims],
    Nothing
};

(* Save an expression in a format suitable for Maple\[CloseCurlyQuote]s `read()`
 * command.
 *
 * The name of the variable is set automatically to the
 * basename of the file, so `MaplePut[..., "x.mma"]` would
 * result in a variable `x` being defined after `read("x.mma")`
 * is executed.
 *)
MaplePut[expression_, filename_String] :=
    MaplePut[expression, filename, FileBaseName[filename]]

MaplePut[expression_, filename_String, varname_String] := Module[{fd},
    fd = OpenWrite[filename, BinaryFormat -> True];
    If[fd === $Failed, Error["MaplePut: failed to open ", filename, " for writing"]];
    WrString[fd, varname, " := ", expression // ToMaple, ":\n"];
    Close[fd];
]

(* Convert a Mathematica expression into a a string with an
 * equivalent Maple expression. *)
ToMaple[expression_] :=
    ToString[expression /. ToMaple$Map, InputForm] //
        StringReplace[{" " -> "", "[" -> "(", "]" -> ")", "{" -> "[", "}" -> "]"}]

ToMaple$Map = {
    HoldPattern[Log[x_]] :> ln[x],
    HoldPattern[PolyGamma[x_]] :> psi[x],
    HoldPattern[PolyGamma[n_, x_]] :> psi[n, x],
    HoldPattern[PolyLog[n_, x_]] :> polylog[n, x],
    (* There's no Nielsen polylog on the Maple side; we'll convert
     * it into 'Hpl' from HyperInt.
     *)
    HoldPattern[PolyLog[n_, p_, x_]] :> Hpl[x, Join[Table[0, n], Table[1, p]]],
    (* Convert 'Zeta', 'HPL', 'MZV' and 'Mzv' into HyperInt equivalents.
     *)
    (*HoldPattern[Zeta[n_]] :> zeta[n],*)
    HoldPattern[Zeta[n_]] :> Hpl[1, {n}],
    HoldPattern[HPL[w_List, x_]] :> Hpl[x, w],
    (* Note that HyperInt uses the original Goncharov notation
     * for Li and MZV, unlike HPL/HypExp, which use the reverse
     * one.
     *)
    (* HoldPattern[MZV[n_List]] :> zeta @@ Reverse[n] *)
    HoldPattern[MZV[{w__}]] :> MzvToHpl[Mzv[w]],
    HoldPattern[z_Mzv] :> MzvToHpl[z]
};

(* ::Section:: *)
(* From CodeInspector's Format.wl *)
(* https://github.com/WolframResearch/codeinspector *)

colorANSICode[GrayLevel[gray_]] :=
With[{code = ToString[232 + Round[23 * gray]]},
  "\[RawEscape][38;5;"<>code<>"m"
];

colorANSICode[RGBColor[r_, g_, b_]] :=
With[{code = ToString[16 + {36, 6, 1} . Round[5 * {r, g, b}]]},
  "\[RawEscape][38;5;"<>code<>"m"
];

(*
Use simpler sequences for common cases

This also works around an issue on Windows where the 38;5; sequences affect the bold bit
*)
colorANSICode[Black] := "\[RawEscape][30m";
colorANSICode[Red] := "\[RawEscape][31m";
colorANSICode[Green] := "\[RawEscape][32m";
colorANSICode[Yellow] := "\[RawEscape][33m";
colorANSICode[Blue] := "\[RawEscape][34m";
colorANSICode[Magenta] := "\[RawEscape][35m";
colorANSICode[Cyan] := "\[RawEscape][36m";
colorANSICode[White] := "\[RawEscape][37m";

colorANSICode[Automatic] = "";


weightANSICode[Bold] = "\[RawEscape][1m";
weightANSICode["SemiBold"] = "\[RawEscape][1m";
weightANSICode["Medium"] = "";
weightANSICode[Automatic] = "";

variationsANSICode[{"Underline"->True}] = "\[RawEscape][4m";
variationsANSICode[Automatic] = "";

resetANSICode[] = "\[RawEscape][0m";

(* ::Section:: *)
(* End *)

End[] (* "`Private`" *)

EndPackage[] (* "utils`" *)
