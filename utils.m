(* ::Package:: *)

BeginPackage["utils`"]

filter::usage = "The filter function."

save::usage = "save[args...] memoizes the call to `Nothing`, so the saved argument tuples can be inspected later through `DownValues[save]`."
dvals::usage = "dvals[head] returns a simplified view of `DownValues[head]`. dvals[n][head] uses `n` wrapper levels when extracting the left- and right-hand sides."
Hide::usage = "Hide[expr] wraps `expr` so it prints as \"...\". Hidden lists and `SparseArray` objects print as \"...\" followed by their dimensions."
Unhide::usage = "Unhide replaces `Hide` with `Identity` inside an expression, revealing hidden arguments again."
zipWith::usage = "zipWith[fs, xs] pairwise composes equally long lists `fs` and `xs` with `MapThread[Compose, ...]`."
zipList::usage = "zipList[fs, xs] returns the flattened outer product of pairwise compositions between `fs` and `xs`. zipList[fs] is the corresponding operator form."
Lengths::usage = "Lengths[list] maps `Length` over the first level of `list`."
Firsts::usage = "Firsts[list] maps `First` over the first level of `list`."
Lasts::usage = "Lasts[list] maps `Last` over the first level of `list`."
Multiply::usage = "Multiply[x1, x2, ...][y] returns `x1 x2 ... y`."
Add::usage = "Add[x1, x2, ...][y] returns `x1 + x2 + ... + y`."
Map2::usage = "Map2[f][expr] applies `Map[f, expr, {2}]`."
Map3::usage = "Map3[f][expr] applies `Map[f, expr, {3}]`."
Map4::usage = "Map4[f][expr] applies `Map[f, expr, {4}]`."
Apply1::usage = "Apply1[f][expr] applies `Apply[f, expr, {1}]`."
Apply2::usage = "Apply2[f][expr] applies `Apply[f, expr, {2}]`."

PlusToList::usage = "PlusToList[expr] turns a sum into a list of its terms and wraps any non-sum as a singleton list."
PowerToList::usage = "PowerToList[expr] expands an integer power into a list of repeated factors; any other expression is wrapped as a singleton list."
TimesToList::usage = "TimesToList[expr] turns a product into a flat list of factors, expanding integer powers via `PowerToList`."

deleteZeroRows::usage = "deleteZeroRows[m] removes zero-density rows from a sparse matrix and returns a `SparseArray`."
rowReduce::usage = "rowReduce[m] row-reduces `m`, converts the result to `SparseArray`, and drops zero rows. rowReduce[{}] returns `{}`."
getNullSpace::usage = "getNullSpace[m] returns `NullSpace[m]`, converting a nonempty basis to `SparseArray`. getNullSpace[{}] returns `{}`."
slicer::usage = "slicer[n][list] slices `list` into consecutive chunks of length at most `n`. slicer[list, n] is equivalent. slicer[n1, n2][m] partitions a matrix into ragged `n1` by `n2` blocks."
mS::usage = "mS[m] renders a matrix as an ASCII string, showing `1` entries explicitly, `0` entries as spaces, and other entries as `*`."
msS::usage = "msS[{m1, m2, ...}] renders several matrices side by side as one ASCII string."
msS1::usage = "msS1[{{...}, {...}, ...}] renders rows of side-by-side matrices as one multi-line ASCII string."
eForm::usage = "eForm[x] numerically formats `x` in engineering notation, using `e`-style exponents."

submons::usage = "submons[vars, head][expr] collects `expr` in `vars` and replaces each monomial by `head` applied to its exponent vector. submons[var, head] uses a single variable."
subjs::usage = "subjs[vars][expr] is `submons[vars, $j][expr]`."
sym2ind::usage = "sym2ind[sym] converts a symbol with alternating letter and digit runs into indexed form, for example `x12y3` to `x[12, y, 3]`."
ind2sym::usage = "ind2sym[expr] removes brackets, commas, and spaces from an indexed expression and converts the result back to a symbol."
mseries1::usage = "mseries1[var, max][expr] expands `expr` as a series in `var` about `0`, rewrites the monomials in `$j` notation, and returns `{jTerms, coeffArray}`."

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
FormatAmount::usage = "..."
FormatBytes::usage = "..."
FormatSeconds::usage = "..."
StringToNumber::usage = "..."
FormatFixed::usage = "..."
FormatScientific::usage = "..."

colorANSICode::usage = "..."
resetANSICode::usage = "..."
abbr::usage = "..."
Restore::usage = "..."

addValidation::usage = "addValidation[symbol] installs a catch-all definition on `symbol` that emits `symbol::badargs` and throws `$Failed` for unsupported argument patterns."

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

(* filter[pattern_] := Union @ Flatten @ Cases[#, pattern, -1]&; *)
filter[pattern_] := RightComposition[
    List,
    Cases[#, pattern, -1]&,
    Flatten,
    Union,
    Identity
];

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
Apply1[f_] = Apply[f, #, {1}]&;
Apply2[f_] = Apply[f, #, {2}]&;


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

SetAttributes[
    {
        save,
        dvals,
        Hide,
        Unhide,
        zipWith,
        zipList,
        Lengths,
        Firsts,
        Lasts,
        Multiply,
        Add,
        Map2,
        Map3,
        Map4,
        Apply1,
        Apply2,
        PlusToList,
        PowerToList,
        TimesToList,
        deleteZeroRows,
        rowReduce,
        getNullSpace,
        slicer,
        mS,
        msS,
        msS1,
        eForm,
        submons,
        subjs,
        sym2ind,
        ind2sym,
        mseries1,
        addValidation
    },
    ReadProtected
];

(* ::Section:: *)
(* From Thomas Hahn *)

$AbbrPrefix = "c";
abbr[expr_] := abbr[expr] = Unique[$AbbrPrefix];
Structure[expr_, x_] := Collect[expr, x, abbr];
AbbrList[] := Cases[DownValues[abbr], _[_[_[f_]], s_Symbol] :> s -> f];
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

(* Format a real number in the scientific notation, e.g. 1.23e-4,
 * with a fixed total width (if it can be achieved).
 *)
FormatScientific[x:(_Integer|_Real), width_Integer] :=
Module[{sign, man, exp, zeros}, 
  {man, exp} = MantissaExponent[x//N, 10];
  sign = If[man >= 0, "", "-"];
  {man, exp} = If[man === 0.0, {0.0, 0}, {Abs[man]*10, exp - 1}];
  exp = "e" <> ToString[exp];
  man = ToString[NumberForm[man, Max[1, width - StringLength[sign] - StringLength[exp] - 1]]];
  zeros = width - StringLength[sign] - StringLength[man] - StringLength[exp];
  If[zeros > 0, sign <> man <> StringRepeat["0", zeros] <> exp, sign <> man <> exp]
]
FormatScientific[width_Integer] := FormatScientific[#, width]&
FormatScientific[Complex[re_, im_], width_Integer] :=
  FormatScientific[re, width] <> " " <> FormatScientific[im, width] <> "j"

(* Format a real number with fixed number of digits after the
 * decimal point.
 *)
FormatFixed[x:(_Integer|_Real), digits_Integer] :=
  IntegerDigits[x*10^digits//Round] //
  If[1 + digits - Length[#] > 0, Join[Table[0, 1 + digits - Length[#]], #], #]& //
  MkString[If[x < 0, "-", ""], #[[;;-digits-1]], ".", #[[-digits;;]]]&
FormatFixed[x:(_Integer|_Real), 0] :=
  IntegerDigits[x//Round] //
  If[1 - Length[#] > 0, Join[Table[0, 1 - Length[#]], #], #]& //
  MkString[If[x < 0, "-", ""], #]&
FormatFixed[digits_Integer] := FormatFixed[#, digits]&

FormatFixed[Complex[re_, im_], digits_Integer] :=
  FormatFixed[re, width] <> " " <> FormatFixed[im, width] <> "j"

(* Convert a string in scientific notation (e.g. `1.23e4`) to a
 * number. *)
StringToNumber[s_String] := Internal`StringToDouble[s]

(* Format a quantity in a human-readable format using the given
 * units. The units are specified as a list of string names and
 * numeric values.
 *)
FormatAmount[units_List] := FormatAmount[#, units]&
FormatAmount[amount_, units_List] := Module[{i, a},
  For[i = 1, i < Length[units] - 1 && amount > units[[i+1,2]]*0.95, i++, True];
  a = amount / units[[i, 2]] // N;
  MkString[NumberForm[a, {Infinity, 3}], units[[i,1]]]
]

(* Format bytes in human-readable format.
 *)
FormatBytes[amount_] := FormatAmount[amount, {
  {"B", 1}, {"kB", 2^10}, {"MB", 2^20}, {"GB", 2^30}, {"TB", 2^40},
  {"PB", 2^50}, {"EB", 2^60}, {"ZB", 2^70}, {"YB", 2^80}
}]

(* Format seconds in human-readable format.
 *)
FormatSeconds[amount_] := FormatAmount[amount, {
  {"s", 1}, {"m", 60}, {"h", 3600}, {"d", 24*3600}, {"w", 7*24*3600},
  {"y", 365*24*3600}
}]

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
