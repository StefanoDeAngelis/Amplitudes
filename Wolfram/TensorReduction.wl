(* ::Package:: *)

BeginPackage["TensorReduction`", {"DdimVariables`"}]


(* ::Section:: *)
(*Messages*)


UMatrix::usage = "UMatrix[\[Mu],\[Nu]] is the symmetric tensor projecting onto the subspace spanned by the declared external momenta: \!\(\*SubscriptBox[\"u\", \"\[Mu]\[Nu]\"]\) = \!\(\*SubsuperscriptBox[\"p\", \"i\", \"\[Mu]\"]\) \!\(\*SubscriptBox[\"\[CapitalDelta]\", \"ij\"]\) \!\(\*SubsuperscriptBox[\"p\", \"j\", \"\[Nu]\"]\). \n \n \t Use SubUMatrix to expand it explicitly."
uM::usage = "..."
MomentumDual::usage = "MomentumDual[k,\[Mu]] is the dual basis associated with the declared \
external momenta: \[LeftAngleBracket]\*SubsuperscriptBox[\"p\", \"j\", \"\[Mu]\"]\[RightAngleBracket] = \!\(\*SubscriptBox[\"\[CapitalDelta]\", \"ij\"]\) \!\(\*SubsuperscriptBox[\"p\", \"j\", \"\[Mu]\"]\). \n \n \t Use SubUMatrix to expand it explicitly."
pD::usage = "..."
MetricPerp::usage = "MetricPerp[\[Mu],\[Nu]] is the metric on the subspace orthogonal to the physical one: \[Eta]^\[Perpendicular]_{\[Mu]\[Nu]} = \[Eta]_{\[Mu]\[Nu]} - u_{\[Mu]\[Nu]}. \n \n \t Use SubMetricPerp to expand it."
etaP::usage = "..."
DualMetric::usage = "..."
dM::usage = "..."


DeclareExternalMomenta::usage = "DeclareExternalMomenta[{p1,p2,...}] sets up the tensor-reduction environment for the given list of external momenta. It stores the Gram matrix, its determinant, and its inverse, and defines the replacement rules used to expand UMatrix[\[Mu],\[Nu]], MomentumDual[k,\[Mu]], and MetricPerp[\[Mu],\[Nu]]. Any previous declaration is cleared first."
ClearExternalMomenta::usage = "ClearExternalMomenta[] resets the tensor reduction environment, clearing all previously declared external momenta and some precomputed data."

(*TensorReduction::usage = "..."*)
ExternalMomenta::usage = "ExternalMomenta[] returns the list of declared external momenta."
GramMatrix::usage = "..."
GramDeterminant::usage = "..."
InverseGramMatrix::usage = "..."
ProjectorRule::usage = "..."
DualMomentumRule::usage = "..."


PartitionsK::usage = "..."

WickTheorem::usage = "..."
ord::usage = "..."
contr::usage = "..."


SubProducts::usage = "..."
SubMetricPerp::usage = "..."
SubUMatrix::usage = "..."

ExpandTensorReduction::usage = "ExpandTensorReduction[expr] applies the full set of substitutions to expand MetricPerp, MomentumDual and UMatrix into explicit basis expressions."

UnitTensor::usage = "UnitTensor[rank] generates the unit tensor of the given rank in the declared basis."


$d::usage = "..."
Gram::usage = "..."


(* ::Section:: *)
(*Errors*)


TensorReduction::undef = "No (or inappropriate) external momenta have been declared. Call DeclareExternalMomenta[ext_List] first, with ext not empty and free of duplicates."


DeclareExternalMomenta::arg = "DeclareExternalMomenta expects a non-empty list of external momenta."
DeclareExternalMomenta::dup = "The external momenta must be duplicate-free. Received `1`."
DeclareExternalMomenta::sing = "The Gram matrix built from `1` is not invertible, so the tensor reduction cannot be generated."


UnitTensor::undef = "No (or inappropriate) external momenta have been declared. Call DeclareExternalMomenta[ext_List] first."
UnitTensor::arg = "UnitTensor expects a positive integer rank."


(* ::Chapter:: *)
(*Tensor Reduction*)


(* ::Section:: *)
(*Begin*)


Begin["`Private`"]


(* ::Section::Closed:: *)
(*Boxes*)


uMBox[mu_, nu_] :=
    TemplateBox[
        {mu, nu},
        "uM",
        DisplayFunction -> (SuperscriptBox["u", RowBox[{##}]]&),
        InterpretationFunction -> (RowBox[{"uM","[",RowBox[{#1, ",", #2}],"]"}]&)
    ]


etaPBox[\[Mu]_,\[Nu]_] :=
    TemplateBox[
        {\[Mu],\[Nu]},
        "etaP",
        DisplayFunction -> (SubsuperscriptBox["\[Eta]", "\[Perpendicular]", RowBox[{##}]]&),
        InterpretationFunction -> (RowBox[{"etaP","[",RowBox[{#1, ",", #2}],"]"}]&)
    ]


pDBox[mom_, k_, a_] :=
    TemplateBox[
        {mom, k, a},
        "pD",
        DisplayFunction -> (RowBox[{"\[LeftAngleBracket]", #1, "\[RightAngleBracket]"}]&),
        InterpretationFunction -> (RowBox[{"pD","[",RowBox[{#2, ",", #3}],"]"}]&)
    ]


dMBox[display_, args__] :=
    TemplateBox[
        {display, args},
        "dM",
        DisplayFunction -> (RowBox[{"\[LeftAngleBracket]", #1, "\[RightAngleBracket]"}]&),
        InterpretationFunction -> (RowBox[{"dM","[",RowBox[{TemplateSlotSequence[2, ","]}],"]"}]&)
    ]


(* ::Section::Closed:: *)
(*UMatrix, MetricPerp, MomentumDual*)


UMatrix[a_, b_] = uM[a, b];

uM[a_, b_] /; !OrderedQ[{a, b}] := uM[b, a]

uM /: MakeBoxes[uM[mu_, nu_], StandardForm | TraditionalForm] := uMBox[ToLabel[mu],ToLabel[nu]]


MetricPerp[a_, b_] := etaP[a, b]

etaP /: MakeBoxes[etaP[\[Mu]_,\[Nu]_], StandardForm | TraditionalForm] := etaPBox[ToLabel[\[Mu]],ToLabel[\[Nu]]]


MomentumDual[k_, a_] := pD[k, a]

pD /: MakeBoxes[pD[k_, a_], form : (StandardForm | TraditionalForm)] := 
    pDBox[
        MakeBoxes[Momentum[k, a], form],
        MakeBoxes[k, form],
        MakeBoxes[a, form]
    ]


DualMetric[] := 1
dM[] := 1
DualMetric[args__List] := dM[args]

dM /: MakeBoxes[dM[args : {_, _} ..], form : (StandardForm | TraditionalForm)] := 
    dMBox[
        RowBox @ Riffle[
            (MakeBoxes[#, form]& /@ (etaP @@@ {args})),
            "\[ThinSpace]"
        ],
        Sequence @@ (MakeBoxes[#, form]& /@ {args})
    ]


(* ::Section::Closed:: *)
(*$tensorReduction*)


(* Design overview:
   - Declaring external momenta fixes the basis for the reduction.
   - Every basis-dependent object is precomputed once and stored in a single Association.
   - UnitTensor first builds the abstract Wick-like combinatorics and expands the abstract tensors into explicit Momentum[...] data. *)


(* All kinematic data generated is stored in the variable $tensorReduction so a fresh kernel only needs DeclareExternalMomenta[...] to reconstruct the reduction setup. *)
(* Only one set of momentum at the time is allowed. *)
$tensorReduction = <||>;


(* ::Section:: *)
(*Auxiliary functions*)


declaredQ[] := AssociationQ[$tensorReduction] && KeyExistsQ[$tensorReduction, "ExternalMomenta"]


(* Resetting the Association is enough to invalidate the whole setup because every public variable derives from the same shared variable. *)
ClearExternalMomenta[] := ($tensorReduction = <||>;)


(* Single lookup helper so every quantity shares the same initialization check and error behaviour. *)
externalLookup[key_] :=
    If[
        declaredQ[],
        $tensorReduction[key],
        Message[TensorReduction::undef];
        $Failed
    ]


buildTensorReduction[ext_List] :=
    Block[
        {
            n,
            gramMatrix,
            gramDeterminant,
            deltaMatrix,
            position,
            subU,
            subDual
        },
        
        (* n counts the external basis vectors, not the full spacetime dimension DD. It controls the size of the Gram matrix and appears in the transverse-sector identities. *)
        n = Length[ext];
        
        (* The Gram matrix of the external momenta. *)
        gramMatrix =
            Simplify @ 
                Table[
                    DotProduct[Momentum[i], Momentum[j]],
                    {i, ext},
                    {j, ext}
                ];
            
        (* If the inverse Gram matrix does not exist, the chosen momenta do not provide a usable reduction basis, so we abort early and let the caller issue the public error. *)
        gramDeterminant = FullSimplify @ Det[gramMatrix];
        deltaMatrix = Quiet @ Check[Simplify[(Inverse[gramMatrix] * gramDeterminant) / Gram], $Failed];
            
        If[deltaMatrix === $Failed, Return[$Failed]];
            
        (* Remember where each symbolic momentum label sits in deltaMatrix so later rules can refer to momenta by name instead of by index. *)
        position = AssociationThread[ext, Range[n]];
            
        (* Expand the abstract projector UMatrix into the external basis: u^{\[Mu] \[Nu]} = p_i^{\[Mu]} \[CapitalDelta]_{ij} p_j^{\[Nu]}
        With[...] captures ext and deltaMatrix during the evaluation of the function. This step is necessary due to the delayed evaluation required for symbolic rules. *)
        subU =
            With[
                {momenta = ext, delta = deltaMatrix},

                (* uM[lor1_, lor2_] :> Table[Momentum[p, lor1], {p, momenta}] . delta . Table[Momentum[p, lor2], {p, momenta}] *)
                (* To avoid the appearance of TensorReduction`Private`lor1, and so on... *)
                uM[TensorReduction`m_, TensorReduction`n_] :> (Map[Momentum[#, TensorReduction`m] &, momenta] . delta . Map[Momentum[#, TensorReduction`n] &, momenta])
            ];
            
        (* MomentumDual is the dual basis associated with ext: MomentumDual[k]^lor = \[CapitalDelta]_{k i} p_i^lor *)
        subDual =
            With[
                {momenta = ext, delta = deltaMatrix, pos = position},
                
                (* pD[k_, lor_] /; KeyExistsQ[pos, k] :> delta[[pos[k]]] . Table[Momentum[p, lor], {p, momenta}] *)
                pD[TensorReduction`k_, TensorReduction`m_] /; KeyExistsQ[pos, TensorReduction`k] :> (delta[[pos[TensorReduction`k]]] . Map[Momentum[#, TensorReduction`m] &, momenta])
            ];
        
        <|
            "ExternalMomenta" -> ext,
            (* "NumberOfMomenta" -> n, *)
            "GramMatrix" -> gramMatrix,
            "GramDeterminant" -> gramDeterminant,
            "InverseGramMatrix" -> deltaMatrix,
            "ProjectorRule" -> subU,
            "DualMomentumRule" -> subDual
        |>
    ]


(* ::Subsection:: *)
(*Definition, properties and substitutions*)


(* Substitute the abstract Wick placeholders into actual tensor objects. *)
SubProducts[exp_] := 
    Block[
        {ord, contr, localexp = exp},
        
        ord[list_List] := Product[uM[mu[i], nu[i]], {i, list}];
        contr[lists__List] := Product[etaP[Sequence @@ (mu /@ list)], {list, {lists}}] * dM[Sequence @@ Map[nu, {lists}, {2}]];
        
        Return[localexp]
    ]


(* The transverse metric is left abstract during the combinatoric stage and only resolved into Metric - UMatrix when the final expression is expanded. *)
SubMetricPerp[exp_] := Block[{etaP, localexp = exp}, etaP[lor1_, lor2_] := Metric[lor1, lor2] - uM[lor1, lor2]; Return[localexp]]


SubUMatrix[exp_] := exp /. DualMomentumRule[] /. ProjectorRule[]


(* ::Section:: *)
(*DeclareExternalMomenta*)


DeclareExternalMomenta[ext_List] :=
    Module[{state},
        (* ext is treated as an ordered basis. Empty lists and duplicates are rejected. *)
        If[ext === {} || !ListQ[ext],
            Message[DeclareExternalMomenta::arg];
            Return[$Failed]
        ];
        
        If[!DuplicateFreeQ[ext],
            Message[DeclareExternalMomenta::dup, ext];
            Return[$Failed]
        ];
        
        state = buildTensorReduction[ext];
        
        (* A singular Gram matrix means the chosen external momenta do not define are not independent. *)
        If[state === $Failed,
            Message[DeclareExternalMomenta::sing, ext];
            Return[$Failed]
        ];
        
        $tensorReduction = state;
    ]

DeclareExternalMomenta[___] :=
    (
        Message[DeclareExternalMomenta::arg];
        $Failed
    )


(* ::Section:: *)
(*Reduction Helpers*)


(*TensorReduction[] :=
    If[
        declaredQ[],
        $tensorReduction,
        Message[TensorReduction::undef];
        $Failed
    ]*)

ExternalMomenta[] := externalLookup["ExternalMomenta"]
GramMatrix[] := externalLookup["GramMatrix"]
GramDeterminant[] := externalLookup["GramDeterminant"]
InverseGramMatrix[] := externalLookup["InverseGramMatrix"]
ProjectorRule[] := externalLookup["ProjectorRule"]
DualMomentumRule[] := externalLookup["DualMomentumRule"]


(* This is the public helper that reproduces the basic notebook substitution
   chain: MetricPerp -> Metric - UMatrix, then MomentumDual expansion, then UMatrix expansion. *)
ExpandTensorReduction[expr_] :=
    Block[{rules, expanded, dM},
        If[!declaredQ[],
            Message[TensorReduction::undef];
            Return[$Failed]
        ];

        rules = Union @ Cases[expr, dM[args__List] :> 2 Length[{args}], {0, Infinity}];
        rules = loadDualMetric /@ rules;
        
        expanded = expr //. rules;
        expanded = SubUMatrix[SubMetricPerp[expanded]]
    ]


(* ::Section:: *)
(*UnitTensor*)


UnitTensor[rank_Integer?Positive] :=
    Module[{expr},
        (* UnitTensor depends on the basis-specific rules cached by DeclareExternalMomenta, so calling it before initialization is an error. *)
        If[!declaredQ[],
            Message[UnitTensor::undef];
            Return[$Failed]
        ];
        
        (* Build the abstract Wick sum, translate ord/contr into tensor factors, then expand MetricPerp, MomentumDual and UMatrix into explicit basis expressions. *)
        expr =
            ExpandTensorReduction[
                SubProducts[
                    WickTheorem[Range[rank]]
                ]
            ]
    ]

UnitTensor[___] :=
    (
        Message[UnitTensor::arg];
        $Failed
    )


(* ::Section:: *)
(*Wick Contraction*)


(* Generate all pairings/contractions of the elements of a list. *)
wickContractions[{}] := 1
wickContractions[{a_, b_}] := contr[{a, b}]

wickContractions[list_List] :=
    Block[
        {
            sublist = Delete[list, 1],
            first = list[[1]]
        },
        
        Expand[
            Sum[
                contr[{first, sublist[[i]]}] * wickContractions[Delete[sublist, i]],
                {i, Length @ sublist}
            ]
        ]
    ] //. contr[list1__] contr[list2__] :> contr[list1, list2]


(* Choose any even-cardinality subset to apply Wick's theorem and leave the complement. *)
WickTheorem[list_List] :=
    Expand[
        Plus @@ (
            (ord[Complement[list, Flatten[#]]]*wickContractions[#]) & /@ Prepend[Subsets[list, {2, Length @ list, 2}], {}]
        )
    ]


(* ::Section:: *)
(*Lorentz indices*)


(* Formal Lorentz indices mu1, mu2, ... and nu1, nu2, ... such that the tensor rank can be kept generic.*)
mu[i_Integer] := ToExpression["\[Mu]" <> ToString[i]]
nu[i_Integer] := ToExpression["\[Nu]" <> ToString[i]]


(* ::Section:: *)
(*Partitions*)


PartitionsK[list_,l_]/;Length[list]==l:={{list}}

PartitionsK[list_,l_]:= (*Iterative definition of the partitions of a set in subsets with l elements (Length[list]/l has to be an integer)*)
    Join@@
        Table[
            {x,##} & @@@ PartitionsK[Complement[list, x], l], (*# represent the first argument supplied to a pure function, ## represents a slot of arguments*)
            {x, Subsets[list, {l}, Binomial[Length[list]-1, l-1]]}(*Binomial[Length[list]-1,l-1] is the number of subsets with the first element of list. This avoids repetitions.*)
        ]


(* ::Section:: *)
(*generateDualMetric*)


perpSimplify[exp_]:=
    Block[
        {etaP,localexp=Expand[exp]},

        etaP /: etaP[a_, c_] etaP[c_, b_] := etaP[a, b];
        etaP /: etaP[a_, c_] etaP[b_, c_] := etaP[a, b];
        etaP /: etaP[c_, a_] etaP[c_, b_] := etaP[a, b];
        etaP /: etaP[a_, b_]^2 := $d;
        etaP /: etaP[a_, a_] := $d;

        Simplify[localexp]
    ]


perpPartitions[exp_]:=
    Block[
        {etaP, part, localexp = Expand[exp]},

        etaP[a_, b_] := etaP[1/2][a, b];
        etaP /: etaP[n_][a_, c_] etaP[m_][c_, b_] := etaP[n + m][a, b];
        etaP /: etaP[n_][a_, c_] etaP[m_][b_, c_] := etaP[n + m][a, b];
        etaP /: etaP[n_][c_, a_] etaP[m_][c_, b_] := etaP[n + m][a, b];
        etaP /: etaP[n_][a_, b_]^2 := etaP[2n];
        etaP /: etaP[n_][a_, a_] := etaP[n];

        localexp=part[localexp];

        part[x_Times] := part /@ (List @@ x);
        part[x_Power] := part /@ (ConstantArray[#1, #2]& @@ x);
        part[x_etaP] := List @@ x;

        localexp = ReverseSort @ Flatten[localexp];

        Simplify[localexp]
    ]


generateDualMetric[n_Integer?EvenQ]:=
    Block[
        {
            list,
            metrics,
            first,
            positions,
            partitions = ReverseSortBy[IntegerPartitions[n/2], Length]
        },

        list = Table[ToExpression["m" <> ToString[i]], {i, n}];

        metrics = Times @@@ Apply[etaP, PartitionsK[list, 2], {2}];

        list = metrics[[1]] * metrics;

        list = perpPartitions /@ list;

        positions = Outer[Boole[#1==#2]&, list, partitions, 1];
        first = Flatten[FirstPosition[list, #]& /@ partitions];

        first = 
            perpSimplify[
                TensorProduct[
                    metrics[[first]], 
                    metrics . positions
                ]
            ];

        first = Thread[partitions -> Factor @ LinearSolve[first, PadRight[{1}, PartitionsP[n/2]]]];
        list = list /. first;

        list . metrics
    ]


$dualMetricCacheDir = FileNameJoin[{DirectoryName[$InputFileName], "tmp"}];

storeDualMetric[n_Integer?EvenQ] :=
    Module[
        {lhs, def, file},

        lhs = "{m" <> ToString[2 # - 1] <> "_, m" <> ToString[2 #] <> "_}" & /@ Range[n/2];
        
        lhs   = "dM[" <> StringRiffle[lhs, ", "] <> "]";
        
        def   = lhs <> " :> " <> ToString[generateDualMetric[n], InputForm];

        file  = FileNameJoin[{$dualMetricCacheDir, "dM" <> ToString[n] <> ".m"}];
        
        If[!DirectoryQ[$dualMetricCacheDir], CreateDirectory[$dualMetricCacheDir]];

        Export[file, def, "Text"];

        file
    ]


loadDualMetric[n_Integer?EvenQ] := 
    loadDualMetric[n] =
        Block[
            {file = FileNameJoin[{$dualMetricCacheDir, "dM" <> ToString[n] <> ".m"}]},
            
            If[!FileExistsQ[file], storeDualMetric[n]];
        
            Get[file]
        ]


(* ::Section::Closed:: *)
(*End*)


End[]


(* ::Chapter:: *)
(*Attributes*)


Protect @@ Names["TensorReduction`*"]

EndPackage[]
