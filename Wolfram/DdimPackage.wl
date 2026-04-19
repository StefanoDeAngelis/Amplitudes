(* ::Package:: *)

BeginPackage["DdimPackage`", {"YoungSymm`","DdimVariables`"}]


(* ::Section:: *)
(*Messages*)


MassDimension::usage = "MassDimension[expr] gives the mass dimension of expr, where the mass dimension of a Momentum is 1, of a FieldStr is 1, of a Riemann is 2, of a Mandelstam is 2, and of a Mass is 1. \n If expr is a sum of terms with different mass dimensions, MassDimension will issue a warning and return a subset of terms which have the same mass dimension."

RelabelDummies::usage = "..."
Relabel::usage = "..."

ScalarProductsToIndices::usage = "..."
(*ToScalarProducts::usage = "..."*)
ToTrace::usage = "..."

SetMasses::usage = "..."
FixMasses::usage = "..."
ZeroMasses::usage = "..."
ClearMasses::usage = "..."

LorentzGauge::usage = "..."
FixedScalarProducts::usage = "..."

DDerivative::usage = "..."

CombinePolarisations::usage = "..."
DecombinePolarisations::usage = "..."

DecomposeFTraces::usage = "..."


(* ::Section:: *)
(*D-dimensional Functions*)


Begin["`Private`"]


(* ::Text:: *)
(*TODO:*)


(*-Problem: e.g. latin indices after 26 give errors. We should define some sort of index mod 26 which adds a number to the letter after 26. {a,b...z,a1,b1,...z1,a2,...}*)
(*          more generally, we need numbered indices, also as an option*)
(*-Feature: DDerivative with respect to a Momentum/EpsilonPol inside FieldStr and for FTraces*)
(*-Feature: make ToTrace faster with UpValues instead of replacement rules*)
(*-Feature: function which open FieldStr into Momentum and EpsilonPol*)
(*-Feature: clear function for LorentzGauge and FixedScalarProducts*)

(* Done! (Under debugging) FromDotIndices has to be rewritten to take into account the changes for the momenta and epsilon polarizations. An additional feature is needed for FTrace.*)


(* ::Subsection::Closed:: *)
(*MassDimension*)


Attributes[MassDimension]={Listable};

MassDimension[FieldStr[__]]:=1
MassDimension[Riemann[__]]:=2
MassDimension[Momentum[___]]:=1
MassDimension[FTrace[a_,x_,b_]]:=MassDimension[a]+MassDimension[b]+Length[x]
MassDimension[FTrace[x_List]]:=Length[x]
MassDimension[Mass[_]]:=1
MassDimension[Mandelstam[__]]:=2
MassDimension[DotProduct[a_,b_]]:=MassDimension[a]+MassDimension[b]

MassDimension[exp_Times] := Plus @@ (MassDimension /@ List @@ exp)

MassDimension[Power[expr_, expo_]] := expo * MassDimension[expr]

MassDimension[exp_Plus] := 
	Block[{dims = MassDimension /@ (List @@ exp)},
		dims = DeleteDuplicates[dims];
		If[
			Length[dims] > 1,
			Message[MassDimension::hom, exp],
			Return[dims[[1]]]
		]
	]

MassDimension::hom = "`1` is not homogeneous in the mass dimension";

MassDimension[x_] := 0


(* ::Subsection::Closed:: *)
(*Relabel Dummies*)


Options[RelabelDummies] = {"Indices" -> "Greek"};

RelabelDummies[OptionsPattern[]][x_Plus] := Plus@@(RelabelDummies["Indices"->OptionValue["Indices"]][#]&/@(List @@ x))

RelabelDummies[OptionsPattern[]][exp_] :=
	Module[{dummies, indices, newdummies},
		dummies = (*Join[Cases[exp, HoldPattern[Momentum[_,h_]] :> h, \[Infinity]], Cases[exp, HoldPattern[EpsilonPol[_,h__]] :> h, \[Infinity]], Cases[exp, HoldPattern[FieldStr[_,h__]] :> h,\[Infinity]], Cases[exp, HoldPattern[Riemann[_,h__]] :> h, \[Infinity]]];*)
			Join[
				Cases[
					exp, 
					HoldPattern[EpsilonPol[_,h__]] | HoldPattern[FieldStr[_,h__]] | HoldPattern[Riemann[_,h__]] :> h,
					\[Infinity]
				],
				Cases[
					exp,
					HoldPattern[Momentum[_,h_]] :> h,
					\[Infinity]
				]
			];
		indices = DeleteDuplicates[dummies];
		dummies = Select[Tally[dummies], #[[2]] > 1&][[All, 1]];
		newdummies =
			Table[
				ToExpression @
					FromCharacterCode[
						If[OptionValue["Indices"] == "Greek",
							944 + i,
							96 + i
						]
					]
				,
				{i, Length @ indices}
			];
		newdummies = Complement[newdummies,Complement[indices, dummies]][[;;Length@dummies]];
		YoungSymm`ReLabel[exp, dummies, newdummies]
	]



(* ::Subsection::Closed:: *)
(*Relabel*)


Options[Relabel] = {"Indices" -> "Greek"};

Relabel[OptionsPattern[]][x_Plus, n_:0] := Plus @@ (Relabel["Indices" -> OptionValue["Indices"]][#, n]& /@ (List @@ x))

Relabel[OptionsPattern[]][exp_, n_:0] :=
	Module[{dummies, indices, newindices},
		dummies =(*Join[Cases[exp, HoldPattern[Momentum[_,h_]] :> h, \[Infinity]], Cases[exp, HoldPattern[EpsilonPol[_,h__]]:> h, \[Infinity]], Cases[exp, HoldPattern[FieldStr[_,h__]]:> h, \[Infinity]], Cases[exp, HoldPattern[Riemann[_,h__]] :> h, \[Infinity]]];*)
			Join[
				Cases[
					exp,
					HoldPattern[EpsilonPol[_,h__]] | HoldPattern[FieldStr[_,h__]] | HoldPattern[Riemann[_,h__]] | HoldPattern[Metric[h__]] :> h,
					\[Infinity]
				],
				Cases[
					exp,
					HoldPattern[Momentum[_,h_]] :> h,
					\[Infinity]
				]
			];
		indices = DeleteDuplicates[dummies];
		dummies = Select[Tally[dummies], #[[2]] > 1&][[All, 1]];
		newindices =
			Table[
				ToExpression @
					FromCharacterCode[
						If[
							OptionValue["Indices"] == "Greek",
							944 + i + n,
							96 + i + n
						]
					],
				{i, Length @ indices}
			];
		indices = SortBy[indices, MemberQ[dummies, #]&];
		YoungSymm`ReLabel[exp, indices, newindices]
	]



(* ::Subsection::Closed:: *)
(*ToTrace*)


(*ToScalarProducts[exp_Plus] := ToScalarProducts /@ exp

ToScalarProducts[exp_Times] /; !(Denominator[exp]==1) := ToScalarProducts[Numerator[exp]]/Denominator[exp]

ToScalarProducts[exp_]:=
	Block[
		{local,Momentum,EpsilonPol},
		
		Momentum /: Momentum[x_,a_] Momentum[y_,a_] := DotProduct[Momentum[x],Momentum[y]];
		Momentum /: Momentum[x_,a_] EpsilonPol[y_,a_] := DotProduct[Momentum[x],EpsilonPol[y]];
		EpsilonPol /: EpsilonPol[x_,a_] EpsilonPol[y_,a_] := DotProduct[EpsilonPol[x],EpsilonPol[y]];
		
		local=DecombinePolarisations[exp];
		
		Return[local]
	]*)


ToTrace[exp_Plus] := ToTrace /@ exp

(*ToTrace[Times[a___, b_, c___]] /; MatchQ[b, Power[_, _ ? (# < 0&)]] := b * ToTrace[Times[a, c]]*)
ToTrace[exp_Times] /; !(Denominator[exp]==1) := ToTrace[Numerator[exp]]/Denominator[exp]

ToTrace[exp_] :=
	ReplaceRepeated[
		ReplaceRepeated[
			ReplaceRepeated[
				DecombinePolarisations[exp] // Expand,
					{f_[x_,a_] g_[y_,a_] /; MatchQ[f, EpsilonPol| Momentum] && MatchQ[g, EpsilonPol | Momentum ] :> DotProduct[f[x], g[y]]}
				],
			{
				f_[x_,a_] FieldStr[y_,a_, b_] /; MatchQ[f, EpsilonPol | Momentum] :> FTrace[f[x], {FieldStr[y]}][b],
				f_[x_,b_] FieldStr[y_,a_, b_] /; MatchQ[f, EpsilonPol| Momentum] :> -FTrace[f[x], {FieldStr[y]}][a],
				
				FieldStr[y_,a_, b_]^2 :> - FTrace[{FieldStr[y],FieldStr[y]}],
				
				FTrace[x_, y_][a_] FieldStr[z_,a_, b_] :> FTrace[x, Append[y, FieldStr[z]]][b],
				FTrace[x_, y_][b_] FieldStr[z_,a_,b_] :> -FTrace[x, Append[y, FieldStr[z]]][a],
				
				f_[x_,a_] FTrace[y_, z_List][a_] /; MatchQ[f, EpsilonPol| Momentum] :> FTrace[y, z, f[x]],
				
				FTrace[x_, z1_List][a_] FTrace[y_, z2_List][a_] :> (-1) ^ (Length[z2]) FTrace[x, Join[z1, Reverse @ z2], y],
				FTrace[x_, y_][a_]^2 :> (-1)^Length[y] FTrace[x,Join[y,Reverse@y],x]
			}
		],
		{
			FieldStr[x_,a_, b_] FieldStr[y_,b_, c_] :> FTrace[FieldStr[x], FieldStr[y]][a, c],
			FieldStr[x_,a_, c_] FieldStr[y_,b_, c_] :> -FTrace[FieldStr[x], FieldStr[y]][a, b],
			
			FTrace[x__][a_, b_] FieldStr[y_, b_, c_] :> FTrace[x, FieldStr[y]][a, c],
			FTrace[x__][a_, c_] FieldStr[y_, b_, c_] :> -FTrace[x, FieldStr[y]][a, b],
			FTrace[x__][c_, a_] FieldStr[y_, b_, c_] :> FTrace[FieldStr[y], x][b, a],
			HoldPattern[FTrace[x__][c_, a_] FieldStr[y_, c_, b_]] :> -FTrace[FieldStr[y], x][b, a],
			
			FTrace[x__][a_, b_] FTrace[y__][b_, c_] :> FTrace[x, y][a, c],
			
			FTrace[x__][a_, c_] FTrace[y__][b_, c_] :> (-1) ^ (Length[{y}]) *FTrace[x, Sequence @@ Reverse @ {y}][a, b],
			
			FTrace[x__][a_, a_] :> FTrace[{x}]
		}
	]



(* ::Subsection::Closed:: *)
(*From Scalar Products To Indices*)


Options[ScalarProductsToIndices] = {"Indices" -> "Greek"};

ScalarProductsToIndices[OptionsPattern[]][exp_Plus, n_:0] := Plus @@ (ScalarProductsToIndices["Indices" -> OptionValue["Indices"]][#, n]& /@ (List @@ exp))

ScalarProductsToIndices[OptionsPattern[]][exp_, n_:0] :=
	Block[{Momentum,EpsilonPol,FieldStr,Riemann,Metric},
		Momentum[a_][b_]:=Momentum[a,b];
		EpsilonPol[a_][b_]:=EpsilonPol[a,b];
		FieldStr[a_][b__]:=FieldStr[a,b];
		Riemann[a_][b__]:=Riemann[a,b];
		Times@@
			Module[{i = 1 + n, j, num = Numerator[exp]},
				i = i + Length @
					Cases[
						num,
						Momentum[_,h__] | EpsilonPol[_,h__] | FieldStr[_,h__] | Riemann[_,h__] | Metric[h__] :> h,
						\[Infinity]
					];
				If[
					MatchQ[
						#,
						DotProduct[_, _]
					],
					If[
						OptionValue["Indices"] == "Greek",
						#[[1]][ToExpression@FromCharacterCode[944 + i]] #[[2]][ToExpression @ FromCharacterCode[944 + (i++)]],
						#[[1]][ToExpression @ FromCharacterCode[96 + i]] #[[2]][ToExpression @ FromCharacterCode[96 + (i++)]]
					],
					If[
						MatchQ[
							#,
							FTrace[_, _, _]
						],
						If[
							OptionValue["Indices"] == "Greek",
							#[[1]][ToExpression@FromCharacterCode[944 + i]] Product[fields[ToExpression@FromCharacterCode[944 + (i++)],ToExpression@FromCharacterCode[944 + i]],{fields,#[[2]]}]#[[3]][ToExpression @ FromCharacterCode[944 + (i++)]],
							#[[1]][ToExpression@ FromCharacterCode[96 + i]] Product[fields[ToExpression@FromCharacterCode[96 + (i++)], ToExpression@FromCharacterCode[96 + i]], {fields,#[[2]]}]#[[3]][ToExpression @ FromCharacterCode[96 + (i++)]]
						],
						If[
							MatchQ[
								#,
								FTrace[_]
							],
							j=i;
							If[
								OptionValue["Indices"] == "Greek",
								Product[fields[ToExpression@FromCharacterCode[944 + (i++)],ToExpression@FromCharacterCode[944 + i]],{fields,#[[1]]}],
								Product[fields[ToExpression@FromCharacterCode[96 + (i++)], ToExpression@FromCharacterCode[96 + i]], {fields,#[[1]]}]
							]*
							If[
								OptionValue["Indices"] == "Greek",
								Metric[ToExpression@FromCharacterCode[944 + (i++)],ToExpression@FromCharacterCode[944 + j]],
								Metric[ToExpression@FromCharacterCode[96 + (i++)],ToExpression@FromCharacterCode[96 + j]]
							]
							,
						#
						]
					]
				]&/@ 
					(Flatten@
						Replace[
							If[Head[#] === Times, List @@ #, {#}] &@ Relabel["Indices" -> OptionValue["Indices"]][num, n],
							Power[x_(*?(MatchQ[Head[#],DotProduct]&)*), y_] :> ConstantArray[x, y] /; IntegerQ[y] && y>0,
							{1}
						]
					)
				] / Denominator[exp]
	]


(* ::Subsection::Closed:: *)
(*Combine Polarisation Vectors*)


CombinePolarisations[exp_] :=
	ReplaceRepeated[
		exp,
		{
			EpsilonPol[a_, \[Mu]_] EpsilonPol[a_,\[Nu]_] :> EpsilonPol[a, \[Mu], \[Nu]],
			FieldStr[a_, \[Mu]_, \[Nu]_] FieldStr[a_, \[Rho]_, \[Sigma]_] :> Riemann[a, \[Mu], \[Nu], \[Rho], \[Sigma]],
			FieldStr[a_, \[Mu]_, \[Nu]_]^2 :> Riemann[a, \[Mu], \[Nu], \[Mu], \[Nu]]
		}
	]

DecombinePolarisations[exp_] :=
	ReplaceRepeated[
		exp, 
		{
			EpsilonPol[a_, \[Mu]_, \[Nu]_] :>EpsilonPol[a, \[Mu]] EpsilonPol[a, \[Nu]],
			Riemann[a_, \[Mu]_, \[Nu]_, \[Rho]_, \[Sigma]_] :> FieldStr[a, \[Mu], \[Nu]] FieldStr[a, \[Rho], \[Sigma]]
		}
	]



(* ::Subsection::Closed:: *)
(*Masses*)


(* ::Subsubsection::Closed:: *)
(*SetMasses*)


SetMasses[masses_List] :=
	(
		Unprotect[DotProduct];
		Set @@@ Transpose[{(DotProduct[Momentum[#], Momentum[#]]& /@ masses), (Mass[#]^2 &/@masses)}];
		Protect[DotProduct];
	)


(* ::Subsubsection::Closed:: *)
(*FixMasses*)


FixMasses[particles_List,masses_List] /; Length[particles] == Length[masses] :=
	(
		Unprotect[Mass];
		Set @@@ Transpose @ {Mass /@ particles, masses};
		Protect[Mass];
	)


(* ::Subsubsection::Closed:: *)
(*ZeroMasses*)


ZeroMasses[masses_List] :=
	(
		Unprotect[Mass];
		Set @@@ Transpose @ {Mass /@ masses, Table[0, Length@masses]};
		Protect[Mass];
	)



(* ::Subsubsection::Closed:: *)
(*ClearMasses*)


ClearDownValues[f_] := DownValues[f] = DeleteCases[DownValues[f], _ ? (FreeQ[First[#], Pattern]&)]

ClearMasses[] :=
	(
		Unprotect[Mass, DotProduct];
		ClearDownValues[Mass];
		ClearDownValues[DotProduct];
		Protect[Mass, DotProduct];
	)



(* ::Subsection::Closed:: *)
(*Fix scalar products*)


(* ::Subsubsection::Closed:: *)
(*Lorentz gauge*)


LorentzGauge[bosons_List]:=
	(
		Unprotect[DotProduct,FTrace];
		Table[
			{
				DotProduct[EpsilonPol[x], Momentum[x]]=0,
				DotProduct[EpsilonPol[-x], Momentum[x]]=0,
				FTrace/:FTrace[EpsilonPol[x], {FieldStr[x],y___},z_]:=0,
				FTrace/:FTrace[Momentum[x], {FieldStr[x],y___},z_]:=0,
				FTrace/:FTrace[z_, {y___,FieldStr[x]},Momentum[x]]:=0,
				FTrace/:FTrace[z_, {y___,FieldStr[x]},EpsilonPol[x]]:=0,
				FTrace/:FTrace[z1_, {y1___,FieldStr[x],FieldStr[x],y2___},z2_]:=0
			},
			{x,bosons}];
		Protect[DotProduct,FTrace];
	)


(* ::Subsubsection::Closed:: *)
(*Fix scalar products*)


FixedScalarProducts[rules__?(MatchQ[Head[#],Rule]&)]:=
	(
		Unprotect[DotProduct,FTrace];
		Set@@@{rules};
		Protect[DotProduct,FTrace];
	)


(* ::Subsection::Closed:: *)
(*DDerivative*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary function: StripoffIndex*)


StripoffIndex[p_]:=p[[;;1]]


(* ::Subsubsection::Closed:: *)
(*DDerivative*)


(*DDerivative[exp_,,p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=If[Echo@FreeQ[exp,Echo@Head[p]],0]*)
DDerivative[DotProduct[p1_,p2_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=(If[MatchQ[p1,StripoffIndex[p]],Append[p2,p[[2]]],0]+If[MatchQ[p2,StripoffIndex[p]],Append[p1,p[[2]]],0])
DDerivative[Momentum[x_,a_],Momentum[x_,b_]]:=Metric[a,b]
DDerivative[EpsilonPol[x_,a_],EpsilonPol[x_,b_]]:=Metric[a,b]
DDerivative[sum_Plus,p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=Plus@@(DDerivative[#,p]&/@List@@sum)
DDerivative[Times[a_,b_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=DDerivative[a,p]*Times[b]+a*DDerivative[b,p]
DDerivative[Power[a_,b_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=b*Power[a,b-1]*DDerivative[a,p]+Log[a]*Power[a,b]*DDerivative[b,p]
DDerivative[Log[a_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=1/a*DDerivative[a,p]
DDerivative[Sin[a_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=Cos[a]*DDerivative[a,p]
DDerivative[Cos[a_],p_?(MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)]:=-Sin[a]*DDerivative[a,p]
DDerivative[exp_, p_ ? (MatchQ[#, Momentum[_,_]  | EpsilonPol[_,_]]&)]:=0
(*DDerivative[exp_,,p_?(!MatchQ[#,Momentum[_,_]|EpsilonPol[_,_]]&)] define an error message*)


(* ::Subsection:: *)
(*DecomposeFTraces*)


DecomposeFTraces[exp_]:=(*function pasted from the notebook Stefano/gravity/leading_order/tree_decomposition.nb*)
	Block[{FTrace,localexp=exp},

		FTrace[{FieldStr[k1_],z__}]:=-FTrace[Momentum[k1],{z},EpsilonPol[k1]]+FTrace[EpsilonPol[k1],{z},Momentum[k1]];
		
		(*FTrace[{z__,FieldStr[k1_]}]:=FTrace[Momentum[k1],{z},EpsilonPol[k1]]-FTrace[EpsilonPol[k1],{z},Momentum[k1]];*)
	
		FTrace[x_,{FieldStr[k1_]},y_]:=DotProduct[x,Momentum[k1]]DotProduct[y,EpsilonPol[k1]]-DotProduct[x,EpsilonPol[k1]]DotProduct[y,Momentum[k1]];
		FTrace[x_,{FieldStr[k1_],z__},y_]:=DotProduct[x,Momentum[k1]] FTrace[EpsilonPol[k1],{z},y]-DotProduct[x,EpsilonPol[k1]]FTrace[Momentum[k1],{z},y];
		(*FTrace[x_,{z__,FieldStr[k1_]},y_]:=-FTrace[x,{z},EpsilonPol[k1]]DotProduct[Momentum[k1],y]+FTrace[x,{z},Momentum[k1]]DotProduct[EpsilonPol[k1],y];*)
		
		Return[localexp]
	]
	
DecomposeFTraces[exp_,list_]:=
	Block[{FTrace,localexp=exp},

		FTrace[{z1__,FieldStr[k1_]}]/;MemberQ[list,k1]:=-FTrace[Momentum[k1],{z1},EpsilonPol[k1]]+FTrace[EpsilonPol[k1],{z1},Momentum[k1]];
		FTrace[{FieldStr[k1_],z2__}]/;MemberQ[list,k1]:=-FTrace[Momentum[k1],{z2},EpsilonPol[k1]]+FTrace[EpsilonPol[k1],{z2},Momentum[k1]];
		FTrace[{z1___,FieldStr[k1_],z2___}]/;MemberQ[list,k1]:=-FTrace[Momentum[k1],{z2,z1},EpsilonPol[k1]]+FTrace[EpsilonPol[k1],{z2,z1},Momentum[k1]];
	
		(*FTrace[x_,{FieldStr[k1_]},y_]/;MemberQ[list,k1]:=DotProduct[x,Momentum[k1]]DotProduct[y,EpsilonPol[k1]]-DotProduct[x,EpsilonPol[k1]]DotProduct[y,Momentum[k1]];*)
		(*FTrace[x_,{FieldStr[k1_],z___},y_]/;MemberQ[list,k1]:=DotProduct[x,Momentum[k1]] FTrace[EpsilonPol[k1],{z},y]-DotProduct[x,EpsilonPol[k1]]FTrace[Momentum[k1],{z},y];
		FTrace[x_,{z___,FieldStr[k1_]},y_]/;MemberQ[list,k1]:=-FTrace[x,{z},EpsilonPol[k1]]DotProduct[Momentum[k1],y]+FTrace[x,{z},Momentum[k1]]DotProduct[EpsilonPol[k1],y];*)
		FTrace[x_,{z1___,FieldStr[k_],z2___},y_]/;MemberQ[list,k]:=FTrace[EpsilonPol[k], {z2}, y]*FTrace[x, {z1}, Momentum[k]] - FTrace[x, {z1}, EpsilonPol[k]]*FTrace[Momentum[k], {z2}, y];
		
		FTrace[x_,{},y_]:=DotProduct[x,y];
		
		Return[localexp]
	]


(* ::Subsection:: *)
(*End*)


End[]


(* ::Section:: *)
(*Attributes*)


Protect @@ Names["DdimPackage`*"]

EndPackage[]


(* If[
	ValueQ[Global`$DdimAddOn] && MemberQ[Flatten @ {Global`$DdimAddOn}, "TensorReduction"],
	Needs[
		"TensorReduction`",
		FileNameJoin[{DirectoryName[$InputFileName], "TensorReduction.wl"}]
	];
	If[
		FreeQ[$ContextPath, "TensorReduction`"],
		AppendTo[$ContextPath, "TensorReduction`"]
	]
] *)
