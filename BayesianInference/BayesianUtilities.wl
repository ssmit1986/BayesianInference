(* Wolfram Language Package *)

BeginPackage["BayesianUtilities`", {"CompiledFunctionTools`"}]
(* Exported symbols added here with SymbolName::usage *)
passOptionsDown::usage = "passOptionsDown[mainFunction, subFunction, {opts}] passes options down correctly from the main function into a sub function, even when the default options for both functions are different";
quietCheck::usage = "quietCheck[expr, failexr, {msg1, msg2, ...}] combines the functionalities of Quiet and Check";
normalizeData::usage = "normalizeData[data] will center and scale the data and return an association containing the transformed data together with the scaling functions used";
normalizedDataQ::usage = "normalizedDataQ[data] tests if dat is an association produced by normalizedData";
dataNormalForm::usage = "dataNormalForm[data] brings the data to the standard form that is used throughout this package";
dataNormalFormQ::usage = "dataNormalFormQ[data] tests if the data are in the standard format produced by dataNormalForm";
takePosteriorFraction::usage = "takePosteriorFraction[obj, frac] drops the samples with the smallest weights from the posterior distribution, leaving fraction frac of the posterior mass";
logSumExp::usage = "logSumExp[list] calculates Log[Total[Exp[list]]], but in a numerically stable fashion. Does not thread automatically";
$MachineLogZero::usage = "A number that is used to represent the the log of zero probabilities in machine numbers";
checkCompiledFunction::usage = "checkCompiledFunction[cf] will check if cf has calls to MainEvaluate. If it does, it will issue a message and return False. It will return True for CompiledFunctions that pass the test and $Failed for any expression other than a CompiledFunction";
distributionDimension::usage = "distributionDimension[dist] checks the dimension of the domain of dist. Note that it returns {1} for 1D vector distributions like MultinormalDistribution[{{1}}]";
inferenceObject::usage = "A wrapper for an Association containing all relevant information for an inference problem. Can be converted to an Association with Normal";
inferenceObjectQ::usage = "inferenceObjectQ[obj] returns True for valid inference objects";
posteriorDistribution::usage = "posteriorDistribution is a wrapper that typesets large MixtureDistributions";
varsToParamVector::usage = "varsToParamVector[expr, {sym1, sym2...} -> vectorSym] replaces instances of sym_i in expr with Indexed[vectorSym, i]";
expressionToFunction::usage = "expressionToFunction[expr, {sym1, sym2...} -> vectorSym] returns the function Function[vectorSym, varsToParamVector[expr, {sym1, sym2...} -> vectorSym]]";
simplifyLogPDF::usage = "simplifyLogPDF[pdf, assum] Attempts to simplify analytical log probability densities";
numericMatrixQ::usage = "numericMatrixQ[data] tests if data is a numeric matrix";
numericVectorQ::usage = "numericVectorQ[data] tests if data is a numeric vector";
empiricalDistributionToWeightedData::usage = "empiricalDistributionToWeightedData[dist] convert an empirical data distribution to a WeightedData object";
matrixBlockInverse::usage = "matrixBlockInverse[mat, columns] gives Inverse[mat][[columns, colums]]";
inverseMatrixBlockInverse::usage = "inverseMatrixBlockInverse[mat, columns] gives Inverse[Inverse[mat][[columns, colums]]]. This function is faster than inverting the result of matrixBlockInverse[mat, columns]";
$BayesianContexts;

Begin["`Private`"] (* Begin Private Context *)

$MachineLogZero = - 0.99 * $MaxMachineNumber;

$BayesianContexts = Flatten[
    {
        Map[
            {#, # <> "Private`"}&,
            {
                "BayesianUtilities`",
                "BayesianStatistics`",
                "BayesianGaussianProcess`",
                "BayesianVisualisations`"
            }
        ],
        "Global`"
    }
];

numericMatrixQ = Function[MatrixQ[#, NumericQ]];
numericVectorQ = Function[VectorQ[#, NumericQ]];

(* Dummy code to make WL load everything related to MixtureDistribution *)
MixtureDistribution[{1, 2}, {NormalDistribution[], ExponentialDistribution[1]}];

Unprotect[MixtureDistribution];
Format[MixtureDistribution[list1_List, list2_List]] := posteriorDistribution[
    Framed[
        Tooltip[
            StringForm[
                "<< Mixture of `1` distributions >>",
                Length[list1]
            ],
            Grid[
                KeyValueMap[List] @ CountsBy[list2, Head],
                Alignment -> Left
            ]
        ]
    ]
];
Protect[MixtureDistribution];

summaryForm[list_List] := ToString @ StringForm["List (``)", StringRiffle[ToString /@ Dimensions[list], " \[Times] "]];
summaryForm[KeyValuePattern[{"Mean" -> mean_, "StandardError" -> err_}]] := ToString[mean \[PlusMinus] err];
summaryForm[assoc_?AssociationQ] := ToString @ StringForm["Association (`` keys)", Length[assoc]];
summaryForm[dist_?DistributionParameterQ] := With[{dim = distributionDimension[dist]},
    ToString @ Switch[dim,
        1,
            "Distribution (1D, Real)",
        {_Integer},
            StringForm["Distribution (``D, Vector)", First[dim]],
        _,
            $Failed
    ]
];
summaryForm[atom : (_?NumericQ | _String)] := ToString[Short[atom]];
summaryForm[other_] := ToString[StringForm["``[...]", Head[other]]];


Format[inferenceObject[assoc_?AssociationQ]] := With[{
    notMissing = DeleteMissing @ assoc
},
    inferenceObject[
        If[ TrueQ[Length[notMissing] > 0],
            Tooltip[
                #,
                Grid[KeyValueMap[{#1, summaryForm[#2]}&, notMissing], Alignment -> Left]
            ]&,
            Identity
        ] @ Framed[
            StringForm[
                "<< `1` defined properties >>",
                Length[notMissing]
            ]
        ]
    ]
];

inferenceObject /: Normal[inferenceObject[assoc_?AssociationQ]] := assoc;
inferenceObject /: Append[inferenceObject[assoc_?AssociationQ], elem_] :=  inferenceObject @ Append[assoc, elem];
inferenceObject /: Prepend[inferenceObject[assoc_?AssociationQ], elem_] := inferenceObject @ Prepend[assoc, elem]
inferenceObject /: FailureQ[inferenceObject[$Failed]] := True;

inferenceObject[inferenceObject[assoc_?AssociationQ]] := inferenceObject[assoc];
inferenceObject[first_, rest__] := inferenceObject[first];
inferenceObject[assoc_?AssociationQ]["Properties"] := Sort @ Append[Keys[assoc], "Properties"];
inferenceObject[assoc_?AssociationQ][prop : (_String | {__String} | All)..] := assoc[[prop]];

inferenceObjectQ[inferenceObject[assoc_?AssociationQ]] := True;
inferenceObjectQ[___] := False;

SetAttributes[quietCheck, {HoldAll}];
quietCheck[expr_, failexpr_, msgs : {__MessageName}] :=
    Quiet[
        Check[
            expr,
            failexpr,
            msgs
        ],
        msgs
    ];
quietCheck[expr_, failexpr_] :=
    Quiet[
        Check[
            expr,
            failexpr
        ]
    ];

passOptionsDown[functionName_Symbol, {opts : OptionsPattern[]}] := passOptionsDown[functionName, functionName, {opts}];

passOptionsDown[mainFunctionName_Symbol, subFunctionName_Symbol, {opts : OptionsPattern[]}] :=
    FilterRules[
        Thread[
            Rule[
                Options[mainFunctionName][[All, 1]],
                OptionValue[
                    mainFunctionName,
                    Join[
                        {opts},
                        Options[mainFunctionName]
                    ],
                    Options[mainFunctionName][[All, 1]]
                ]
            ]
        ],
        Options[subFunctionName]
    ];

xLogx := Compile[{
    {x, _Real}
},
    If[ x == 0. || x == 1.,
        0.,
        x * Log[x]
    ],
    RuntimeAttributes -> {Listable}
];

xLogy := Compile[{
    {x, _Real},
    {y, _Real}
},
    Which[
        x == 0.,
            0.,
        y == 0.,
            - Sign[x] * $MaxMachineNumber,
        True,
            x * Log[y]
    ],
    RuntimeAttributes -> {Listable}
];

dataNormalForm[miss_Missing] := miss;
dataNormalForm[data_List?numericMatrixQ] := data;
dataNormalForm[data_List?numericVectorQ] := List /@ data;
dataNormalForm[data : {__Rule}] := dataNormalForm[Thread[data, Rule]];
dataNormalForm[in_List -> out_List] := With[{
    input = dataNormalForm[in],
    output = dataNormalForm[out]
},
    (input -> output) /; Length[input] === Length[output]
];
dataNormalForm[___] := $Failed;
dataNormalFormQ = Function[
    Or[
        numericMatrixQ[#],
        Head[#] === Rule && AllTrue[#, numericMatrixQ]
    ]
]

normalizeData[data : {__Rule}] := normalizeData[
    Developer`ToPackedArray[data[[All, 1]]],
    Developer`ToPackedArray[data[[All, 2]]]
];

normalizeData[data : Rule[_List, _List]] := normalizeData[data[[1]], data[[2]]];

normalizeData[dataIn_List, dataOut_List] := AssociationThread[
    {"Input", "Output"},
    normalizeData /@ {dataIn, dataOut}
];

normalizeData[dataSequence : Repeated[_List, {3, Infinity}]] := AssociationThread[
    Range[Length[{dataSequence}]],
    normalizeData /@ {dataSequence}
];

normalizeData[data_List?numericVectorQ] := normalizeData[dataNormalForm[data]];

normalizeData[data_List?numericMatrixQ] := With[{
    fe = FeatureExtraction[data, "StandardizedVector"]
},
    With[{
        inv = Function[
            fe[#, "OriginalData"]
        ]
    },
        <|
            "NormalizedData" -> Developer`ToPackedArray[fe[data]],
            "Function" -> fe,
            "InverseFunction" -> inv
        |>
    ]
];

normalizedDataQ = With[{
    test = Function[
        And[
            AssociationQ[#],
            SubsetQ[Keys[#], {"NormalizedData", "Function", "InverseFunction"}],
            numericMatrixQ[#["NormalizedData"]]
        ]
    ]
},
    Function[
        Or[
            test[#],
            And[
                AssociationQ[#],
                Sort @ Keys[#] === Sort @ {"Input", "Output"},
                AllTrue[#, test]
            ]
        ]
    ]
];

takePosteriorFraction[inferenceObject[assoc_?AssociationQ], rest___] := inferenceObject @ takePosteriorFraction[assoc, rest];

takePosteriorFraction[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&), 1] := MapAt[
    SortBy[-#CrudePosteriorWeight &],
    result,
    {"Samples"}
];

takePosteriorFraction[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&), frac_?NumericQ] /; 0 <= frac < 1 := Module[{
    count = 0
},
    MapAt[
        Function[ samples,
            TakeWhile[
                SortBy[samples, -#CrudePosteriorWeight &],
                Function[
                    With[{
                        boole = count <= frac
                    },
                        count += #CrudePosteriorWeight;
                        boole
                    ]
                ]
            ]
        ],
        result,
        {"Samples"}
    ]
];

logSumExp = Composition[
    Compile[{
        {list, _Real, 1}
    },
        Module[{
            max = Max[list]
        },
            Plus[
                max,
                Log @ Total[
                    Exp[Subtract[list, max]]
                ]
            ] 
        ]
    ],
    Select[NumericQ] (* Get rid of -Infinity *)
];

checkCompiledFunction::mainEval = "CompiledFunction `1` has calls to MainEvaluate and may not perform optimally";
checkCompiledFunction[cf_CompiledFunction, name : _ : Automatic] /; StringContainsQ[CompilePrint[cf], "MainEvaluate"] := (
    Message[checkCompiledFunction::mainEval, Replace[name, Automatic :> Short[cf]]];
    False
);
checkCompiledFunction[_CompiledFunction, ___] := True;
checkCompiledFunction[___] := $Failed;

randomDomainPointDistribution[
    list : {{_?NumericQ | DirectedInfinity[-1], _?NumericQ | DirectedInfinity[1]}..},
    width : (_?NumericQ) : 100
] := TruncatedDistribution[
    list,
    ProductDistribution[{CauchyDistribution[0, width], Length[list]}]
];

distributionDimension[dist_?DistributionParameterQ] := With[{dom = DistributionDomain[dist]},
    Switch[ dom,
        {__},
            {Length[dom]},
        _Interval,
            1,
        _,
            $Failed
    ]
];

varsToParamVector::duplicateSym = "Warning: symbol `1` already present in expression";
varsToParamVector[expr_, rules : {({__Symbol} -> (_Symbol | _Slot))..}] := Fold[
    varsToParamVector[#1, #2]&,
    expr,
    rules
];

varsToParamVector[expr_, (vars : {__Symbol}) -> (paramVectorSymbol : (_Symbol | _Slot))] := (
    If[ !FreeQ[expr, paramVectorSymbol],
        Message[varsToParamVector::duplicateSym, paramVectorSymbol]
    ];
    ReplaceAll[
        expr,
        Thread[
            vars -> Table[
                Indexed[paramVectorSymbol, i],
                {i, Length[vars]}
            ]
        ]
    ]
);

expressionToFunction[expr_, rule_Rule, attributes___] := expressionToFunction[expr, {rule}, attributes];

expressionToFunction[expr_, rules : {({__Symbol} -> _Symbol)..}, attributes___] := Function[
    Evaluate @ rules[[All, 2]],
    Evaluate @ varsToParamVector[expr, rules],
    {attributes}
];

expressionToFunction[expr_, rules : {({__Symbol} -> _Slot)..}, attributes___] := Function[
    Null,
    Evaluate @ varsToParamVector[expr, rules],
    {attributes}
];

simplifyLogPDF[logPDF_, assum_] := PowerExpand[ (* PowerExpand helps converting expressions like Log[1. / x] to -Log[x]*)
    FullSimplify[
        logPDF,
        assum
    ],
    Assumptions -> assum
];

empiricalDistributionToWeightedData[dist_DataDistribution /; dist["Type"] === EmpiricalDistribution] := WeightedData[
    Replace[dist["Domain"], mat_?MatrixQ :> Transpose[mat]],
    dist["Weights"]
];

matrixBlockInverse[
    mat_?SquareMatrixQ,
    columns : {__Integer}
] /; DuplicateFreeQ[columns] && Max[columns] <= Length[mat] && MatrixQ[mat, NumericQ] := LinearSolve[
    inverseMatrixBlockInverse[mat, columns],
    IdentityMatrix[Length[columns]]
];

inverseMatrixBlockInverse[
    mat_?SquareMatrixQ,
    columns : {__Integer}
] /; DuplicateFreeQ[columns] && Max[columns] <= Length[mat] && MatrixQ[mat, NumericQ] := Block[{
    droppedColumns = Complement[Range[Length[mat]], columns],
    splitMatrix
},
    splitMatrix = Table[
        mat[[i, j]],
        {i, {droppedColumns, columns}},
        {j, {droppedColumns, columns}}
    ];
    Subtract[
        splitMatrix[[2, 2]],
        splitMatrix[[2, 1]] . LinearSolve[splitMatrix[[1, 1]], splitMatrix[[1, 2]]]
    ]
];

End[] (* End Private Context *)

EndPackage[]