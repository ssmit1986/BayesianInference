(* Wolfram Language Package *)

BeginPackage["BayesianUtilities`", {"CompiledFunctionTools`"}]
(* Exported symbols added here with SymbolName::usage *)
passOptionsDown::usage = "passOptionsDown[mainFunction, subFunction, {opts}] passes options down correctly from the main function into a sub function, even when the default options for both functions are different";
quietCheck::usage = "quietCheck[expr, failexr, {msg1, msg2, ...}] combines the functionalities of Quiet and Check";
normalizeData;
takePosteriorFraction;
$BayesianContexts;
logSumExp;
$MachineLogZero;
checkCompiledFunction::usage = "checkCompiledFunction[cf] will check if cf has calls to MainEvaluate. If it does, it will issue a message and return False. It will return True for CompiledFunctions that pass the test and $Failed for any expression other than a CompiledFunction";
distributionDimension;
inferenceObject;
posteriorDistribution;

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

(* Dummy code to make WL load everything related to MixtureDistribution *)
MixtureDistribution[{1, 2}, {NormalDistribution[], ExponentialDistribution[1]}];

Unprotect[MixtureDistribution];
Format[MixtureDistribution[list1_List, list2_List]] := posteriorDistribution[
    StringForm[
        "Mixture of `1` distributions",
        Length[list1]
    ]
];
Protect[MixtureDistribution];

summaryForm[list_List] := ToString @ StringForm["List (``)", StringRiffle[ToString /@ Dimensions[list], " \[Times] "]];
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
inferenceObject /: FailureQ[inferenceObject[$Failed]] := True;

inferenceObject[inferenceObject[assoc_?AssociationQ]] := inferenceObject[assoc];
inferenceObject[first_, rest__] := inferenceObject[first];
inferenceObject[assoc_?AssociationQ]["Properties"] := Sort @ Append[Keys[assoc], "Properties"];
inferenceObject[assoc_?AssociationQ][prop : (_String | {__String})] := assoc[[prop]];


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

normalizeData[data : {__Rule}, opts : OptionsPattern[]] := normalizeData[
    Developer`ToPackedArray[data[[All, 1]]],
    Developer`ToPackedArray[data[[All, 2]]],
    opts
];

normalizeData[data : Rule[_List, _List], opts : OptionsPattern[]] := normalizeData[data[[1]], data[[2]], opts];

normalizeData[dataIn_List, dataOut_List, opts : OptionsPattern[]] := AssociationThread[
    {"Input", "Output"},
    normalizeData[#, opts]& /@ {dataIn, dataOut}
];

normalizeData[dataSequence : Repeated[_List, {3, Infinity}], opts : OptionsPattern[]] := AssociationThread[
    Range[Length[{dataSequence}]],
    normalizeData[#, opts]& /@ {dataSequence}
];

normalizeData[data_?(MatrixQ[#, NumericQ] || VectorQ[#, NumericQ]&), opts : OptionsPattern[]] := With[{
    mean = First[OptionValue["StandardizationFunctions"], Mean] @ data,
    std = Quiet[
        Replace[
            Last[OptionValue["StandardizationFunctions"], StandardDeviation] @ data,
            _?PossibleZeroQ -> 1,
            {-1}
        ],
        "Packing"
    ]
},
    With[{
        fun = If[ MatrixQ[data]
            ,
            Function[
                Transpose[
                    Divide[Subtract[Transpose[#], mean], std]
                ]
            ]
            ,
            Function[
                Divide[Subtract[#, mean], std]
            ]
        ],
        inv = If[ MatrixQ[data]
            ,
            Function[
                Transpose[
                    Plus[Times[Transpose[#], std], mean]
                ]
            ]
            ,
            Function[
                Plus[Times[#, std], mean]
            ]
        ]
    },
        <|
            "NormalizedData" -> Developer`ToPackedArray[fun[data]],
            "Function" -> fun,
            "InverseFunction" -> inv
        |>
    ]
];
Options[normalizeData] = {
    "StandardizationFunctions" -> {Mean, StandardDeviation}
};

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

regressionLogLikelihoodFunction[
    (inputData : {__}) -> (outputData : {__}),
    regressionFormula_,
    errorDistribution_,
    locationVariables  : {__Symbol},
    regressionParameters : {__Symbol},
    opts : OptionsPattern[]
] := Assuming[
    OptionValue[Assumptions]
    ,
    Module[{
        residuals = Simplify[
            outputData - Function[locationVariables, regressionFormula] /@ inputData
        ],
        locationIndependentErrorsQ = FreeQ[errorDistribution, Alternatives @@ locationVariables],
        errors
    },
        errors = If[ locationIndependentErrorsQ,
            errorDistribution,
            ProductDistribution @@ (Function[locationVariables, errorDistribution] /@ inputData)
        ];
        With[{
            logLikelihood = Simplify @ LogLikelihood[
                errors,
                If[locationIndependentErrorsQ, residuals, {residuals}]
            ]
        },
            If[ OptionValue["Compilation"] === True,
                Compile[
                    Evaluate[
                        Transpose[
                            {
                                Join[regressionParameters],
                                ConstantArray[_Real, Length[regressionParameters]]
                            }
                        ]
                    ],
                    Replace[
                        logLikelihood,
                        {_DirectedInfinity -> -$MaxMachineNumber}
                    ],
                    RuntimeAttributes -> {Listable}
                ],
                Function[
                    Evaluate[regressionParameters],
                    logLikelihood
                ]
            ]
        ]
    ]
];
Options[regressionLogLikelihoodFunction] = {
    Assumptions -> True,
    "Compilation" -> False
};

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

End[] (* End Private Context *)

EndPackage[]