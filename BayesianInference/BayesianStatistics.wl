(* ::Package:: *)

BeginPackage["BayesianStatistics`", {"BayesianUtilities`"}];

directPosteriorDistribution;
nestedSampling;
posteriorDistribution;
combineRuns;
predictiveDistribution;
calculationReport;
parallelNestedSampling;

Begin["`Private`"];

(* Dummy code to make WL load everything related to MixtureDistribution *)
MixtureDistribution[{1, 2}, {NormalDistribution[], ExponentialDistribution[1]}];

Unprotect[MixtureDistribution];
Format[MixtureDistribution[list1_List, list2_List]] := posteriorDistribution["Mixture of " <> ToString @ Length[list1] <> " distributions"];
Protect[MixtureDistribution];

(*
    If the prior is a list, convert all strings "LocationParameter" and "ScaleParameter" to distributions automatically
    and convert the List to a ProductDistribution
*)
ignorancePrior[
    priorSpecification : {(_?DistributionParameterQ | "LocationParameter" | "ScaleParameter")..},
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..}
] /; Length[priorSpecification] === Length[variables] := Module[{
    positionsLoc = Position[priorSpecification, "LocationParameter"],
    positionsScale = Position[priorSpecification, "ScaleParameter"]
},
        ProductDistribution @@ ReplacePart[
            priorSpecification,
            Join[
                Thread[
                    positionsLoc -> (
                        UniformDistribution[{#[[2 ;;]]}]& /@ Extract[variables, positionsLoc]
                    )
                ],
                Thread[
                    positionsScale -> (
                        ProbabilityDistribution[
                            Divide[1, #[[1]]],
                            #,
                            Method -> "Normalize"
                        ]& /@ Extract[variables, positionsScale]
                    )
                ]
            ]
        ]
    ];


directPosteriorDistribution[data_NumericQ, generatingDistribution_, prior_, variables_, opts : OptionsPattern[]] :=
    directPosteriorDistribution[{data}, generatingDistribution, prior, variables, opts];

directPosteriorDistribution[data_List, generatingDistribution_, prior_,
    variables : {_Symbol, _?NumericQ, _?NumericQ}, opts : OptionsPattern[]
] := directPosteriorDistribution[data, generatingDistribution, prior, {variables}, opts];

directPosteriorDistribution[data_List, generatingDistribution_, prior_List,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..}, opts : OptionsPattern[]
] := directPosteriorDistribution[
        data,
        generatingDistribution,
        ignorancePrior[prior, variables],
        variables,
        opts
    ];

directPosteriorDistribution[
    data_List,
    generatingDistribution_?DistributionParameterQ,
    priorDistribution_?DistributionParameterQ,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..},
    opts : OptionsPattern[]
] := directPosteriorDistribution[
    Simplify[
        Likelihood[generatingDistribution, data],
        Assumptions -> And @@ Thread[LessEqual @@ Transpose[variables[[All, {2, 1, 3}]]]]
    ],
    priorDistribution,
    variables,
    opts
];

directPosteriorDistribution[
    likelihood_,
    priorDistribution_?DistributionParameterQ,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..},
    opts : OptionsPattern[]
] := Module[{
    pdf = Simplify[
        N[
            (* Use Flatten to make sure there are no lingering lists *)
            First @ Flatten[{PDF[priorDistribution, variables[[All, 1]]] * likelihood}]
        ],
        Assumptions -> And @@ Thread[LessEqual @@ Transpose[variables[[All, {2, 1, 3}]]]]
    ],
    evidence
},
    evidence = NIntegrate[
        pdf,
        Evaluate[Sequence @@ variables],
        Evaluate[Sequence @@ OptionValue["IntegrationOptions"]]
    ];
    <|
        "Posterior" -> ProbabilityDistribution[
            Simplify[Divide[pdf, evidence]],
            Sequence @@ variables,
            Sequence @@ passOptionsDown[directPosteriorDistribution, ProbabilityDistribution, {opts}]
        ],
        "LogEvidence" -> Log[evidence]
    |>
];
Options[directPosteriorDistribution] = Join[
    Options[ProbabilityDistribution],
    {"IntegrationOptions" -> {}}
];

constrainedMarkovChainMonteCarlo[
    pdfFunction_,
    livingPoints_List,
    stepDistribution_,
    numberOfSteps_Integer,
    constraintFunction_,
    constraintLimit : (_?NumericQ | DirectedInfinity[-1])
] := Module[{
    acceptReject = {0, 0},
    tempPDF,
    tempConstraint
},
    {
        Fold[
            Function[{
                pnt, step
            },
                Function[
                    If[ And[
                            Greater[
                                tempPDF = pdfFunction[##],
                                0
                            ],
                            Or[
                                tempPDF >= pnt[[2]],
                                Divide[tempPDF, pnt[[2]]] > RandomReal[]
                            ],
                            Greater[
                                tempConstraint = constraintFunction[##],
                                constraintLimit
                            ]
                        ]
                        ,
                        PreIncrement[acceptReject[[1]]];
                        {
                            {##},
                            tempPDF,
                            tempConstraint
                        }
                        ,
                        PreIncrement[acceptReject[[2]]];
                        pnt
                    ]
                ] @@ (pnt[[1]] + step)
            ],
            RandomChoice[livingPoints[[All, "Prior"]] -> livingPoints],
            RandomVariate[stepDistribution, numberOfSteps]
        ],
        acceptReject
    }
];

trapezoidWeigths = Compile[{
    {list, _Real, 1}
},
    0.5 * Subtract[
        Prepend[Most[list], 2 - First[list]],
        Append[Rest[list], -Last[list]]
    ],
    RuntimeAttributes -> {Listable}
];

calculateXValues = Compile[{
    {nSamplePool, _Real},
    {nDeleted, _Real}
},
    Join[
        Exp[-Divide[#, nSamplePool]]& /@ Range[nDeleted],
        Reverse @ Rest @ Most @ Subdivide[Exp[-Divide[nDeleted, nSamplePool]], nSamplePool + 1]
    ],
    {
        {Subdivide[_, _], _Real, 1}
    }
];

calculateEntropy[samples_Association, evidence_] := Subtract[
    Dot[
        Divide[
            Values[samples[[All, "CrudePosteriorWeight"]]],
            evidence
        ],
        Replace[Values[samples[[All, "LogLikelihood"]]], _DirectedInfinity -> 0, {1}]
    ],
    Log[evidence]
];

calculateWeightsCrude[samplePoints_Association, nSamplePool_Integer] := Module[{
    nDeleted = Length[samplePoints] - nSamplePool,
    sorted = SortBy[{#LogLikelihood, #Point}&] @ samplePoints, (* Sorting by #Point is used to break ties. *)
    xValues,
    weights,
    keys
},
    keys = Keys[sorted];
    xValues = calculateXValues[nSamplePool, nDeleted];
    weights = trapezoidWeigths[xValues];
    Merge[
        {
            sorted,
            <|"X" -> #|> & /@ AssociationThread[keys, xValues],
            <|"CrudePosteriorWeight" -> #|> & /@ AssociationThread[keys, weights * Exp[Values @ sorted[[All, "LogLikelihood"]]]]
        },
        Join @@ # &
    ]
];

nestedSampling[
    logLikelihoodFunction_,
    variablePrior_,
    variables : {_Symbol, _?NumericQ, _?NumericQ},
    opts : OptionsPattern[]
] := nestedSampling[logLikelihoodFunction, variablePrior, {variables}, opts];

nestedSampling[
    logLikelihoodFunction_,
    variablePrior_List,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..},
    opts : OptionsPattern[]
] := nestedSampling[logLikelihoodFunction, ignorancePrior[variablePrior, variables], variables, opts];

nestedSampling[
    logLikelihoodFunction_,
    variablePrior : _?DistributionParameterQ | _Function,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..},
    opts : OptionsPattern[]
] := With[{
    dimensionCheck = Function[
        And[
            MatrixQ[#, NumericQ],
            Dimensions[#] === {OptionValue["SamplePoolSize"], Length[variables]}
        ]
    ],
    maxiterations = Max[OptionValue["MaxIterations"], OptionValue["MinIterations"]],
    miniterations = Min[OptionValue["MaxIterations"], OptionValue["MinIterations"]],
    mcMethod = Replace[OptionValue["MonteCarloMethod"], Automatic -> constrainedMarkovChainMonteCarlo],
    mcSteps = OptionValue["MonteCarloSteps"],
    termination = OptionValue["TerminationFraction"],
    nSamples = OptionValue["SamplePoolSize"],
    minMaxAcceptanceRate = OptionValue["MinMaxAcceptanceRate"],
    mcAdjustment = OptionValue["MonteCarloStepSizeAdjustment"],
    mcStepDistribution = Function[
        Evaluate[
            ProductDistribution @@ Map[
                Function[{scale}, OptionValue["MonteCarloStepDistribution"][0, scale]],
                Slot /@ Range[Length[variables]]
            ]
        ]
    ]
},
    Module[{
        variableSamplePoints,
        priorPDF,
        likelihoodThreshold = 0,
        iteration = 1,
        acceptReject,
        bestPoints,
        newPoint,
        estimatedMissingEvidence,
        evidence = 0,
        entropy = 0,
        mcStepSize = {OptionValue["InitialMonteCarloStepSize"]},
        acceptanceRatios = {},
        interrupted = False,
        statusCell,
        output
    },
        variableSamplePoints = Which[ dimensionCheck[OptionValue["StartingPoints"]],
            OptionValue["StartingPoints"]
            ,
            DistributionParameterQ[variablePrior],
                RandomVariate[
                    variablePrior,
                    OptionValue["SamplePoolSize"]
                ],
            True,
                Return["Need starting points"]
        ];
        If[ !dimensionCheck[variableSamplePoints],
            Return["Bad prior specification"]
        ];
        priorPDF = If[ DistributionParameterQ[variablePrior],
            Evaluate[
                PDF[
                    variablePrior,
                    Function[{i}, Slot[i]] /@ Range[Length[variables]]
                ]
            ]&,
            variablePrior
        ];
        variableSamplePoints = SortBy[{#LogLikelihood, #Point}&] @ Association @ MapIndexed[
            Function[
                {point, index},
                Rule[
                    First[index],
                    <|
                        "Point" -> point,
                        "Prior" -> priorPDF @@ point,
                        "LogLikelihood" -> logLikelihoodFunction @@ point,
                        "AcceptanceRejectionCounts" -> Missing["InitialSample"]
                    |>
                ]
            ],
            variableSamplePoints
        ];
        If[ !MatchQ[
                Values @ variableSamplePoints[[All, "LogLikelihood"]],
                {(_?NumericQ | DirectedInfinity[-1])..}
            ],
            Return["Bad likelihood function"]
        ];
        estimatedMissingEvidence = With[{
            lmax = OptionValue["LikelihoodMaximum"]
        },
            Switch[ lmax,
            _?NumericQ,
                Function[
                    lmax * Min[DeleteMissing @ #[[All, "X"]]]
                ],
            _,
                Function[
                    Times[
                        Min[DeleteMissing @ #[[All, "X"]]],
                        Exp @ Max[#[[All, "LogLikelihood"]]]
                    ]
                ]
            ]
        ];

        If[ TrueQ[OptionValue["Monitor"]],
            statusCell = PrintTemporary[
                Dynamic[
                    Grid[
                        {
                            {"Iteration: ", iteration},
                            {"Samples: ", Length[variableSamplePoints]},
                            {"Log evidence: ", NumberForm[Log[evidence], 5]},
                            {"Entropy: ", NumberForm[entropy, 5]},
                            {
                                Button[
                                    "Finish",
                                    interrupted = True,
                                    ImageSize -> 70
                                ],
                                SpanFromLeft
                            }

                        },
                        Alignment -> Left,
                        BaseStyle -> "Text"
                    ],
                    TrackedSymbols :> {}, UpdateInterval -> 1
                ]
            ]
        ];
        (* Main loop starts here *)
        While[
            And[
                !TrueQ[interrupted],
                iteration <= maxiterations,
                Or[
                    iteration === 1,
                    iteration <= miniterations,
                    !TrueQ[
                        estimatedMissingEvidence[variableSamplePoints] <= evidence * termination
                    ]
                ]
            ]
            ,
            bestPoints = Take[variableSamplePoints, -nSamples];
            likelihoodThreshold = Min[bestPoints[[All, "LogLikelihood"]]];

            {newPoint, acceptReject} = mcMethod[
                priorPDF,
                Values @ bestPoints,
                mcStepDistribution @@ (
                    Last[mcStepSize] * Map[
                        Abs[Subtract @@ MinMax[#]]&,
                        Transpose[Values @ bestPoints[[All , "Point"]]]
                    ]
                ),
                mcSteps,
                logLikelihoodFunction,
                likelihoodThreshold
            ];

            If[ mcAdjustment =!= None,
                AppendTo[acceptanceRatios, Divide[#1, (#1 + #2)] & @@ acceptReject];
                With[{
                    order = Lookup[mcAdjustment, "Order", 3],
                    historyLength = Clip[
                        Lookup[mcAdjustment, "HistoryLength", 0],
                        {Lookup[mcAdjustment, "Order", 3] + 1, Infinity}
                    ]
                },
                    AppendTo[
                        mcStepSize,
                        If[ Length[mcStepSize] > order,
                            Clip[
                                quietCheck[
                                    LinearModelFit[
                                        Take[
                                            Reverse @ Transpose[{acceptanceRatios - 0.5, mcStepSize}],
                                            UpTo[historyLength]
                                        ],
                                        Array[\[FormalX]^(# - 1) &, order + 1],
                                        \[FormalX],
                                        Weights -> Divide[1, Take[Range[Length[acceptanceRatios]], UpTo[historyLength]]]
                                    ][0],
                                    First[mcStepSize]
                                ],
                                Lookup[mcAdjustment, "MinMax", {0.001, 0.5}]
                            ],
                            Last[mcStepSize] * 1.2
                        ]
                    ]
                ]
            ];

            If[ TrueQ @ Between[Divide[#1, #1 + #2]& @@ acceptReject, minMaxAcceptanceRate]
                ,
                variableSamplePoints = calculateWeightsCrude[
                    Append[
                        variableSamplePoints,
                        iteration + nSamples -> AssociationThread[
                            {
                                "Point",
                                "Prior",
                                "LogLikelihood",
                                "AcceptanceRejectionCounts"
                            },
                            Append[newPoint, acceptReject]
                        ]
                    ],
                    nSamples
                ];
                evidence = Total[variableSamplePoints[[All, "CrudePosteriorWeight"]]];
                entropy = calculateEntropy[variableSamplePoints, evidence];
            ];
            PreIncrement[iteration];
        ];

        If[ ValueQ[statusCell], NotebookDelete[statusCell]];
        output = evidenceSampling[
            <|
                "Samples" -> variableSamplePoints,
                "Parameters" -> variables[[All, 1]],
                "ParameterRanges" -> variables[[All, {2, 3}]],
                "PriorFunction" -> priorPDF,
                "LogLikelihoodFunction" -> logLikelihoodFunction,
                "SamplePoolSize" -> nSamples,
                "GeneratedNestedSamples" -> Length[variableSamplePoints] - nSamples,
                "GeneratingDistribution" -> Quiet @ Replace[
                    logLikelihoodFunction,
                    {
                        Function[
                            first : Repeated[_, {0, 1}],
                            LogLikelihood[dist_, ___],
                            rest : Repeated[_, {0, 1}]
                        ] :> Function[first, dist, rest],
                        _ :> Missing["NoData"]
                    }
                ]
            |>,
            Sequence @@ passOptionsDown[nestedSampling, evidenceSampling, {opts}]
        ];
        Share[output];
        output
    ]
];

meanAndErrorAssociation = Function[
    If[ MatchQ[#, {___?NumericQ}],
        <|
            "Mean" -> Mean[#],
            "StandardError" -> StandardDeviation[#]
        |>,
        <| (* This happens for samples with such a low loglikelihood that Exp[loglike] flushes to zero *)
            "Mean" -> DirectedInfinity[-1],
            "StandardError" -> Indeterminate
        |>
    ]
];

meanAndError[data_List /; Length[Dimensions[data]] === 1] := meanAndErrorAssociation[data];

meanAndError[data_List /; Length[Dimensions[data]] === 2] := Map[
    meanAndErrorAssociation,
    data
];


evidenceSampling[assoc_?AssociationQ, opts : OptionsPattern[]] := Module[{
    result = MapAt[
        calculateWeightsCrude[#, assoc["SamplePoolSize"]]&,
        assoc,
        {"Samples"}
    ],
    nRuns = OptionValue["PostProcessSamplingRuns"],
    keys,
    evidenceWeigths,
    posteriorWeights,
    sampledX,
    parameterSamples,
    zSamples,
    output,
    crudeEvidence,
    crudeEntropy
},
    crudeEvidence = Total[result[["Samples", All, "CrudePosteriorWeight"]]];
    crudeEntropy = calculateEntropy[result["Samples"], crudeEvidence];
    output = Join[
        result,
        <|
            "CrudeLogEvidence" -> Log[crudeEvidence],
            "LogLikelihoodMaximum" -> Max[result[["Samples", All, "LogLikelihood"]]],
            "LogEstimatedMissingEvidence" -> Log @ Times[
                Min[DeleteMissing @ result[["Samples", All, "X"]]],
                Exp @ Max[result[["Samples", All, "LogLikelihood"]]]
            ],
            "CrudeRelativeEntropy" -> crudeEntropy,
            "PosteriorPDF" -> With[{
                prior = result["PriorFunction"],
                loglike = result["LogLikelihoodFunction"],
                ev = crudeEvidence
            },
                Function[
                    Null,
                    Divide[
                        Times[
                            prior[##],
                            Exp[loglike[##]]
                        ],
                        ev
                    ],
                    {Listable}
                ]
            ]
        |>
    ];
    If[ !TrueQ[IntegerQ[nRuns] && nRuns > 0],
        Return[output]
    ];

    keys = Keys[result["Samples"]];
    evidenceWeigths = Times[
        Exp[Values @ result[["Samples", All, "LogLikelihood"]]],
        Transpose[
            trapezoidWeigths[
                sampledX = Map[
                    Join[
                        #,
                        Reverse @ Sort @ RandomVariate[UniformDistribution[{0, Min[#]}], result["SamplePoolSize"]]
                    ]&,
                    With[{
                        randomNumbers = RandomVariate[
                            BetaDistribution[result["SamplePoolSize"], 1],
                            {result["GeneratedNestedSamples"], nRuns}
                        ]
                    },
                        Transpose[
                            FoldList[Times, randomNumbers]
                        ]
                    ]
                ]
            ]
        ]
    ];
    zSamples = Log @ Total[evidenceWeigths];
    parameterSamples = Transpose[
        Dot[
            posteriorWeights = Replace[
                Normalize[#, Total]& /@ Transpose[evidenceWeigths],
                0. -> 0, (* Make zero values exact so that their Log flushes to -Inf *)
                {2}
            ],
            Values[result[["Samples", All, "Point"]]]
        ]
    ];
    Join[
        output,
        <|
            "Samples" -> SortBy[-#CrudePosteriorWeight &] @ Merge[
                {
                    MapAt[
                        Divide[#, crudeEvidence]&,
                        result["Samples"],
                        {All, "CrudePosteriorWeight"}
                    ],
                    <|"SampledX" -> #|> & /@ AssociationThread[
                        keys,
                        meanAndError[Transpose[sampledX]]
                    ],
                    <|"LogPosteriorWeight" -> #|> & /@ AssociationThread[
                        keys,
                        meanAndError @ Subtract[
                            Transpose[Log[posteriorWeights]],
                            logSumExp[Mean[Log @ posteriorWeights]] (* Adjust LogWeights by constant factor so that Total[Exp[meanLogweights]] == 1. *)
                        ]
                    ]
                },
                Join @@ # &
            ],
            "LogEvidence" -> meanAndError[zSamples],
            "ParameterExpectedValues" -> meanAndError[parameterSamples],
            "RelativeEntropy" -> meanAndError[
                Subtract[
                    posteriorWeights . Replace[Values[result[["Samples", All, "LogLikelihood"]]], _DirectedInfinity -> 0, {1}],
                    zSamples
                ]
            ],
            "EmpiricalPosteriorDistribution" -> If[
                OptionValue["EmpiricalPosteriorDistributionType"] === "Simple"
                ,
                EmpiricalDistribution[ (* use the averaged weights *)
                    Rule[
                        Values @ result[["Samples", All, "CrudePosteriorWeight"]],
                        Values @ result[["Samples", All, "Point"]]
                    ]
                ]
                ,
                MixtureDistribution[ (* use all sampled weights *)
                    ConstantArray[Divide[1, nRuns], nRuns],
                    Map[
                        EmpiricalDistribution[
                            # -> Values @ result[["Samples", All, "Point"]]
                        ]&,
                        posteriorWeights
                    ]
                ]
            ]
        |>
    ]
];

Options[evidenceSampling] = {
    "PostProcessSamplingRuns" -> 100,
    "EmpiricalPosteriorDistributionType" -> "Simple"
};

Options[nestedSampling] = Join[
    {
        "SamplePoolSize" -> 25,
        "StartingPoints" -> Automatic,
        "MaxIterations" -> 1000,
        "MinIterations" -> 100,
        "MonteCarloMethod" -> Automatic,
        "MonteCarloSteps" -> 200,
        "InitialMonteCarloStepSize" -> 0.05,
        "MonteCarloStepSizeAdjustment" -> <|"Order" -> 3, "HistoryLength" -> 10, "MinMax" -> {0.001, 0.5}|>,
        "MonteCarloStepDistribution" -> NormalDistribution,
        "LocalOptimumHandling" -> <|
            "RangeExtension" -> 1.5,
            "BackTracking" -> 2
        |>,
        "TerminationFraction" -> 0.01,
        "Monitor" -> True,
        "LikelihoodMaximum" -> Automatic,
        "MinMaxAcceptanceRate" -> {0.05, 0.95}
    },
    Options[evidenceSampling]
];

combineRuns[results__?AssociationQ, opts : OptionsPattern[]] /; UnsameQ[results] := With[{
    mergedResults = SortBy[{#LogLikelihood, #Point}&] @ DeleteDuplicatesBy[
        Join @@ Values /@ {results}[[All, "Samples"]],
        #Point&
    ]
},
    evidenceSampling[
        <|
            {results}[[1]],
            "Samples" -> AssociationThread[
                Range[Length @ mergedResults],
                mergedResults
            ],
            "LogLikelihoodMaximum" -> Max[{results}[[All, "LogLikelihoodMaximum"]]],
            "SamplePoolSize" -> Total[{results}[[All, "SamplePoolSize"]]],
            "GeneratedNestedSamples" -> Length[mergedResults] - Total[{results}[[All, "SamplePoolSize"]]]
        |>,
        opts
    ]
];
Options[combineRuns] = Options[evidenceSampling];

parallelNestedSampling[logLikelihood_, prior_, variables_, opts : OptionsPattern[]] := Module[{
    resultTable,
    parallelRuns = OptionValue["ParallelRuns"],
    nestedSamplingOptions = Join[
        {
            "PostProcessSamplingRuns" -> None,
            "Monitor" -> False
        },
        passOptionsDown[parallelNestedSampling, nestedSampling, {opts}]
    ]
},

    resultTable = ParallelTable[
        nestedSampling[
            logLikelihood,
            prior,
            variables,
            Sequence @@ nestedSamplingOptions
        ],
        {parallelRuns},
        Evaluate[Sequence @@ passOptionsDown[parallelNestedSampling, ParallelTable, {opts}]]
    ];
    combineRuns[
        ##,
        Sequence @@ passOptionsDown[parallelNestedSampling, combineRuns, {opts}]
    ]& @@ resultTable
];

Options[parallelNestedSampling] = Join[
    Options[nestedSampling],
    Options[ParallelTable],
    {"ParallelRuns" :> 4}
];
SetOptions[parallelNestedSampling, DistributedContexts :> $BayesianContexts];

predictiveDistribution[
    result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&),
    posteriorFraction : _?NumericQ : 1
] /; !MissingQ[result["GeneratingDistribution"]] :=
    predictiveDistribution[
        result,
        result["GeneratingDistribution"],
        posteriorFraction
    ];

predictiveDistribution[
    result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&),
    posteriorFraction : _?NumericQ : 1
] /; MissingQ[result["GeneratingDistribution"]] := "No distribution specified";

predictiveDistribution[
    result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&),
    dist : Except[_?NumericQ],
    posteriorFraction : _?NumericQ : 1
] /; Between[posteriorFraction, {0, 1}] := Module[{
    truncatedResult = takePosteriorFraction[result, posteriorFraction]
},
    MixtureDistribution[
        Values @ truncatedResult[["Samples", All, "CrudePosteriorWeight"]],
        dist @@ #& /@ Values @ truncatedResult[["Samples", All, "Point"]]
    ]
];

calculationReport[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)] := TabView[{

    DynamicModule[{
        min = Max[result[["Samples", All, "LogLikelihood"]]] - 100
    },
        Column[{
           Dynamic[
               ListLogLinearPlot[
                    Transpose[
                        {
                            Values @ result[["Samples", All, "SampledX", "Mean"]],
                            Values @ result[["Samples", All, "LogLikelihood"]]
                        }
                    ],
                    PlotRange -> {min, All},
                    PlotLabel -> "Enclosed prior mass vs log likelihood",
                    ImageSize -> Large
                ],
                TrackedSymbols :> {min}
            ],
            Manipulator[
                Dynamic[min],
                Max[result[["Samples", All, "LogLikelihood"]]] + {-100, -1}
            ]
        }, Alignment -> Left]
    ],

    ListLogLogPlot[
        Transpose[
            {
                Values @ result[["Samples", All, "SampledX", "Mean"]],
                Reverse @ Accumulate @ Reverse[
                    Values @ result[["Samples", All, "CrudePosteriorWeight"]]
                ]
            }
        ],
        PlotRange -> All,
        PlotLabel -> "Enclosed posterior mass vs enclosed prior mass",
        ImageSize -> Large
    ],

    ListPlot[
        Log /@ Accumulate @ Values @ result[["Samples", All, "CrudePosteriorWeight"]],
        PlotLabel -> "Log evidence",
        PlotRange -> All,
        ImageSize -> Large
    ],

    ListPlot[
        result[["Samples", All, "LogLikelihood"]],
        PlotLabel -> "Log likelihood",
        PlotRange -> All,
        ImageSize -> Large
    ],

    ListPlot[
        Divide[#[[1]], #[[1]] + #[[2]]]& /@ DeleteMissing @ result[["Samples", All, "AcceptanceRejectionCounts"]],
        PlotLabel -> "Acceptance Ratio",
        PlotRange -> {0, 1},
        ImageSize -> Large,
        Epilog -> InfiniteLine[{{0, 0.5}, {1, 0.5}}]
    ]
}];

End[(*Private*)]

EndPackage[(*"BayesianStatistics"*)]