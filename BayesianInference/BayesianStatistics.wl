(* ::Package:: *)

BeginPackage["BayesianStatistics`", {"BayesianUtilities`", "GeneralUtilities`"}];

directPosteriorDistribution;
nestedSampling;
combineRuns;
predictiveDistribution;
calculationReport;
parallelNestedSampling;
defineInferenceProblem;
bayesianInferenceObject;
generateStartingPoints;

Begin["`Private`"];

paramSpecPattern = {_Symbol, _?NumericQ | DirectedInfinity[-1], _?NumericQ | DirectedInfinity[1]};

(*
    If the prior is a list, convert all strings "LocationParameter" and "ScaleParameter" to distributions automatically
    and convert the List to a ProductDistribution
*)
ignorancePrior[
    priorSpecification : {(_?DistributionParameterQ | "LocationParameter" | "ScaleParameter")..},
    variables : {paramSpecPattern..}
] /; Length[priorSpecification] === Length[variables] := Module[{
    positionsLoc = Position[priorSpecification, "LocationParameter"],
    positionsScale = Position[priorSpecification, "ScaleParameter"],
    positionsDist = Position[priorSpecification, _?DistributionParameterQ]
},
        ProductDistribution @@ ReplacePart[
            priorSpecification,
            Join[
                Thread[
                    positionsLoc -> (
                        UniformDistribution[{#[[{2, 3}]]}]& /@ Extract[variables, positionsLoc]
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
                ],
                Thread[
                    positionsDist -> MapThread[
                        TruncatedDistribution[
                            #2[[{2, 3}]],
                            #1
                        ]&,
                        {
                            Extract[priorSpecification, positionsDist],
                            Extract[variables, positionsDist]
                        }
                    ]
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

defineInferenceProblem::dataFormat = "Data was provided in unusable format";
defineInferenceProblem::insuffInfo = "Not enough information was provide to define the problem. Failed at: `1`";
defineInferenceProblem::logLike = "Unable to automatically construct the loglikelihood function for distribution `1`. Please construct one manually";
defineInferenceProblem::prior = "Unable to automatically construct the log prior PDF function for distribution `1`. Please construct one manually";
defineInferenceProblem::failed = "Failure. `1` does not yield numerical results in the required domain";

defineInferenceProblem[] := {
    "Data",
    "Parameters",
    "IndependentVariables",
    "LogLikelihoodFunction",
    "LogPriorPDFFunction",
    "GeneratingDistribution",
    "PriorDistribution",
    "PriorPDF"
};
defineInferenceProblem[rules : __Rule] := defineInferenceProblem[Association[{rules}]];
defineInferenceProblem[inferenceObject[assoc_?AssociationQ]] := defineInferenceProblem[assoc];

defineInferenceProblem[input_?AssociationQ] := inferenceObject @ Catch[
    Module[{
        assoc = input,
        keys,
        tempKeys,
        randomTestPoints
    },
        keys = Keys[DeleteMissing @ assoc];
        If[ MemberQ[keys, "Data"],
            assoc["Data"] = normalizeData @ assoc["Data"]
        ];
        Which[ 
            MatchQ[assoc["Parameters"], {paramSpecPattern..}],
                Null,
            MatchQ[assoc["Parameters"], paramSpecPattern],
                assoc["Parameters"] = {assoc["Parameters"]},
            True,
                Message[defineInferenceProblem::insuffInfo, "Parameter definition"];
                Throw[$Failed, "problemDef"]
        ];
        If[ MemberQ[keys, "IndependentVariables"] && !ListQ[assoc["IndependentVariables"]],
            assoc["IndependentVariables"] = {assoc["IndependentVariables"]}
        ];
        AppendTo[assoc, "ParameterSymbols" -> assoc["Parameters"][[All, 1]]];
        If[ ListQ[assoc["PriorDistribution"]],
            With[{
                priorDist = ignorancePrior[
                    assoc["PriorDistribution"],
                    assoc["Parameters"]
                ]
            },
                If[ TrueQ @ DistributionParameterQ[priorDist],
                    assoc["PriorDistribution"] = priorDist,
                    Message[defineInferenceProblem::insuffInfo, "Prior distribution construction"];
                    Throw[$Failed, "problemDef"]
                ]
            ]
        ];
        Which[
            MemberQ[keys, "LogLikelihoodFunction"],
                Null,
            And[
                SubsetQ[keys, tempKeys = {"GeneratingDistribution", "Data", "Parameters"}],
                ListQ[assoc["Data"]]
            ],
                AppendTo[assoc, "LogLikelihoodFunction" -> logLikelihoodFunction @@ Values[assoc[[tempKeys]]]],
            And[
                SubsetQ[keys, tempKeys = {"GeneratingDistribution", "Data", "IndependentVariables", "Parameters"}],
                Head[assoc["Data"]] === Rule
            ],
                AppendTo[assoc, "LogLikelihoodFunction" -> regressionLogLikelihoodFunction @@ Values[assoc[[tempKeys]]]],
            True,
                (
                    Message[defineInferenceProblem::insuffInfo, "LogLikelihood function"];
                    Throw[$Failed, "problemDef"]
                )
        ];
        Which[
            MemberQ[keys, "LogPriorPDFFunction"],
                Null,
            SubsetQ[keys, tempKeys = {"PriorDistribution", "Parameters"}],
                AppendTo[
                    assoc,
                    "LogPriorPDFFunction" -> logPDFFunction @@ Values[assoc[[tempKeys]]]
                ],
            SubsetQ[keys, tempKeys = {"PriorPDF", "Parameters"}],
                AppendTo[
                    assoc,
                    "LogPriorPDFFunction" -> logPDFFunction @@ Values[assoc[[tempKeys]]]
                ],
            True,
                (
                    Message[defineInferenceProblem::insuffInfo, "Log prior PDF"];
                    Throw[$Failed, "problemDef"]
                )
        ];
        
        (* Simple test to check if the functions work as required *)
        randomTestPoints = RandomVariate[
            BayesianUtilities`Private`randomDomainPointDistribution[assoc["Parameters"][[All, {2, 3}]]],
            100
        ];
        If[ !TrueQ @ VectorQ[assoc["LogPriorPDFFunction"] /@ randomTestPoints, NumericQ]
            ,
            (
                Message[defineInferenceProblem::failed, "LogPriorPDFFunction"];
                Throw[$Failed, "problemDef"]
            )
            ,
            If[ !TrueQ @ VectorQ[assoc["LogLikelihoodFunction"] /@ randomTestPoints, NumericQ],
                (
                    Message[defineInferenceProblem::failed, "LogLikelihoodFunction"];
                    Throw[$Failed, "problemDef"]
                )
            ]
        ];
        
        (* Issue a message if a sub-optimal compiled function is found *)
        KeyValueMap[checkCompiledFunction[#2, #1]&,
            assoc[[{"LogPriorPDFFunction", "LogLikelihoodFunction"}]]
        ];
        assoc
    ],
    "problemDef"
];
defineInferenceProblem[___] := inferenceObject[$Failed];

normalizeData[miss_Missing] := miss;
normalizeData[data_List?(MatrixQ[#, NumericQ]&)] := data;
normalizeData[data_List?(VectorQ[#, NumericQ]&)] := List /@ data;
normalizeData[data : {__Rule}] := normalizeData[Thread[data, Rule]];
normalizeData[in_List -> out_List] := With[{
    input = normalizeData[in],
    output = normalizeData[out]
},
    (input -> output) /; Length[input] === Length[output]
];
normalizeData[___] := (
    Message[defineInferenceProblem::dataFormat];
    Throw[$Failed, "problemDef"]
);

distributionDomainTest::paramSpec = "Warning! The support of distribution `1` could not be verified to contain the region specified by parameters `2`";
distributionDomainTest[dist_?DistributionParameterQ, parameters : {paramSpecPattern..}] := With[{
    reg1 = Replace[DistributionDomain[dist], int_Interval :> {int}],
    reg2 = Map[
        Interval,
        parameters[[All, {2, 3}]]
    ]
},
    TrueQ[
        And @@ IntervalMemberQ[reg1, reg2]
    ] /; And[
        AllTrue[{reg1, reg2}, MatchQ[{__Interval}]],
        Length[reg1] === Length[reg2]
    ]
];
distributionDomainTest[___] := False;

parametersToConstraints[parameters : {paramSpecPattern..}, otherConstraints : _ : True] := FullSimplify[
    And[
        And @@ (Less @@@ parameters[[All, {2, 1, 3}]]),
        Element[
            Alternatives @@ parameters[[All, 1]],
            Reals
        ],
        otherConstraints
    ]
];

constraintsToFunction[parameters : {paramSpecPattern..}, otherConstraints : _ : True] := Block[{
    paramVector
},
    expressionToFunction[
        And @@ Cases[
            BooleanConvert[parametersToConstraints[parameters, otherConstraints], "CNF"],
            _Less | _Greater | _GreaterEqual | _LessEqual,
            {0, 1}
        ],
        {parameters[[All, 1]] -> paramVector} 
    ]
];

distributionDomainToConstraints[int_Interval, {sym_}] := distributionDomainToConstraints[int, sym];
distributionDomainToConstraints[Interval[{min_, max_}], sym : Except[_List]] := FullSimplify[min < sym < max && Element[sym, Reals]];
distributionDomainToConstraints[dom : {__Interval}, symbols_List] /; Length[dom] === Length[symbols] := And @@ MapThread[
    distributionDomainToConstraints,
    {dom, symbols}
];
distributionDomainToConstraints[___] := True;

logPDFFunction[
    dist_?DistributionParameterQ,
    parameters : {paramSpecPattern..}
] := (
    If[ !TrueQ[distributionDomainTest[dist, parameters]],
        Message[distributionDomainTest::paramSpec, dist, parameters]
    ];
    logPDFFunction[
        Replace[
            If[ Head[DistributionDomain[dist]] === List,
                PDF[dist, parameters[[All, 1]]],
                PDF[dist, parameters[[1, 1]]]
            ],
            _PDF :> (
                Message[defineInferenceProblem::prior, dist];
                Throw[$Failed, "problemDef"]
            )
        ],
        parameters
    ]
);

logPDFFunction[
    pdf_,
    parameters : {paramSpecPattern..}
] := Block[{
    constraints = parametersToConstraints[parameters],
    logPDF,
    paramVector
},
    logPDF = expressionToFunction[
        simplifyLogPDF[
            N @ Log[pdf],
            And[
                constraints,
                Element[
                    Alternatives @@ parameters[[All, 1]],
                    Reals
                ]
            ]
        ],
        {parameters[[All, 1]] -> paramVector}
    ];
    constraints = constraintsToFunction[parameters, constraints];
    
    Compile[{
        {param, _Real, 1}
    },
        If[ constraints[param],
            logPDF[param],
            $MachineLogZero
        ],
        CompilationOptions -> {
            "InlineExternalDefinitions" -> True,
            "InlineCompiledFunctions" -> True
        },
        RuntimeAttributes -> {Listable}
    ]
];

logLikelihoodFunction[
    dist_?DistributionParameterQ,
    data_List?(MatrixQ[#, NumericQ]&),
    parameters : {paramSpecPattern..}
] := Module[{
    dataDim = Dimensions[data][[2]],
    logLike,
    constraints,
    domain = DistributionDomain[dist]
},
    constraints = parametersToConstraints[parameters, DistributionParameterAssumptions[dist]];
    logLike = Function[
        {paramVector, dataPoint},
        Evaluate[
            N @ varsToParamVector[
                With[{
                    vars = Table[
                        Indexed[dataPoint, i],
                        {i, 1, dataDim}
                    ]
                },
                    simplifyLogPDF[
                        Replace[
                            LogLikelihood[
                                dist,
                                If[ Head[domain] === List , List @ vars, vars] (* Determine if dist is a scalar of vector distribution *)
                            ],
                            _LogLikelihood :> ( (* If LogLikelihood doesn't evaluate, no compiled function can be constructed *)
                                Message[defineInferenceProblem::logLike, dist];
                                Throw[$Failed, "problemDef"]
                            )
                        ],
                        And[
                            constraints,
                            distributionDomainToConstraints[domain, vars]
                        ] 
                    ]
                ],
                parameters[[All, 1]] -> paramVector
            ]
        ]
    ];
    logLike = Compile[{
        {input, _Real, 1},
        {pt, _Real, 1}
    },
        logLike[input, pt],
        CompilationOptions -> {
            "InlineExternalDefinitions" -> True,
            "InlineCompiledFunctions" -> True
        }
    ];
    
    (* convert constraint equations into a boolean function that tells you if the constraints are satisfied for a given parameter vector *)
    constraints = constraintsToFunction[parameters, constraints];
    Compile[{
        {input, _Real, 1}
    },
        If[ constraints[input],
            Sum[logLike[input, i], {i, data}],
            $MachineLogZero
        ],
        CompilationOptions -> {
            "InlineExternalDefinitions" -> True,
            "InlineCompiledFunctions" -> True
        },
        RuntimeAttributes -> {Listable}
    ]
];
logLikelihoodFunction[dist_, ___] := (
    Message[defineInferenceProblem::logLike, dist];
    Throw[$Failed, "problemDef"]
);

regressionLogLikelihoodFunction[
    regressionDistribution_?DistributionParameterQ,
    (inputData_List?(MatrixQ[#, NumericQ]&)) -> (outputData_List?(MatrixQ[#, NumericQ]&)),
    independentVariables  : {__Symbol},
    parameters : {paramSpecPattern..}
] /; Length[inputData] === Length[outputData] := Module[{
    constraints = parametersToConstraints[parameters, DistributionParameterAssumptions[regressionDistribution]],
    domain = DistributionDomain[regressionDistribution],
    dataDimOut = Dimensions[outputData][[2]],
    logLike,
    nDat = Length[inputData]
},
    logLike = Function[
        {paramVector, dataIn, dataOut},
        Evaluate[
            N @ varsToParamVector[
                With[{
                    varsOut = Table[
                        Indexed[dataOut, i],
                        {i, 1, dataDimOut}
                    ]
                },
                    simplifyLogPDF[
                        Replace[
                            LogLikelihood[
                                regressionDistribution,
                                If[ Head[domain] === List , List @ varsOut, varsOut] (* Determine if dist is a scalar of vector distribution *)
                            ],
                            _LogLikelihood :> ( (* If LogLikelihood doesn't evaluate, no compiled function can be constructed *)
                                Message[defineInferenceProblem::logLike, regressionDistribution];
                                Throw[$Failed, "problemDef"]
                            )
                        ],
                        And[
                            constraints,
                            distributionDomainToConstraints[domain, varsOut]
                        ] 
                    ]
                ],
                {parameters[[All, 1]] -> paramVector, independentVariables -> dataIn}
            ]
        ]
    ];
    logLike = Compile[{
        {input, _Real, 1},
        {ptIn, _Real, 1},
        {ptOut, _Real, 1}
    },
        logLike[input, ptIn, ptOut],
        CompilationOptions -> {
            "InlineExternalDefinitions" -> True,
            "InlineCompiledFunctions" -> True
        }
    ];
    constraints = constraintsToFunction[parameters];
    Compile[{
        {input, _Real, 1}
    },
        If[ constraints[input],
            Sum[logLike[input, inputData[[i]], outputData[[i]]], {i, nDat}],
            $MachineLogZero
        ],
        CompilationOptions -> {
            "InlineExternalDefinitions" -> True,
            "InlineCompiledFunctions" -> True
        },
        RuntimeAttributes -> {Listable}
    ]
];
regressionLogLikelihoodFunction[dist_, ___] := (
    Message[defineInferenceProblem::logLike, dist];
    Throw[$Failed, "problemDef"]
);


nsDensity[logPriorDensity_CompiledFunction, logLikelihood_CompiledFunction, logThreshold_?NumericQ] := Compile[{
    {point, _Real, 1}
},
    If[ logLikelihood[point] > logThreshold,
        logPriorDensity[point],
        $MachineLogZero
    ],
    CompilationOptions -> {
        "InlineExternalDefinitions" -> True, 
        "InlineCompiledFunctions" -> False
    }
];

nsDensity[logPriorDensity_, logLikelihood_, logThreshold_?NumericQ] := With[{
    logzero = $MachineLogZero 
},
    Function[
        If[ TrueQ[logLikelihood[#] > logThreshold],
            logPriorDensity[#],
            logzero
        ]
    ]
];

MCMC[
    logDensity_,
    initialPoint_List,
    meanEst_List,
    covEst_List,
    {numberOfSteps_Integer, extraSteps_Integer, maxSteps_Integer},
    minMaxAcceptanceRate : {_, _}
] := With[{
    startingIteration = 10
},
    Module[{
        (* Initialise the chain at step 10 so that the estimated covariance does not go all over the place *)
        chain = Statistics`MCMC`BuildMarkovChain[{"AdaptiveMetropolis", "Log"}][
            "FullState",
            {initialPoint, startingIteration, meanEst, covEst},
            logDensity,
            {covEst, startingIteration},
            Real,
            Compiled -> Head[logDensity] === CompiledFunction
        ]
    },
        Statistics`MCMC`MarkovChainIterate[chain, {1, numberOfSteps}];
        While[ True,
            If[ Or[
                    TrueQ @ Between[chain["AcceptanceRate"], minMaxAcceptanceRate],
                    TrueQ[chain["StateData"][[2]] >= maxSteps + startingIteration]
                ],
                Break[],
                Statistics`MCMC`MarkovChainIterate[chain, {1, extraSteps}]
            ]
        ];
        Append[
            AssociationThread[
                {"Point", "MeanEstimate", "CovarianceEstimate"},
                chain["StateData"][[{1, 3, 4}]]
            ],
            "AcceptanceRate" -> chain["AcceptanceRate"]
        ]
    ]
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
        Reverse @ Table[
            (i / (nSamplePool + 1)) * Exp[-Divide[nDeleted, nSamplePool]],
            {i, 1, nSamplePool}
        ]
    ]
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
    Join[
        sorted,
        GeneralUtilities`AssociationTranspose @ <|
            "X" -> AssociationThread[keys, xValues],
            "CrudePosteriorWeight" -> AssociationThread[keys, weights * Exp[Values @ sorted[[All, "LogLikelihood"]]]]
        |>,
        2
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
        "TerminationFraction" -> 0.01,
        "Monitor" -> True,
        "LikelihoodMaximum" -> Automatic,
        "MinMaxAcceptanceRate" -> {0.05, 0.95}
    },
    Options[evidenceSampling]
];
Options[nestedSamplingInternal] = DeleteCases[
    Options[nestedSampling],
    ("SamplePoolSize" | "StartingPoints") -> _
];

nestedSampling::MCSteps = "Cannot use value `1` for option MonteCarloSteps. Defaulting to `2` instead";

nestedSamplingInternal[
    logLikelihoodFunction_,
    logPriorDensityFunction_,
    startingPoints_,
    params : {paramSpecPattern..},
    opts : OptionsPattern[]
] := Module[{
    maxiterations = Max[OptionValue["MaxIterations"], OptionValue["MinIterations"]],
    miniterations = Min[OptionValue["MaxIterations"], OptionValue["MinIterations"]],
    mcSteps = Replace[
        OptionValue["MonteCarloSteps"],
        {
            i_Integer :> {i, i, 5 * i},
            other : Except[{_Integer, _Integer, _Integer}] :> (
                Message[nestedSampling::MCSteps, Short[other], {200, 200, 1000}];
                {200, 200, 5}
            )
        } 
    ],
    termination = OptionValue["TerminationFraction"],
    minMaxAcceptanceRate = OptionValue["MinMaxAcceptanceRate"],
    variableSamplePoints = startingPoints,
    nSamples,
    parameterSpaceDimension,
    likelihoodThreshold = 0,
    iteration = 1,
    bestPoints,
    newPoint,
    constrainedLogDensity,
    meanEst,
    covEst,
    var,
    factor,
    estimatedMissingEvidence,
    evidence = 0,
    entropy = 0,
    interrupted = False,
    statusCell,
    output
},
    {nSamples, parameterSpaceDimension} = Dimensions[startingPoints];
    variableSamplePoints = SortBy[{#LogLikelihood, #Point}&] @ Association @ MapIndexed[
        Function[
            {point, index},
            Rule[
                First[index],
                <|
                    "Point" -> point,
                    "LogLikelihood" -> logLikelihoodFunction[point],
                    "AcceptanceRate" -> Missing["InitialSample"]
                |>
            ]
        ],
        variableSamplePoints
    ];
    If[ !VectorQ[
            Values @ variableSamplePoints[[All, "LogLikelihood"]],
            NumericQ
        ],
        Return["Bad likelihood function"]
    ];
    meanEst = Mean[Values @ variableSamplePoints[[All, "Point"]]];
    covEst = DiagonalMatrix @ Variance[Values @ variableSamplePoints[[All, "Point"]]];
    
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
        constrainedLogDensity = nsDensity[
            logPriorDensityFunction,
            logLikelihoodFunction,
            likelihoodThreshold
        ];
        var = Variance[bestPoints[[All, "Point"]]];
        factor = 1;
        covEst = Divide[covEst + 3 * DiagonalMatrix[var], 4]; (* Retain a fraction of the previous covariance estimate *)
        While[ True,
            newPoint = MCMC[
                constrainedLogDensity,
                RandomChoice[Values @ bestPoints[[All, "Point"]]],
                meanEst,
                covEst,
                Ceiling[factor * mcSteps],
                minMaxAcceptanceRate
            ];
            {meanEst, covEst} = Values @ newPoint[[{"MeanEstimate", "CovarianceEstimate"}]];
            If[ Between[newPoint["AcceptanceRate"], minMaxAcceptanceRate],
                Break[],
                factor *= 1.25
            ]
        ];
        
        variableSamplePoints = calculateWeightsCrude[
            Append[
                variableSamplePoints,
                iteration + nSamples -> Append[
                    newPoint[[{"Point", "AcceptanceRate", "MeanEstimate", "CovarianceEstimate"}]],
                    "LogLikelihood" -> logLikelihoodFunction[newPoint[["Point"]]]
                ]
            ],
            nSamples
        ];
        evidence = Total[variableSamplePoints[[All, "CrudePosteriorWeight"]]];
        entropy = calculateEntropy[variableSamplePoints, evidence];
        PreIncrement[iteration];
    ];
    
    If[ ValueQ[statusCell], NotebookDelete[statusCell]];
    output = evidenceSampling[
        <|
            "Samples" -> variableSamplePoints,
            "SamplePoolSize" -> nSamples,
            "GeneratedNestedSamples" -> Length[variableSamplePoints] - nSamples,
            "TotalSamples" -> Length[variableSamplePoints],
            "ParameterRanges" -> CoordinateBounds[Values @ variableSamplePoints[[All, "Point"]]]
        |>,
        params[[All, 1]],
        Sequence @@ passOptionsDown[nestedSampling, evidenceSampling, {opts}]
    ];
    Share[output];
    output
];

Options[generateStartingPoints] = {
    "BurnInPeriod" -> 1000,
    "Thinning" -> 1000
};
generateStartingPoints[inferenceObject[assoc_?AssociationQ], n_Integer, opts : OptionsPattern[]] := With[{
    pts = generateStartingPoints[assoc, n, opts]
},
    If[ MatrixQ[pts, NumericQ] && Dimensions[pts][[2]] === Length[assoc["Parameters"]],
        inferenceObject[Append[assoc, "StartingPoints" -> pts]],
        inferenceObject[$Failed]
    ]
]

generateStartingPoints[
    assoc : KeyValuePattern["PriorDistribution" -> dist_?DistributionParameterQ],
    n_Integer,
    OptionsPattern[]
] := Replace[
    RandomVariate[dist, n],
    {
        lst_List?(VectorQ[#, NumericQ]&) :> List /@ lst,
        Except[_List?(MatrixQ[#, NumericQ]&)] :> generateStartingPoints[
            KeyDrop[assoc, "PriorDistribution"], (* Try generating points from the LogPriorPDFFunction, if available *)
            n
        ]
    }
];

generateStartingPoints[
    assoc : KeyValuePattern[{"LogPriorPDFFunction" -> logPDF_, "Parameters" -> params : {paramSpecPattern..}}],
    n_Integer,
    opts : OptionsPattern[]
] := Module[{
    chain = With[{
        crudeSamples = RandomVariate[BayesianUtilities`Private`randomDomainPointDistribution[params[[All, {2, 3}]]], 100]
    },
        Statistics`MCMC`BuildMarkovChain[{"AdaptiveMetropolis", "Log"}][
            First @ crudeSamples,
            logPDF,
            {DiagonalMatrix[Variance[crudeSamples]], 20},
            Real,
            Compiled -> True
        ]
    ],
    samples
},
    Statistics`MCMC`MarkovChainIterate[chain, {1, OptionValue["BurnInPeriod"]}];
    samples = Statistics`MCMC`MarkovChainIterate[chain, {n, OptionValue["Thinning"]}];
    Print @ StringForm[
        "Generated `1` inital samples using MCMC. Acceptance rate: `2`",
        n,
        chain["AcceptanceRate"]
    ];
    samples
];
generateStartingPoints[__] := $Failed

nestedSampling[
    inferenceObject[assoc_?AssociationQ],
    opts : OptionsPattern[]
] /; !MatrixQ[assoc["StartingPoints"], NumericQ] := With[{
    startingPoints = Replace[
        OptionValue["StartingPoints"],
        {
            Except[_?(MatrixQ[#, NumericQ]&)] :> generateStartingPoints[assoc, OptionValue["SamplePoolSize"]]
        }
    ]
},
    nestedSampling[
        inferenceObject[Append[assoc, "StartingPoints" -> startingPoints]]
    ] /; MatrixQ[startingPoints, NumericQ]
];

nestedSampling[
    inferenceObject[assoc_?AssociationQ],
    opts : OptionsPattern[]
] /; And[
    MatrixQ[assoc["StartingPoints"], NumericQ],
    MatchQ[assoc["Parameters"], {paramSpecPattern..}],
    Dimensions[assoc["StartingPoints"]][[2]] === Length[assoc["Parameters"]]
] := Module[{
    result = nestedSamplingInternal[
        assoc["LogLikelihoodFunction"],
        assoc["LogPriorPDFFunction"],
        assoc["StartingPoints"],
        assoc["Parameters"],
        Sequence @@ FilterRules[{opts}, Options[nestedSamplingInternal]]
    ]
},
    If[ TrueQ @ AssociationQ[result],
        inferenceObject[Join[assoc, result]],
        result
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


evidenceSampling[assoc_?AssociationQ, paramNames : _List : {}, opts : OptionsPattern[]] := Module[{
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
            "CrudeRelativeEntropy" -> crudeEntropy
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
            "Samples" -> SortBy[-#CrudePosteriorWeight &] @ Join[
                MapAt[
                    Divide[#, crudeEvidence]&,
                    result["Samples"],
                    {All, "CrudePosteriorWeight"}
                ],
                GeneralUtilities`AssociationTranspose @ <|
                    "SampledX" -> AssociationThread[keys, meanAndError[Transpose[sampledX]]],
                    "LogPosteriorWeight" -> AssociationThread[
                        keys,
                        meanAndError @ Subtract[
                            Transpose[Log[posteriorWeights]],
                            logSumExp[Mean[Log @ posteriorWeights]] (* Adjust LogWeights by constant factor so that Total[Exp[meanLogweights]] == 1. *)
                        ]
                    ]
                |>,
                2
            ],
            "LogEvidence" -> meanAndError[zSamples],
            "ParameterExpectedValues" -> With[{
                paramMeanErr = meanAndError[parameterSamples]
            },
                If[ Length[paramNames] === Length[paramMeanErr],
                    AssociationThread[paramNames, paramMeanErr],
                    paramMeanErr
                ]
            ],
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

combineRuns[results : inferenceObject[_?AssociationQ].., opts : OptionsPattern[]] /; UnsameQ[results] := With[{
    mergedResults = SortBy[{#LogLikelihood, #Point}&] @ DeleteDuplicatesBy[
        Join @@ Values /@ {results}[[All, 1, "Samples"]],
        #Point&
    ]
},
    evidenceSampling[
        <|
            {results}[[All, 1]],
            "Samples" -> AssociationThread[
                Range[Length @ mergedResults],
                mergedResults
            ],
            "LogLikelihoodMaximum" -> Max[{results}[[All, 1, "LogLikelihoodMaximum"]]],
            "SamplePoolSize" -> Total[{results}[[All, 1, "SamplePoolSize"]]],
            "GeneratedNestedSamples" -> Length[mergedResults] - Total[{results}[[All, 1, "SamplePoolSize"]]],
            "TotalSamples" -> Length[mergedResults]
        |>,
        {results}[[1, 1, "Parameters", All, 1]],
        opts
    ]
];
Options[combineRuns] = Options[evidenceSampling];

parallelNestedSampling[
    inferenceObject[assoc_?AssociationQ],
    opts : OptionsPattern[]
] /; !MatrixQ[assoc["StartingPoints"], NumericQ] := With[{
    startingPoints = Replace[
        OptionValue["StartingPoints"],
        {
            Except[_?(MatrixQ[#, NumericQ]&)] :> generateStartingPoints[assoc, OptionValue["SamplePoolSize"]]
        }
    ]
},
    parallelNestedSampling[
        inferenceObject[Append[assoc, "StartingPoints" -> startingPoints]]
    ] /; MatrixQ[startingPoints, NumericQ]
];

parallelNestedSampling[
    inferenceObject[assoc_?AssociationQ],
    opts : OptionsPattern[]
] /; MatrixQ[assoc["StartingPoints"], NumericQ] := Module[{
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
    Quiet[LaunchKernels[], {LaunchKernels::nodef}];
    resultTable = ParallelTable[
        Needs["GeneralUtilities`"];
        nestedSampling[
            inferenceObject[assoc],
            Sequence @@ nestedSamplingOptions
        ],
        {parallelRuns},
        Evaluate[Sequence @@ passOptionsDown[parallelNestedSampling, ParallelTable, {opts}]]
    ];
    inferenceObject[
        combineRuns[
            ##,
            Sequence @@ passOptionsDown[parallelNestedSampling, combineRuns, {opts}]
        ]& @@ resultTable
    ]
];

Options[parallelNestedSampling] = Join[
    Options[nestedSampling],
    Options[ParallelTable],
    {"ParallelRuns" :> 4}
];
SetOptions[parallelNestedSampling, DistributedContexts :> $BayesianContexts];

predictiveDistribution::MissGenDist = "No generating distribution specified";
predictiveDistribution::unsampled = "Posterior has not been sampled yet";
predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && MissingQ[#["Samples"]]&)]
] := (
    Message[predictiveDistribution::unsampled];
    $Failed
);
predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && !MissingQ[#["Samples"]] && MissingQ[#["GeneratingDistribution"]]&)]
] := (
    Message[predictiveDistribution::MissGenDist];
    $Failed
);

predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)]
] := With[{
    dist = Block[{
        paramVector
    },
        expressionToFunction[
            result["GeneratingDistribution"],
            {result["ParameterSymbols"] -> paramVector}
        ]
    ]
},
    MixtureDistribution[
        Values @ result[["Samples", All, "CrudePosteriorWeight"]],
        dist /@ Values[result[["Samples", All, "Point"]]]
    ]
];

calculationReport[inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)]] := With[{
    style = Function[
        {
            Frame -> True,
            ImageSize -> Large,
            FrameLabel -> {{#2, None}, {#1, None}}
        }
    ],
    manipulateStyle = {ControlPlacement -> Bottom, Paneled -> False}
},
    TabView @ AssociationThread[{
            "Skilling's plot",
            "Posterior concentration",
            "Evidence",
            "LogLikelihood",
            "Acceptance rate"
        } -> {
        With[{
            dat = Transpose @ {
                Values @ result[["Samples", All, "SampledX", "Mean"]],
                Values @ result[["Samples", All, "LogLikelihood"]]
            }
        },
            Manipulate[
                Show[
                    ListLogLinearPlot[
                        dat,
                        PlotRange -> MinMax[dat[[All, 2]]],
                        PlotRangePadding -> {{0, 0}, {0, Scaled[0.01]}},
                        PlotLabel -> "Skilling's plot",
                        Sequence @@ style["X; enclosed prior mass", "LogLikelihood"]
                    ],
                    PlotRange -> {{All, Log[1]}, {Dynamic[min], All}}
                ],
                {
                    {min, Max[result[["Samples", All, "LogLikelihood"]]] - 100, "Y-axis range"},
                    Sequence @@ (Max[result[["Samples", All, "LogLikelihood"]]] + {-100, -1})
                },
                Evaluate[Sequence @@ manipulateStyle]
            ]
        ],
        
        With[{
            points = With[{
                sorted = SortBy[
                    result[["Samples", All, {"X", "CrudePosteriorWeight", "LogLikelihood"}]],
                    #LogLikelihood&
                ]
            },
                Transpose[
                    {
                        Values @ sorted[[All, "X"]],
                        Reverse @ Accumulate @ Reverse[
                            Values @ sorted[[All, "CrudePosteriorWeight"]]
                        ]
                    }
                ]
            ]
        },
            DynamicModule[{
                splitPts, range,
                fit
            },
                Manipulate[
                    splitPts = TakeDrop[points, Sort[Length[points] + 1 - range]];
                    If[ Length[splitPts[[1]]] > 1,
                        fit = Exp[
                            Fit[Log @ splitPts[[1]], {1, \[FormalX]}, \[FormalX]] /. \[FormalX] -> Log[\[FormalX]]
                        ],
                        fit = 0
                    ];
                    Show[
                        ListLogLogPlot[
                            DeleteCases[{}] @ splitPts,
                            PlotRange -> {{All, 1}, {All, 1}},
                            PlotLabel -> "Localisation of posterior distribution",
                            Sequence @@ style["Enclosed prior mass", "Enclosed posterior mass"]
                        ],
                        LogLogPlot[
                            fit, {\[FormalX], Min[points[[All, 1]]], 1},
                            PlotRange -> {{All, 1}, {All, 1}}
                        ],
                        Graphics[
                            Inset[
                                Style[fit, 20],
                                Scaled[{0.8, 0.2}]
                            ]
                        ]
                    ],
                    {
                        {range, {1, Ceiling[Length[points] / 3]}, "Range"},
                        1, Length[points], 1, ControlType -> IntervalSlider
                    },
                    Evaluate[Sequence @@ manipulateStyle]
                ]
            ]
        ],
        
        ListPlot[
            Log /@ Accumulate @ Values @ result[["Samples", All, "CrudePosteriorWeight"]],
            PlotLabel -> "Evidence progression",
            PlotRange -> All,
            Sequence @@ style["Iteration", "Evidence found"]
        ],
        
        ListPlot[
            result[["Samples", All, "LogLikelihood"]],
            PlotLabel -> "LogLikelihood progression",
            PlotRange -> All,
            Sequence @@ style["Iteration", "LogLikelihood"]
        ],
        
        ListPlot[
            DeleteMissing @ result[["Samples", All, "AcceptanceRate"]],
            PlotLabel -> "Acceptance rate",
            PlotRange -> {0, 1},
            ImageSize -> Large,
            Epilog -> InfiniteLine[{{0, 0.5}, {1, 0.5}}]
        ]
    }]
];

End[(*Private*)]

EndPackage[(*"BayesianStatistics"*)]