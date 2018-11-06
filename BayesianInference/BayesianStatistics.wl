(* ::Package:: *)

BeginPackage["BayesianStatistics`", {"BayesianUtilities`"}];

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
    positionsScale = Position[priorSpecification, "ScaleParameter"]
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

defineInferenceProblem::insuffInfo = "Not enough information was provide to define the problem. Failed at: `1`";
defineInferenceProblem::logLike = "Unable to automatically construct the loglikelihood function for distribution `1`. Please construct one manually";
defineInferenceProblem::prior = "Unable to automatically construct the log prior PDF function for distribution `1`. Please construct one manually";
defineInferenceProblem::failed = "Failure. `1` does not yield numerical results in the required domain";

defineInferenceProblem[] := {
    "Data",
    "Parameters",
    "LogLikelihoodFunction",
    "LogPriorPDFFunction",
    "GeneratingDistribution",
    "PriorDistribution",
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
        keys = Keys[assoc];
        If[ MemberQ[keys, "Data"] && VectorQ[assoc["Data"]],
            assoc["Data"] = List /@ assoc["Data"]
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
            SubsetQ[keys, tempKeys = {"GeneratingDistribution", "Data", "Parameters"}],
                AppendTo[assoc, "LogLikelihoodFunction" -> logLikelihoodFunction @@ Values[assoc[[tempKeys]]]],
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
] := Module[{
    constraints = And @@ (Less @@@ parameters[[All, {2, 1, 3}]]),
    logPDF,
    dim = Length[parameters]
},
    logPDF = Activate @ Function[ paramVector,
        Evaluate[
            ReplaceAll[
                FullSimplify[
                    Log[pdf],
                    constraints
                ],
                Thread[
                    parameters[[All, 1]] -> Table[
                        Inactive[Part][paramVector, i],
                        {i, 1, dim}
                    ]
                ]
            ]
        ]
    ];
    constraints = Activate @ Function[
        Evaluate[
            constraints /. Thread[
                parameters[[All, 1]] -> Table[
                    Inactive[Part][#, i],
                    {i, 1, dim}
                ]
            ]
        ]
    ];
    
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
    dim = Length[parameters],
    dataDim = Dimensions[data][[2]],
    logLike,
    constraints,
    domain = DistributionDomain[dist]
},
    constraints = FullSimplify @ And[
        DistributionParameterAssumptions[dist],
        And @@ (Less @@@ parameters[[All, {2, 1, 3}]])
    ];
    logLike = Activate @ Function[
        {paramVector, dataPoint},
        Evaluate[
            ReplaceAll[
                With[{
                    vars = Table[
                        Inactive[Part][dataPoint, i],
                        {i, 1, dataDim}
                    ]
                },
                    FullSimplify[
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
                            And @@ (Less @@@ Transpose @ Insert[
                                Transpose[
                                    Cases[
                                        domain,
                                        dom_Interval :> First[dom],
                                        {0, 1}
                                    ]
                                ],
                                vars,
                                2
                            ])
                        ] 
                    ]
                ],
                Thread[
                    parameters[[All, 1]] -> Table[
                        Inactive[Part][paramVector, i],
                        {i, 1, dim}
                    ]
                ]
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
    constraints = Activate @ Function @ Evaluate[
        And @@ Cases[
            BooleanConvert[constraints, "CNF"],
            _Less | _Greater | _GreaterEqual | _LessEqual,
            {0, 1}
        ] /. Thread[
            parameters[[All, 1]] -> Table[
                Inactive[Part][#, i],
                {i, 1, dim}
            ]
        ]
    ];
    Compile[{
        {input, _Real, 1}
    },
        If[ constraints[input],
            Total[logLike[input, #]& /@ data],
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
    Merge[
        {
            sorted,
            <|"X" -> #|> & /@ AssociationThread[keys, xValues],
            <|"CrudePosteriorWeight" -> #|> & /@ AssociationThread[keys, weights * Exp[Values @ sorted[[All, "LogLikelihood"]]]]
        },
        Join @@ # &
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

    resultTable = ParallelTable[
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

predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)],
    posteriorFraction : (_?NumericQ) : 1
] /; !MissingQ[result["GeneratingDistribution"]] :=
    predictiveDistribution[
        result,
        result["GeneratingDistribution"],
        posteriorFraction
    ];

predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)],
    posteriorFraction : (_?NumericQ) : 1
] /; MissingQ[result["GeneratingDistribution"]] := "No distribution specified";

predictiveDistribution[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)],
    dist : Except[_?NumericQ],
    posteriorFraction : (_?NumericQ) : 1
] /; Between[posteriorFraction, {0, 1}] := Module[{
    truncatedResult = takePosteriorFraction[result, posteriorFraction]
},
    MixtureDistribution[
        Values @ truncatedResult[["Samples", All, "CrudePosteriorWeight"]],
        dist @@ #& /@ Values @ truncatedResult[["Samples", All, "Point"]]
    ]
];

calculationReport[inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&)]] := TabView[{
    DynamicModule[{
        min = Max[result[["Samples", All, "LogLikelihood"]]] - 100
    },
        Column[{
            With[{
                dat = Transpose @ {
                    Values @ result[["Samples", All, "SampledX", "Mean"]],
                    Values @ result[["Samples", All, "LogLikelihood"]]
                }
            },
                Dynamic[
                    ListLogLinearPlot[
                        dat,
                        PlotRange -> {{0, 1}, {min, All}},
                        PlotLabel -> "Enclosed prior mass vs log likelihood",
                        ImageSize -> Large
                    ],
                    TrackedSymbols :> {min}
                ]
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
        PlotRange -> {{All, 1}, {All, 1}},
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
        DeleteMissing @ result[["Samples", All, "AcceptanceRate"]],
        PlotLabel -> "Acceptance Ratio",
        PlotRange -> {0, 1},
        ImageSize -> Large,
        Epilog -> InfiniteLine[{{0, 0.5}, {1, 0.5}}]
    ]
}];

End[(*Private*)]

EndPackage[(*"BayesianStatistics"*)]