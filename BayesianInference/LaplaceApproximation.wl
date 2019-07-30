BeginPackage["LaplaceApproximation`", {"GeneralUtilities`", "BayesianConjugatePriors`", "BayesianUtilities`", "Experimental`"}]

laplacePosteriorFit;
numericalLogPosterior;
approximateEvidence;

Begin["`Private`"]

matrixD[expr_, vars_List, n_Integer, rules : _ : {}] := Normal @ SymmetrizedArray[
    {i__} :> Refine[D[expr, Sequence @@ vars[[{i}]]] /. rules],
    ConstantArray[Length[vars], n],
    Symmetric[Range[n]]
];
hessianMatrix[expr_, vars_, rules : _ : {}] := matrixD[expr, vars, 2, rules];

modelAssumptions[model : {__Distributed}] := And @@ MapThread[
    BayesianStatistics`Private`distributionDomainToConstraints,
    {
        DistributionDomain /@ model[[All, 2]],
        model[[All, 1]] 
    }
];

(* Attempts symbolic evaluation *)
modelLogLikelihood[model : {__Distributed}] := Assuming[
    Apply[And, DistributionParameterAssumptions /@ model[[All, 2]]],
    Quiet @ Catch[
        Simplify @ Total @ Replace[
            model,
            Distributed[sym_, dist_] :> If[ TrueQ @ DistributionParameterQ[dist],
                Replace[
                    LogLikelihood[dist, {sym}],
                    {
                        _LogLikelihood :> Throw[Undefined, "DistParamQ"],
                        result_ :> Simplify[result]
                    }
                ],
                Throw[$Failed, "DistParamQ"]
            ],
            {1}
        ],
        "DistParamQ"
    ]
];

Options[numericalLogPosterior] = Join[
    Options[Experimental`CreateNumericalFunction],
    {
        "ParameterDimensions" -> Automatic,
        "ActivateQ" -> True,
        "ReturnNumericalFunction" -> True
    }
];

numericalLogPosterior[
    data : _List | _Rule,
    likelihood : {__Distributed},
    prior : {__Distributed},
    varSpec : _List | _Rule,
    opts : OptionsPattern[]
] := Catch[
    Module[{
        varsIn, datIn, 
        varsOut, datOut,
        modelParams = DeleteDuplicates @ Flatten @ prior[[All, 1]],
        posIndexOut,
        paramSpec,
        logPost,
        paramDims
    },
        {varsIn, varsOut, datIn, datOut} = Replace[
            {varSpec, data},
            {
                {lst1_List, lst2_List} :> {None, lst1, None, Replace[lst2, v_?VectorQ :> List /@ v]},
                {
                    lst11_List -> lst12_List,
                    lst21_List -> lst22_List
                } :> {
                    lst11, lst12,
                    Sequence @@ Replace[{lst21, lst22}, v_?VectorQ :> List /@ v, {1}]
                },
                _ :> Throw[$Failed, "var"]
            }
        ];
        posIndexOut = PositionIndex[varsOut][[All, 1]];
        logPost = Replace[OptionValue["ActivateQ"],
            {
                True -> Refine @* Activate,
                _ -> Identity
            }
        ] @ Plus[
            Total @ Cases[
                likelihood,
                Distributed[vars_, dist_] :> If[ varsIn === None,
                    With[{
                        dat = Part[datOut, All,
                            Lookup[
                                posIndexOut,
                                Replace[Flatten[{vars}], {i_} :> i],
                                (Message[laplacePosteriorFit::depVar]; Throw[$Failed, "var"])
                            ]
                        ]
                    },
                        Inactive[LogLikelihood][dist, dat]
                    ],
                    Total @ Check[
                        ReplaceAll[
                            Inactive[LogLikelihood][dist, Flatten[{vars}]],
                            MapThread[
                                AssociationThread,
                                {
                                    ConstantArray[Join[varsIn, varsOut], Length[datOut]],
                                    Join[datIn, datOut, 2]
                                }
                            ]
                        ],
                        Throw[$Failed, "var"]
                    ]
                ],
                {1}
            ],
            Total @ Cases[
                prior,
                Distributed[vars_, dist_] :> Inactive[LogLikelihood][dist, {vars}]
            ]
        ];
        If[ TrueQ @ OptionValue["ReturnNumericalFunction"]
            ,
            paramDims = Replace[OptionValue["ParameterDimensions"], Except[KeyValuePattern[{}]] -> {}];
            paramSpec = {#, Lookup[paramDims, #, Nothing]}& /@ modelParams;
            Experimental`CreateNumericalFunction[
                paramSpec, logPost, {},
                Sequence @@ FilterRules[{opts}, Options[Experimental`CreateNumericalFunction]]
            ] @ modelParams
            ,
            logPost
        ]
    ],
    "var"
];

laplacePosteriorFit::depVar = "Only dependent variables can be defined in the likelihood specification";
laplacePosteriorFit::nmaximize = "Failed to find the posterior maximum. `1` Was returned.";
laplacePosteriorFit::assum = "Obtained assumptions `1` contain dependent or independent parameters. Please specify additional assumptions.";
laplacePosteriorFit::acyclic = "Cyclic models are not supported";
laplacePosteriorFit::dependency = "Independent variables cannot depend on others and model parameters cannot depend on dependent variables.";

Options[approximateEvidence] = DeleteDuplicatesBy[First] @ Join[
    Options[NMaximize],
    Options[FindMaximum],
    {
        "InitialGuess" -> Automatic
    }
];

approximateEvidence[
    logPostDens_,
    modelParams_List,
    assumptions_,
    opts : OptionsPattern[]
] := Module[{
    maxVals, mean, hess,
    cov,
    nParam,
    guess = OptionValue["InitialGuess"]
},
    nParam = Length @ modelParams;
    maxVals = If[ TrueQ[MatchQ[guess, KeyValuePattern[{}]] && Length[guess] >= nParam],
        FindMaximum[
            {logPostDens, assumptions},
            Evaluate @ Map[
                {#, Lookup[guess, #, Nothing]}&,
                modelParams
            ],
            Evaluate[Sequence @@ FilterRules[{opts}, Options[FindMaximum]]]
        ],
        NMaximize[
            {logPostDens, assumptions},
            modelParams,
            Sequence @@ FilterRules[{opts}, Options[NMaximize]]
        ]
    ];
    If[ !MatchQ[maxVals, {_?NumericQ, {__Rule}}],
        Message[laplacePosteriorFit::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    hess = - Replace[
        logPostDens,
        {
            fun_NumericalFunction[___] :> fun["Hessian"[mean]],
            other_ :> hessianMatrix[other, modelParams, Last[maxVals]]
        }
    ];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ LinearSolve[hess, IdentityMatrix[nParam]];
    <|
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2,
        "MAPEstimate" -> maxVals,
        "Mean" -> mean,
        "PrecisionMatrix" -> hess,
        "Parameters" -> Keys[Last[maxVals]]
    |>
];

Options[laplacePosteriorFit] = DeleteDuplicatesBy[First] @ Join[
    Options[approximateEvidence],
    Options[Experimental`CreateNumericalFunction],
    DeleteCases[Options[numericalLogPosterior], "ReturnNumericalFunction" -> _],
    {
        Assumptions -> True,
        "IncludeDensity" -> False,
        "HyperParameters" -> {}
    }
];
SetOptions[laplacePosteriorFit,
    {
        MaxIterations -> 10000
    }
];

laplacePosteriorFit[
    data : _List | _Rule,
    likelihood : {__Distributed},
    prior : {__Distributed},
    vars_,
    opts : OptionsPattern[]
] := Module[{
    logPost,
    nParam, modelParams,
    assumptions, 
    graph, result,
    varsIn, varsOut,
    cov,
    hyperParams = Replace[OptionValue["HyperParameters"], Except[_List] :> {}]
},
    {varsIn, varsOut} = Replace[vars,
        {
            l_List :> {{}, l},
            Verbatim[Rule][in_, out_] :> Flatten @* List /@ {in, out},
            other_ :> {other}
        }
    ];
    graph = modelGraph[Join[likelihood, prior], varsIn -> varsOut];
    If[ !AcyclicGraphQ[graph],
        Message[laplacePosteriorFit::acyclic];
        Return[$Failed]
    ];
    modelParams = Union @ Flatten @ prior[[All, 1]];
    nParam = Length[modelParams];
    If[ AnyTrue[
            EdgeList[graph],
            MatchQ @ Alternatives[
                DirectedEdge[Alternatives @@ varsIn, _],
                DirectedEdge[Alternatives @@ modelParams, Alternatives @@ varsOut]
            ]
        ],
        Message[laplacePosteriorFit::dependency];
        Return[$Failed]
    ];
    
    assumptions = Simplify[modelAssumptions[prior] && OptionValue[Assumptions]];
    If[ !FreeQ[assumptions, Alternatives @@ Join[varsIn, varsOut]],
        Message[laplacePosteriorFit::assum, assumptions];
        Return[$Failed]
    ];
    logPost = numericalLogPosterior[data, likelihood, prior, varsIn -> varsOut,
        "ReturnNumericalFunction" -> hyperParams === {},
        Sequence @@ FilterRules[{opts}, Options[numericalLogPosterior]]
    ];
    result = approximateEvidence[logPost, modelParams, assumptions,
        Sequence @@ FilterRules[{opts}, Options[approximateEvidence]] 
    ];
    If[ !AssociationQ[result], Return[$Failed]];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ LinearSolve[
        result["PrecisionMatrix"],
        IdentityMatrix[nParam]
    ];
    Join[
        result,
        <|
            "ModelGraph" -> graph,
            "IndependentVariables" -> varsIn,
            "DependentVariables" -> varsOut,
            "Model" -> <|
                "Likelihood" -> likelihood,
                "Prior" -> prior
            |>,
            "Posterior" -> DeleteMissing @ <|
                "RegressionCoefficientDistribution" -> MultinormalDistribution[result["Mean"], cov],
                "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"], logPost, Missing[]],
                "PredictiveDistribution" -> ParameterMixtureDistribution[
                    Replace[
                        likelihood,
                        {
                            {Distributed[_, dist_]} :> dist,
                            dists : {__Distributed} :> ProductDistribution @@ dists[[All, 2]]
                        }
                    ],
                    Distributed[modelParams, MultinormalDistribution[mean, cov]]
                ]
            |>
        |>
    ]
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]