BeginPackage["LaplaceApproximation`", {"GeneralUtilities`", "BayesianConjugatePriors`", "BayesianUtilities`", "Experimental`"}]

laplacePosteriorFit;
numericalLogPosterior;

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
        "ActivateQ" -> False,
        "ReturnNumericalFunction" -> True
    }
];

numericalLogPosterior[
    likelihood : {__Distributed},
    prior : {__Distributed},
    dataSpec_Rule,
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
        {varsIn, datIn, varsOut, datOut} = Replace[
            dataSpec,
            {
                Verbatim[Rule][lst1_List, lst2_List] :> {None, None, lst1, Replace[lst2, v_?VectorQ :> List /@ v]},
                Verbatim[Rule][
                    lst11_List -> lst12_List,
                    lst21_List -> lst22_List
                ] :> {
                    lst11, Replace[lst12, v_?VectorQ :> List /@ v],
                    lst21, Replace[lst22, v_?VectorQ :> List /@ v]
                },
                _ :> Throw[$Failed, "var"]
            }
        ];
        posIndexOut = PositionIndex[varsOut][[All, 1]];
        logPost = Replace[OptionValue["ActivateQ"],
            {
                True -> Function[FullSimplify[#, TimeConstraint -> {2, 20}]] @* Activate,
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

Options[laplacePosteriorFit] = DeleteDuplicatesBy[First] @ Join[
    Options[NMaximize],
    Options[FindMaximum],
    Options[Experimental`CreateNumericalFunction],
    {
        Assumptions -> True,
        "IncludeDensity" -> False,
        "InitialGuess" -> Automatic
    }
];
SetOptions[laplacePosteriorFit,
    {
        MaxIterations -> 10000
    }
];

laplacePosteriorFit[
    nFun_Experimental`NumericalFunction[modelParams__],
    assumptions_,
    opts : OptionsPattern[]
] := Module[{
    maxVals, mean, hess,
    cov,
    flatParams = Flatten @ {modelParams},
    nParam,
    guess = OptionValue["InitialGuess"]
},
    nParam = Length @ flatParams;
    nFun[modelParams];
    maxVals = If[ TrueQ[MatchQ[guess, KeyValuePattern[{}]] && Length[guess] >= nParam],
        FindMaximum[
            {nFun[modelParams], assumptions},
            Evaluate @ Map[
                {#, Lookup[guess, #, Nothing]}&,
                flatParams
            ],
            Evaluate[Sequence @@ FilterRules[{opts}, Options[FindMaximum]]]
        ],
        NMaximize[
            {nFun[modelParams], assumptions},
            flatParams,
            Sequence @@ FilterRules[{opts}, Options[NMaximize]]
        ]
    ];
    If[ !MatchQ[maxVals, {_?NumericQ, {__Rule}}],
        Message[laplacePosteriorFit::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    hess = - nFun["Hessian"[mean]];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ LinearSolve[hess, IdentityMatrix[nParam]];
    <|
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2,
        "Parameters" -> Keys[Last[maxVals]],
        "Posterior" -> DeleteMissing @ <|
            "RegressionCoefficientDistribution" -> MultinormalDistribution[mean, cov],
            "PrecisionMatrix" -> hess,
            "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"], nFun[modelParams], Missing[]],
            "MAPEstimate" -> maxVals
        |>
    |>
]

laplacePosteriorFit[
    data : (datIn_?MatrixQ -> datOut_?MatrixQ) /; Length[datIn] === Length[datOut],
    likelihood : {__Distributed},
    prior : {__Distributed},
    varsIn_?VectorQ -> varsOut_?VectorQ,
    opts : OptionsPattern[]
] /; And[
    Length[varsIn] === Dimensions[datIn][[2]],
    Length[varsOut] === Dimensions[datOut][[2]]
] := Module[{
    loglike = modelLogLikelihood[likelihood],
    logprior = modelLogLikelihood[prior],
    logPost,
    nDat = Length[datIn],
    nParam, modelParams,
    assumptions, 
    replacementRules,
    graph, result
},
    If[ FailureQ[loglike] || loglike === Undefined || FailureQ[logprior] || logprior === Undefined,
        Return[$Failed]
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
    replacementRules = MapThread[
        AssociationThread,
        {
            ConstantArray[Join[varsIn, varsOut], nDat],
            Join[datIn, datOut, 2]
        }
    ];
    logPost = Experimental`CreateNumericalFunction[
        modelParams,
        Refine @ Plus[
            Total @ ReplaceAll[loglike, replacementRules],
            logprior
        ],
        {},
        Sequence @@ FilterRules[{opts}, Options[Experimental`CreateNumericalFunction]]
    ];
    result = laplacePosteriorFit[logPost[modelParams], assumptions, opts];
    If[ !AssociationQ[result], Return[$Failed]];
    result["Posterior", "PredictiveDistribution"] = ParameterMixtureDistribution[
        Replace[
            likelihood,
            {
                {Distributed[_, dist_]} :> dist,
                dists : {__Distributed} :> ProductDistribution @@ dists[[All, 2]]
            }
        ],
        Distributed[
            modelParams,
            result["Posterior", "RegressionCoefficientDistribution"]
        ]
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
            |>
        |>
    ]
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]