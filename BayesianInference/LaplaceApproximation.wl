BeginPackage["LaplaceApproximation`", {"GeneralUtilities`", "BayesianConjugatePriors`", "BayesianUtilities`", "Experimental`"}]

laplacePosteriorFit;
numericalLogPosterior;
approximateEvidence;
fitPrecisionAtMax;
laplaceLogEvidence;
macKayUpdateMethod;

Begin["`Private`"]

wrapArgsInList[matrixD, 2];
matrixD[expr_, vars_List, n_Integer, rules : _ : {}] := Normal @ SymmetrizedArray[
    {i__} :> Refine[D[expr, Sequence @@ vars[[{i}]]] /. rules],
    ConstantArray[Length[vars], n],
    Symmetric[Range[n]]
];
hessianMatrix[expr_, vars_, rules : _ : {}] := matrixD[expr, vars, 2, rules];
numericD[expr_, vars_List -> pt_List, deriv_String, opts : OptionsPattern[]] :=
    CreateNumericalFunction[vars, expr, {}, opts][deriv[pt]];

laplaceLogEvidence[{max_?NumericQ, {__Rule}}, rest___] := laplaceLogEvidence[max, rest];
laplaceLogEvidence[max_?NumericQ, precisionMatrix_?numericMatrixQ] := With[{
    nParam = Length[precisionMatrix],
    det = Det[precisionMatrix]
},
    max + (nParam * Log[2 * Pi] - Log[det])/2 /; TrueQ[det > 0]
];
laplaceLogEvidence[max_?NumericQ, var_?Positive] := laplaceLogEvidence[max, {{var}}];
laplaceLogEvidence[__] := Missing[];

wrapArgsInList[{modelLogLikelihood, modelAssumptions}, 1];
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
    Options[CreateNumericalFunction],
    {
        "ParameterDimensions" -> Automatic,
        "ActivateQ" -> True,
        "ReturnNumericalFunction" -> True
    }
];

wrapArgsInList[numericalLogPosterior, {2, 3}];

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
        ] @ {
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
        };
        If[ TrueQ @ OptionValue["ReturnNumericalFunction"]
            ,
            paramDims = Replace[OptionValue["ParameterDimensions"], Except[KeyValuePattern[{}]] -> {}];
            paramSpec = {#, Lookup[paramDims, #, Nothing]}& /@ modelParams;
            CreateNumericalFunction[
                paramSpec, logPost, {2},
                Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
            ] @ modelParams
            ,
            logPost
        ]
    ],
    "var"
];

approximateEvidence::nmaximize = "Failed to find the posterior maximum. `1` Was returned";
approximateEvidence::fixedpoint1 = "Update function did not evaluate to numerical hyper parameters at `1` == `2`. `3` was returned";
approximateEvidence::fixedpoint2 = "Could not evaluate log-evidence at hyper parameters `1` == `2`";
approximateEvidence::nonposdef = "Precision matrix at `1` == `2` calculated to be nonpositive matrix. Log-evidence will not be returned" <>
", but the unnormalized density will be appended for manual fitting";

laplacePosteriorFit::depVar = "Only dependent variables can be defined in the likelihood specification";
laplacePosteriorFit::assum = "Obtained assumptions `1` contain dependent or independent parameters. Please specify additional assumptions";
laplacePosteriorFit::acyclic = "Cyclic models are not supported";
laplacePosteriorFit::dependency = "Independent variables cannot depend on others and model parameters cannot depend on dependent variables";

Options[approximateEvidence] = DeleteDuplicatesBy[First] @ Join[
    Options[NMaximize],
    Options[FindMaximum],
    Options[CreateNumericalFunction],
    {
        "InitialGuess" -> Automatic,
        "HyperParamSearchRadius" -> 0.25,
        "IncludeDensity" -> False,
        "IncludeLogLikelihood" -> False,
        "IncludeHyperParameterPath" -> False,
        "HyperParameterOptimizationMethod" -> NMaximize
    }
];

wrapArgsInList[approximateEvidence, 2];

approximateEvidence[
    dens_,
    modelParams_List,
    assumptions_,
    opts : OptionsPattern[]
] := Module[{
    maxVals, mean, precisionMat,
    nParam,
    guess = OptionValue["InitialGuess"],
    logLikelihood,
    logPostDens
},
    {logLikelihood, logPostDens} = Replace[
        dens,
        {
            {loglike_, logPrior_} :> {loglike, loglike + logPrior},
            other_ :> {Missing[], other}
        }
    ];
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
        Message[approximateEvidence::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    precisionMat = - numericD[logPostDens, modelParams -> mean, "Hessian",
        Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
    ];
    If[ !PositiveDefiniteMatrixQ[precisionMat],
        Message[approximateEvidence::nonposdef, modelParams, mean]
    ];
    DeleteMissing @ <|
        "LogEvidence" -> If[ !MissingQ[precisionMat],
            laplaceLogEvidence[First[maxVals], precisionMat],
            Missing[]
        ],
        "Maximum" -> maxVals,
        "Mean" -> mean,
        "PrecisionMatrix" -> precisionMat,
        "LogLikelihood" -> If[ TrueQ @ OptionValue["IncludeLogLikelihood"],
            Activate[logLikelihood /. Last[maxVals]],
            Missing[]
        ],
        "Parameters" -> Keys[Last[maxVals]],
        "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"] || MissingQ[precisionMat], logPostDens, Missing[]]
    |>
];

(* implements the hyperparameter optimization scheme described in the PhD thesis of David MacKay *)
approximateEvidence[
    dens_,
    modelParams_List,
    assumptions_,
    dists : {__Distributed}, (* distributions of hyperparameters *)
    opts : OptionsPattern[]
] := With[{
    hyperParams = Flatten @ dists[[All, 1]],
    prior = Total @ MapThread[
        LogLikelihood[#1, {#2}]&,
        {dists[[All, 2]], dists[[All, 1]]}
    ]
},
    Module[{
        radius = OptionValue["HyperParamSearchRadius"],
        storedVals = <||>,
        numFun,
        fit, bestfit = <||>, maxHyper,
        mean, precisionMat,
        nHyper = Length[hyperParams],
        assum2 = modelAssumptions[dists],
        logPostDens,
        hyperPost, hyperPostMax = DirectedInfinity[-1],
        hyperParamMethod = Replace[
            OptionValue["HyperParameterOptimizationMethod"],
            {
                {FixedPoint, spec___} /; MatchQ[{spec}, KeyValuePattern[{}]] :> {spec},
                FixedPoint -> {},
                _ -> NMaximize
            }
        ],
        includeLogLike
    },
        includeLogLike = TrueQ[OptionValue["IncludeLogLikelihood"]] || hyperParamMethod =!= NMaximize;
        logPostDens = Simplify[dens, Assumptions -> assumptions && assum2, TimeConstraint -> {2, 10}];
        numFun[numVals : {__?NumericQ}] := numFun[numVals] = With[{
            (* NMaximize will block the hyperparams, so rules are only necessary outside of NMaximize *)
            rules = If[ VectorQ[hyperParams, NumericQ], {}, AssociationThread[hyperParams, numVals]]
        },
            fit = approximateEvidence[
                Refine[logPostDens /. rules], 
                modelParams, assumptions,
                "InitialGuess" -> If[ Length[storedVals] > 0,
                    First[Nearest[Normal[storedVals[[All, 2]]], numVals, {1, radius}], Automatic],
                    Automatic
                ],
                "IncludeLogLikelihood" -> includeLogLike,
                opts
            ];
            hyperPost = fit["LogEvidence"] + (prior /. rules);
            If[ TrueQ[hyperPost >= hyperPostMax],
                {bestfit, hyperPostMax} = {fit, hyperPost};
            ];
            storedVals[numVals] = {hyperPost, Last @ fit["Maximum"]};
            hyperPost
        ];
        
        maxHyper = If[ hyperParamMethod === NMaximize,
            NMaximize[{numFun[hyperParams], assum2}, hyperParams, Sequence @@ FilterRules[{opts}, Options[NMaximize]]],
            With[{
                initialGuess = Lookup[hyperParamMethod, "InitialGuess", ConstantArray[0.1, nHyper]],
                updateFun = Lookup[hyperParamMethod, "UpdateFunction", macKayUpdateMethod[]],
                maxIterations = Lookup[hyperParamMethod, MaxIterations, 1000],
                sameTest = Lookup[hyperParamMethod, SameTest, 
                    With[{tol = Abs @ Lookup[hyperParamMethod, Tolerance, 1*^-6]},
                        Function[Max @ Abs[First @ #1 - First @ #2] < tol]
                    ]
                ],
                priorDeriv = Replace[
                    Lookup[hyperParamMethod, "LogPriorDerivatives", 0&],
                    fun : Except[_List] :> ConstantArray[fun, nHyper] 
                ]
            },
                numFun[initialGuess];
                Replace[
                    {params_List, result_?AssociationQ} :> {
                        hyperPostMax,
                        Thread[hyperParams -> params]
                    } 
                ] @ Catch[
                    FixedPoint[
                        Apply @ Function[{prevGuess, prevFit},
                            With[{
                                updateGuess = Replace[
                                    updateFun[prevGuess, prevFit, priorDeriv],
                                    fail : Except[{__?NumericQ}] :> (
                                        Message[approximateEvidence::fixedpoint1, hyperParams, prevGuess, fail];
                                        Throw[$Failed, "FixedPoint"]
                                    )
                                ]
                            },
                                Replace[
                                    numFun[updateGuess],
                                    Except[_?NumericQ] :> (
                                        Message[approximateEvidence::fixedpoint2, hyperParams, updateGuess];
                                        Throw[$Failed, "FixedPoint"]
                                    )
                                ];
                                {updateGuess, fit (*numFun updates fit as a side effect *)}
                            ]
                        ],
                        {initialGuess, fit},
                        maxIterations,
                        SameTest -> sameTest
                    ],
                    "FixedPoint"
                ]
            ]
        ];
        If[ !MatchQ[maxHyper, {_?NumericQ, {__Rule}}],
            Message[approximateEvidence::nmaximize, Short[maxHyper]];
            Return[$Failed]
        ];
        mean = Values[Last[maxHyper]];
        precisionMat = - numericD[numFun[hyperParams], hyperParams -> mean, "Hessian",
            Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
        ];
        If[ !PositiveDefiniteMatrixQ[precisionMat],
            Message[approximateEvidence::nonposdef, hyperParams, mean];
            precisionMat = Missing[]
        ];
        Prepend[<|
            "LogEvidence" -> If[ !MissingQ[precisionMat],
                laplaceLogEvidence[First[maxHyper], precisionMat],
                Missing[]
            ],
            "ConditionalLogEvidence" -> bestfit["LogEvidence"]
        |>] @ Join[
            bestfit,
            <|
                "HyperParameters" -> DeleteMissing @ <|
                    "Maximum" -> maxHyper,
                    "Mean" -> mean,
                    "PrecisionMatrix" -> precisionMat,
                    "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"] || MissingQ[precisionMat],
                        numFun[hyperParams],
                        Missing[]
                    ],
                    "Distribution" -> If[ !MissingQ[precisionMat],
                        MultinormalDistribution[mean, BayesianConjugatePriors`Private`symmetrizeMatrix @ Inverse[precisionMat]],
                        Missing[]
                    ],
                    "HyperParameterPath" -> If[ TrueQ @ OptionValue["IncludeHyperParameterPath"] || MissingQ[precisionMat],
                        storedVals,
                        Missing[]
                    ]
                |>
            |>
        ]
        
    ]
];
macKayUpdateMethod[] := macKayUpdateMethod[1];

macKayUpdateMethod[nParam : 1, ___] := Function[{params, fit, deriv},
    With[{
        logAlpha = First[params],
        priorDeriv = First[deriv],
        trAinv = Tr[Inverse @ fit["PrecisionMatrix"]],
        ew2 = Total[fit["Mean"]^2],
        k = Length[fit["Mean"]]
    },
        Log @ {
            Divide[ (* new alpha *)
                k,
                ew2 + trAinv - 2 * priorDeriv[logAlpha]
            ]
        }
    ]
];

macKayUpdateMethod[nParam : 2, ndat_Integer] := Function[{params, fit, deriv},
    Module[{
        logAlpha = params[[1]],
        logBeta = params[[2]],
        k = Length[fit["Mean"]],
        alpha, beta,
        trAinv = Tr[Inverse @ fit["PrecisionMatrix"]],
        ew2 = Total[fit["Mean"]^2],
        ed2
    },
        {alpha, beta} = Exp[{logAlpha, logBeta}];
        ed2 = -(2/beta) * (fit["LogLikelihood"] + (ndat/2) * Log[(2 Pi)/beta]); (* Sum of square errors *)
        Log @ {
            Divide[ (* new alpha *)
                k,
                ew2 + trAinv - 2 * deriv[[1]][logAlpha]
            ],
            Divide[ (* new beta *)
                ndat - k + alpha * trAinv,
                ed2 - 2 * deriv[[2]][logBeta]
            ]
        }
    ]
]

Options[laplacePosteriorFit] = DeleteDuplicatesBy[First] @ Join[
    Options[approximateEvidence],
    DeleteCases[Options[numericalLogPosterior], "ReturnNumericalFunction" -> _],
    {
        Assumptions -> True,
        "HyperParameters" -> {}
    }
];
SetOptions[laplacePosteriorFit,
    {
        MaxIterations -> 10000
    }
];

wrapArgsInList[laplacePosteriorFit, {2, 3}];

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
    hyperParams = Replace[
        OptionValue["HyperParameters"],
        {
            d_Distributed :> {d},
            Except[_List] :> {},
            list_List :> Map[
                Replace[el : Except[_Distributed] :> Distributed[el, CauchyDistribution[0, 2]]],
                Flatten[list]
            ]
        }
    ]
},
    {varsIn, varsOut} = Replace[vars,
        {
            l_List :> {{}, l},
            Verbatim[Rule][in_, out_] :> Flatten @* List /@ {in, out},
            other_ :> {other}
        }
    ];
    graph = Graph[
        modelGraph[Join[likelihood, prior, hyperParams], varsIn -> varsOut],
        VertexStyle -> Thread[Flatten[First /@ hyperParams] -> Blue]
    ];
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
        "ReturnNumericalFunction" -> False,
        Sequence @@ FilterRules[{opts}, Options[numericalLogPosterior]]
    ];
    If[ !TrueQ[OptionValue["IncludeLogLikelihood"]] && OptionValue["HyperParameterOptimizationMethod"] === NMaximize,
        logPost = Total[logPost]
    ];
    result = approximateEvidence[logPost,
        modelParams, assumptions,
        Replace[hyperParams, {} :> Unevaluated[Sequence[]]],
        Sequence @@ FilterRules[{opts}, Options[approximateEvidence]] 
    ];
    If[ !AssociationQ[result], Return[$Failed]];
    cov = With[{presMat = result["PrecisionMatrix"]},
        If[ !MissingQ[presMat],
            BayesianConjugatePriors`Private`symmetrizeMatrix @ Inverse[presMat],
            Missing[]
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
                "Prior" -> prior,
                "HyperParameters" -> hyperParams
            |>,
            "Posterior" -> If[ !MissingQ[cov], 
                DeleteMissing @ <|
                    "RegressionCoefficientDistribution" -> MultinormalDistribution[result["Mean"], cov],
                    "PredictiveDistribution" -> ParameterMixtureDistribution[
                        Replace[
                            likelihood,
                            {
                                {Distributed[_, dist_]} :> dist,
                                dists : {__Distributed} :> ProductDistribution @@ dists[[All, 2]]
                            }
                        ] /. Replace[result[["HyperParameters", "Maximum", 2]], _Missing -> {}],
                        Distributed[modelParams, MultinormalDistribution[result["Mean"], cov]]
                    ]
                |>,
                Missing[]
            ]
        |>
    ]
];

fitPrecisionAtMax::noDat = "No data provided";
fitPrecisionAtMax::insuf = "`1` points is insufficient for computing the precision matrix. Requires at least `2` points.";
fitPrecisionAtMax::poorfit1 = "Waring: test points are highly correlated or highly localized (`1`). Expect poor fit of precision matrix";
fitPrecisionAtMax::poorfit2 = "Waring: log-evidence range in data is `1`. Expect poor fit of precision matrix";

fitPrecisionAtMax[<||>] := (Message[fitPrecisionAtMax::noDat]; $Failed);
fitPrecisionAtMax[path_?AssociationQ /; AllTrue[path, MatchQ[{_, {__Rule}}]]] := fitPrecisionAtMax[path[[All, 1]]];
fitPrecisionAtMax[path_?numericMatrixQ] := With[{
    dim2 = Dimensions[path][[2]]
},
    fitPrecisionAtMax[
        AssociationThread[path[[All, Range[dim2 - 1]]], path[[All, dim2]]]
    ] /; dim2 > 1
];

fitPrecisionAtMax[path_?AssociationQ /; AllTrue[path, NumericQ]] := Module[{
    max = TakeLargest[path, 1],
    deltaPoints,
    deltaEvidence,
    npts = Length[path],
    dim = Length @ First @ Keys[path],
    fun, covElements,
    test,
    symCov,
    mat, mattr, ls
},
    If[ !TrueQ[npts > dim * (dim + 1) / 2 + 1],
        Message[fitPrecisionAtMax::insuf, npts, dim * (dim + 1) / 2 + 2];
        Return[$Failed]
    ];
    symCov = Normal @ SymmetrizedArray[{i_, j_} :> \[FormalC][i, j], dim * {1, 1}, Symmetric[{1, 2}]];
    covElements = Union @@ symCov;
    deltaPoints = Keys[path] - ConstantArray[First[Keys[max]], npts];
    test = Abs @ SingularValueList[Covariance[deltaPoints]];
    If[ Divide @@ MinMax[test] < 1*^-4 || Max[test] < 1*^-10,
        Message[fitPrecisionAtMax::poorfit1, test]
    ];
    
    deltaEvidence = Values[path] - First[max];
    test = Max @ Abs[deltaEvidence];
    If[ test < 1*^-5,
        Message[fitPrecisionAtMax::poorfit2, test]
    ];
    fun = With[{
        vec = Table[Indexed[Slot[1], i], {i, dim}]
    },
        Function[
            Evaluate @ Last @ Normal[
                CoefficientArrays[vec . symCov . vec, covElements]
            ]
        ]
    ];
    mat = fun /@ deltaPoints;
    mattr = Transpose[mat];
    ls = LinearSolve[mattr . mat];
    (* Echo[ls["ConditionNumber"]]; *)
    symCov /. AssociationThread[ (* Fit a parabola to the residuals around the maximum *)
        covElements,
        -2 * ls[mattr . deltaEvidence]
    ]
];
fitPrecisionAtMax[path_?AssociationQ /; !AllTrue[path, NumericQ]] := fitPrecisionAtMax[
    Select[path, NumericQ[#[[1]]]&]
];
fitPrecisionAtMax[___] := (Message[fitPrecisionAtMax::noDat]; $Failed);
End[]

EndPackage[(* "BayesianConjugatePriors`" *)]