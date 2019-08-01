BeginPackage["LaplaceApproximation`", {"GeneralUtilities`", "BayesianConjugatePriors`", "BayesianUtilities`", "Experimental`"}]

laplacePosteriorFit;
numericalLogPosterior;
approximateEvidence;
computePrecisionFromPath;

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

wrapArgsInList[approximateEvidence, {2, 3}];

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
            CreateNumericalFunction[
                paramSpec, logPost, {},
                Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
            ] @ modelParams
            ,
            logPost
        ]
    ],
    "var"
];

approximateEvidence::nmaximize = "Failed to find the posterior maximum. `1` Was returned.";
laplacePosteriorFit::depVar = "Only dependent variables can be defined in the likelihood specification";
laplacePosteriorFit::assum = "Obtained assumptions `1` contain dependent or independent parameters. Please specify additional assumptions.";
laplacePosteriorFit::acyclic = "Cyclic models are not supported";
laplacePosteriorFit::dependency = "Independent variables cannot depend on others and model parameters cannot depend on dependent variables.";

Options[approximateEvidence] = DeleteDuplicatesBy[First] @ Join[
    Options[NMaximize],
    Options[FindMaximum],
    Options[CreateNumericalFunction],
    {
        "InitialGuess" -> Automatic,
        "HyperParamSearchRadius" -> 0.25,
        "IncludeDensity" -> False,
        "IncludeHyperParmeterPath" -> False
    }
];

wrapArgsInList[approximateEvidence, 2];

approximateEvidence[
    logPostDens_,
    modelParams_List,
    assumptions_,
    opts : OptionsPattern[]
] := Module[{
    maxVals, mean, hess,
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
        Message[approximateEvidence::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    hess = - numericD[logPostDens, modelParams -> mean, "Hessian",
        Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
    ];
    DeleteMissing @ <|
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2,
        "Maximum" -> maxVals,
        "Mean" -> mean,
        "PrecisionMatrix" -> hess,
        "Parameters" -> Keys[Last[maxVals]],
        "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"], logPostDens, Missing[]]
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
    hyperParams2 = dists[[All, 1]],
    hyperParamsDists = dists[[All, 2]],
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
        mean, hess,
        nHyper = Length[hyperParams],
        assum2 = modelAssumptions[dists],
        logPostDens,
        evidence
    },
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
                opts
            ];
            If[ TrueQ[fit["LogEvidence"] >= Lookup[bestfit, "LogEvidence", DirectedInfinity[-1]]],
                bestfit = fit
            ];
            evidence = fit["LogEvidence"] + (prior /. rules);
            storedVals[numVals] = {evidence, Last @ fit["Maximum"]};
            evidence
        ];
        
        maxHyper = NMaximize[{numFun[hyperParams], assum2}, hyperParams, Sequence @@ FilterRules[{opts}, Options[NMaximize]]];
        If[ !MatchQ[maxHyper, {_?NumericQ, {__Rule}}],
            Message[approximateEvidence::nmaximize, Short[maxHyper]];
            Return[$Failed]
        ];
        mean = Values[Last[maxHyper]];
        hess = - numericD[numFun[hyperParams], hyperParams -> mean, "Hessian",
            Sequence @@ FilterRules[{opts}, Options[CreateNumericalFunction]]
        ];
        Prepend[
            "LogEvidence" -> First[maxHyper] + (nHyper * Log[2 * Pi] - Log[Det[hess]])/2
        ] @ Join[
            bestfit,
            <|
                "HyperParameters" -> DeleteMissing @ <|
                    "Maximum" -> maxHyper,
                    "Mean" -> mean,
                    "PrecisionMatrix" -> hess,
                    "PriorDensity" -> Total @ MapThread[
                        LogLikelihood[#1, {#2}]&,
                        {hyperParamsDists, hyperParams2 /. Last[maxHyper]}
                    ],
                    "UnnormalizedLogDensity" -> If[ TrueQ @ OptionValue["IncludeDensity"], numFun[hyperParams], Missing[]],
                    "Distribution" -> MultinormalDistribution[
                        mean,
                        BayesianConjugatePriors`Private`symmetrizeMatrix @ Inverse[hess]
                    ],
                    "HyperParmeterPath" -> If[ TrueQ @ OptionValue["IncludeHyperParmeterPath"],
                        storedVals,
                        Missing[]
                    ]
                |>
            |>
        ]
        
    ]
];

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
                Replace[el : Except[_Distributed] :> Distributed[el, CauchyDistribution[]]],
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
    result = approximateEvidence[logPost,
        modelParams, assumptions,
        Replace[hyperParams, {} :> Unevaluated[Sequence[]]],
        Sequence @@ FilterRules[{opts}, Options[approximateEvidence]] 
    ];
    If[ !AssociationQ[result], Return[$Failed]];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ Inverse[result["PrecisionMatrix"]];
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
            "Posterior" -> DeleteMissing @ <|
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
            |>
        |>
    ]
];

computePrecisionFromPath::noDat = "No data provided";
computePrecisionFromPath::insuf = "`1` points is insufficient for computing the precision matrix. Requires at least `2` points.";
computePrecisionFromPath::poorfit1 = "Waring: test points are highly correlated or highly localized (`1`). Expect poor fit of precision matrix";
computePrecisionFromPath::poorfit2 = "Waring: log-evidence range in data is `1`. Expect poor fit of precision matrix";

computePrecisionFromPath[<||>] := (Message[computePrecisionFromPath::noDat]; $Failed);
computePrecisionFromPath[path_?AssociationQ /; AllTrue[path, MatchQ[{_, {__Rule}}]]] := computePrecisionFromPath[path[[All, 1]]];
computePrecisionFromPath[path_?numericMatrixQ] := With[{
    dim2 = Dimensions[path][[2]]
},
    computePrecisionFromPath[
        AssociationThread[path[[All, Range[dim2 - 1]]], path[[All, dim2]]]
    ] /; dim2 > 1
];

computePrecisionFromPath[path_?AssociationQ /; AllTrue[path, NumericQ]] := Module[{
    max = TakeLargest[path, 1],
    deltaPoints,
    deltaEvidence,
    npts = Length[path],
    dim = Length @ First @ Keys[path],
    fun, keys,
    test,
    symCov,
    mat, mattr, ls
},
    If[ !TrueQ[npts > dim * (dim + 1) / 2 + 1],
        Message[computePrecisionFromPath::insuf, npts, dim * (dim + 1) / 2 + 2];
        Return[$Failed]
    ];
    symCov = Normal @ SymmetrizedArray[{i_, j_} :> \[FormalC][i, j], dim * {1, 1}, Symmetric[{1, 2}]];
    deltaPoints = Keys[path] - ConstantArray[First[Keys[max]], npts];
    test = Abs @ SingularValueList[Covariance[deltaPoints]];
    If[ Divide @@ MinMax[test] < 1*^-4 || Max[test] < 1*^-10,
        Message[computePrecisionFromPath::poorfit1, test]
    ];
    
    deltaEvidence = Values[path] - First[max];
    test = Max @ Abs[deltaEvidence];
    If[ test < 1*^-3,
        Message[computePrecisionFromPath::poorfit2, test]
    ];
    {fun, keys} = With[{
        body = KeySort @ GroupBy[
            Thread @ Rule[
                Flatten @ symCov,
                Flatten @ Apply[
                    KroneckerProduct,
                    ConstantArray[Table[Indexed[Slot[1], i], {i, dim}], 2]
                ]
            ],
            First -> Last,
            Total
        ]
    },
        {Function[Evaluate @ Values @ body], Keys[body]}
    ];
    mat = fun /@ deltaPoints;
    mattr = Transpose[mat];
    ls = LinearSolve[mattr . mat];
    (* Echo[ls["ConditionNumber"]]; *)
    symCov /. Thread[ (* Fit a parabola to the residuals around the maximum *)
        keys -> -2 * ls[mattr . deltaEvidence]
    ]
];
computePrecisionFromPath[path_?AssociationQ /; !AllTrue[path, NumericQ]] := computePrecisionFromPath[
    Select[path, NumericQ[#[[1]]]&]
];
computePrecisionFromPath[___] := (Message[computePrecisionFromPath::noDat]; $Failed);
End[]

EndPackage[(* "BayesianConjugatePriors`" *)]