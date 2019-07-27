BeginPackage["LaplaceApproximation`", {"GeneralUtilities`", "BayesianConjugatePriors`"}]

laplacePosteriorFit;

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

(* Assumes all rules are such that the LogLikelihoods evaluate to numbers *)
modelLogLikelihood[
    model : {__Distributed},
    rules : (_?AssociationQ | {__Rule}) /; AllTrue[Flatten @ Values[rules], NumericQ]
] := Total @ Replace[
    model,
    Distributed[sym_, dist_] :> LogLikelihood[dist, {Lookup[rules, sym]}],
    {1}
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

modelGraph[fullModel : {__Distributed}, varsIn_?VectorQ -> varsOut_?VectorQ] := Module[{
    allSymbols = Union @ Join[
        varsIn, varsOut,
        Flatten @ fullModel[[All, 1]]
    ],
    edges
},
    edges = DeleteDuplicates @ Flatten @ Map[
        Function[dist,
            Thread @ DirectedEdge[
                #,
                Cases[dist[[2]], Alternatives @@ allSymbols, {0, Infinity}]
            ]& /@ Flatten[{dist[[1]]}]
        ],
        fullModel
    ];
    Graph[edges, VertexLabels -> "Name"]
];

laplacePosteriorFit::nmaximize = "Failed to find the posterior maximum. `1` Was returned.";
laplacePosteriorFit::assum = "Obtained assumptions `1` contain dependent or independent parameters. Please specify additional assumptions.";
laplacePosteriorFit::acyclic = "Cyclic models are not supported";
laplacePosteriorFit::dependency = "Independent variables cannot depend on others and model parameters cannot depend on dependent variables.";

Options[laplacePosteriorFit] = Join[
    Options[NMaximize],
    {
        Assumptions -> True
    }
];
SetOptions[laplacePosteriorFit,
    {
        MaxIterations -> 10000
    }
];

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
    assumptions, maxVals,
    replacementRules,
    hess, cov, mean,
    graph
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
    logPost = Simplify @ ConditionalExpression[
        Plus[
            Total @ ReplaceAll[
                loglike,
                replacementRules
            ],
            logprior
        ],
        assumptions
    ];
    maxVals = NMaximize[logPost, modelParams, Sequence @@ FilterRules[{opts}, Options[NMaximize]]];
    If[ !MatchQ[maxVals, {_?NumericQ, {__Rule}}],
        Message[laplacePosteriorFit::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    hess = - hessianMatrix[logPost, modelParams, Association @ Last[maxVals]];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ LinearSolve[hess, IdentityMatrix[nParam]];
    <|
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2,
        "Parameters" -> Keys[Last[maxVals]],
        "Posterior" -> <|
            "RegressionCoefficientDistribution" -> MultinormalDistribution[mean, cov],
            "PrecisionMatrix" -> hess,
            "PredictiveDistribution" -> ParameterMixtureDistribution[
                Replace[
                    likelihood,
                    {
                        {Distributed[_, dist_]} :> dist,
                        dists : {__Distributed} :> ProductDistribution @@ dists[[All, 2]]
                    }
                ],
                Distributed[
                    Keys[Last[maxVals]],
                    MultinormalDistribution[mean, cov]
                ]
            ],
            "UnnormalizedLogDensity" -> logPost,
            "MAP" -> maxVals
        |>,
        "Model" -> <|
            "Likelihood" -> likelihood,
            "Prior" -> prior
        |>,
        "ModelGraph" -> graph,
        "IndependentVariables" -> varsIn,
        "DependentVariables" -> varsOut
    |>
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]