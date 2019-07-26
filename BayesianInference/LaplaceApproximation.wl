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

laplacePosteriorFit::nmaximize = "Failed to find the posterior maximum. `1` Was returned.";
laplacePosteriorFit::assum = "Obtained assumptions `1` contain dependent or independent parameters. Please specify additional assumptions.";
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
    model : {__Distributed},
    prior : {__Distributed},
    varsIn_?VectorQ -> varsOut_?VectorQ,
    opts : OptionsPattern[]
] /; And[
    Length[varsIn] === Dimensions[datIn][[2]],
    Length[varsOut] === Dimensions[datOut][[2]]
] := Module[{
    loglike = modelLogLikelihood[model],
    logprior = modelLogLikelihood[prior],
    logPostAtData,
    nDat = Length[datIn],
    nParam, modelParams,
    assumptions, maxVals,
    replacementRules,
    hess, cov, mean
},
    If[ FailureQ[loglike] || loglike === Undefined || FailureQ[logprior] || logprior === Undefined,
        Return[$Failed]
    ];
    modelParams = Union @ Flatten @ prior[[All, 1]];
    nParam = Length[modelParams];
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
    logPostAtData = Simplify @ ConditionalExpression[
        Plus[
            Total @ ReplaceAll[
                loglike,
                replacementRules
            ],
            logprior
        ],
        assumptions
    ];
    maxVals = NMaximize[logPostAtData, modelParams, Sequence @@ FilterRules[{opts}, Options[NMaximize]]];
    If[ !MatchQ[maxVals, {_?NumericQ, {__Rule}}],
        Message[laplacePosteriorFit::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    mean = Values[Last[maxVals]];
    hess = - hessianMatrix[logPostAtData, modelParams, Association @ Last[maxVals]];
    cov = BayesianConjugatePriors`Private`symmetrizeMatrix @ LinearSolve[hess, IdentityMatrix[nParam]];
    <|
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2,
        "Parameters" -> Keys[Last[maxVals]],
        "Posterior" -> <|
            "RegressionCoefficientDistribution" -> MultinormalDistribution[mean, cov],
            "PrecisionMatrix" -> hess,
            "PredictiveDistribution" -> ParameterMixtureDistribution[
                Replace[
                    model,
                    {
                        {Distributed[_, dist_]} :> dist,
                        dists : {__Distributed} :> ProductDistribution @@ dists[[All, 2]]
                    }
                ],
                Distributed[
                    Keys[Last[maxVals]],
                    MultinormalDistribution[mean, cov]
                ]
            ]
        |>,
        "Model" -> model,
        "IndependentVariables" -> varsIn,
        "DependentVariables" -> varsOut
    |>
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]