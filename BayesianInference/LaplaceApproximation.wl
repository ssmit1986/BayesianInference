BeginPackage["LaplaceApproximation`", {"GeneralUtilities`"}]

laplacePosteriorFit;

Begin["`Private`"]

matrixD[expr_, vars_List, n_Integer] := Nest[Refine @ Grad[#, vars]&, expr, n];
hessianMatrix = Function[matrixD[#1, #2, 2]];

modelAssumptions[model : {__Distributed}] := Apply[And, DistributionParameterAssumptions /@ model[[All, 2]]];

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

dataToReplacementRules[data_, vars_] := With[{
},
    Join @@ Append[
        MapThread[
            Function[{v, d},
                MapThread[Rule, {ConstantArray[v, n], d}, 2]
            ],
            {vars, data}
        ],
        2
    ]
];

laplacePosteriorFit::nmaximize = "Failed to find the posterior maximum. `1` Was returned";
Options[laplacePosteriorFit] = Options[NMaximize];

laplacePosteriorFit[
    data : (datIn_?MatrixQ -> datOut_?MatrixQ) /; Length[datIn] === Length[datOut],
    model : {__Distributed},
    varsIn_?VectorQ -> varsOut_?VectorQ,
    opts : OptionsPattern[]
] /; And[
    Length[varsIn] === Dimensions[datIn][[2]],
    Length[varsOut] === Dimensions[datOut][[2]]
] := Module[{
    logPost = modelLogLikelihood[model],
    logPostAtData,
    nDat = Length[datIn],
    nParam,
    modelParams,
    outDists,
    priorDists,
    priorAssum,
    maxVals,
    hess,
    replacementRules
},
    If[ FailureQ[logPost] || logPost === Undefined,
        Return[logPost]
    ];
    modelParams = Complement[Union @ Flatten[model[[All, 1]]], varsOut];
    nParam = Length[modelParams];
    outDists = Cases[
        model,
        Distributed[sym_, _] /; MemberQ[sym, Alternatives @@ varsOut, {0, Infinity}]
    ];
    priorDists = Complement[model, outDists];
    priorAssum = modelAssumptions[priorDists];
    replacementRules = MapThread[
        AssociationThread,
        {
            ConstantArray[Join[varsIn, varsOut], nDat],
            Join[datIn, datOut, 2]
        }
    ];
    logPostAtData = Simplify @ ConditionalExpression[
        Total @ ReplaceAll[
            logPost,
            replacementRules
        ],
        priorAssum
    ];
    maxVals = NMaximize[logPostAtData, modelParams, Sequence @@ FilterRules[{opts}, Options[NMaximize]]];
    If[ !MatchQ[maxVals, {_?NumericQ, {__Rule}}],
        Message[laplacePosteriorFit::nmaximize, Short[maxVals]];
        Return[$Failed]
    ];
    
    hess = -Total @ ReplaceAll[
        hessianMatrix[logPost, modelParams] /. Last[maxVals],
        replacementRules
    ];
    <|
        "Parameters" -> Keys[Last[maxVals]],
        "Mean" -> Values[Last[maxVals]],
        "PrecisionMatrix" -> hess,
        "CovarianceMatrix" -> LinearSolve[hess, IdentityMatrix[nParam]],
        "MaxVal" -> First[maxVals],
        "LogEvidence" -> First[maxVals] + (nParam * Log[2 * Pi] - Log[Det[hess]])/2
    |>
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]