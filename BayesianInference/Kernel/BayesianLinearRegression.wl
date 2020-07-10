BeginPackage["BayesianConjugatePriors`", {"GeneralUtilities`", "BayesianUtilities`"}]

BayesianLinearRegression::usage = "BayesianLinearRegression[{x1, x2, ...} -> {y1, y2, ...}, {f1, f2, ...}, {var1, var2, ...}] performs a Bayesion linear fit.";

Begin["`Private`"]

BayesianLinearRegression::dataFormat = "Data format `1` not recognised";
BayesianLinearRegression::dataDims = "Number of independent variables `1` does not match dimensions of input data `2`";
BayesianLinearRegression::designMat =  "Failed to construct the design matrix. `1` was returned";
BayesianLinearRegression::prior = "Prior parameters `1` do not have the right dimensions";
Options[BayesianLinearRegression] = {
    IncludeConstantBasis -> True,
    "PriorParameters" -> Automatic,
    "IncludeFunctions" -> False
};

BayesianLinearRegression[data_, basis : Except[_List], rest___] := BayesianLinearRegression[data, {basis}, rest];
BayesianLinearRegression[data_, basis_, independentVar : Except[_List], rest___] := 
    BayesianLinearRegression[data, basis, {independentVar}, rest];

BayesianLinearRegression[data_?MatrixQ, basis_, independentVars_List, rest___] := With[{
    nvars = Length[independentVars]
},
    BayesianLinearRegression[
        Take[data, All, nvars] -> Drop[data, None, nvars],
        basis,
        independentVars,
        rest
    ] /; nvars < Dimensions[data][[2]]
];

BayesianLinearRegression[data : _Rule | {__Rule}, basis_List, independentVars_List, opts : OptionsPattern[]] := Module[{
    formattedData = regressionDataNormalForm[data],
    dimIn1 = Length[independentVars],
    dimIn2,
    dimOut,
    designMat,
    result,
    fullBasis
},
    If[ formattedData === $Failed,  
        Message[BayesianLinearRegression::dataFormat, Short[data]];
        Return[$Failed]
    ];
   
   dimIn2 = Dimensions[formattedData[[1]]][[2]];
   dimOut = Dimensions[formattedData[[2]]][[2]];
   If[ dimIn1 =!= dimIn2,
        Message[BayesianLinearRegression::dataDims, dimIn1, dimIn2];
        Return[$Failed]  
    ];
   
    designMat = Replace[
        DesignMatrix[
            Join[
                formattedData[[1]],
                ConstantArray[0, {Length[formattedData[[1]]], 1}] ,(*Add dummy y-values that don't affect the design matrix anyway *)
                2
            ],
            basis,
            independentVars,
            Sequence @@ FilterRules[{opts}, Options[DesignMatrix]]
        ],
        numMat_?(MatrixQ[#, NumericQ] &) :> Developer`ToPackedArray[numMat]
    ];
    If[ !MatrixQ[designMat],
        Message[BayesianLinearRegression::designMat, designMat];
        Return[$Failed]
    ];
    result = bayesianLinearRegressionInternal[designMat, formattedData[[2]], OptionValue["PriorParameters"]];
    fullBasis = First @ DesignMatrix[
        {Append[independentVars, 0]},
        basis,
        independentVars,
        Sequence @@ FilterRules[{opts}, Options[DesignMatrix]]
    ];
    If[ AssociationQ[result],
        AppendTo[
            result["Functions"],
            Map[
                Function[{zeroOrOne}, (* the "PredictiveDistribution" and "UnderlyingValueDistribution" are the same, save for a single "+ 1" *)
                    With[{
                        inVec = fullBasis
                    },
                        If[ dimOut > 1,
                            Function[
                                With[{dim = #Nu - dimOut + 1},
                                    Simplify @ MultivariateTDistribution[
                                        inVec . #B,
                                        (#V/dim) * (inVec . #LambdaInverse . inVec + zeroOrOne),
                                        dim
                                    ]
                                ]
                            ],
                            Function[
                                Simplify @ StudentTDistribution[inVec.#B, Sqrt[(#V/#Nu)*(inVec . #LambdaInverse . inVec + zeroOrOne)], #Nu]
                            ]
                        ]
                    ]
                ],
                <|
                    "PredictiveDistribution" -> 1,
                    "UnderlyingValueDistribution" -> 0
                |>
            ]
        ];
        Join[
            KeyDrop[result, "Functions"],
            <|
                "Posterior" -> Map[
                    # @ result["PosteriorParameters"]&,
                    result["Functions"]
                ],
                "Prior" -> Map[
                    # @ result["PriorParameters"]&,
                    result["Functions"]
                ],
                "Basis" -> fullBasis,
                "IndependentVariables" -> independentVars
            |>,
            If[ TrueQ @ OptionValue["IncludeFunctions"],
                result[[{"Functions"}]],
                <||>
            ]
        ],
        $Failed
    ]
];

symmetrizeMatrix = Replace[{
    mat_?SquareMatrixQ /; MatrixQ[mat, NumericQ] && !SymmetricMatrixQ[mat] :> Divide[mat + Transpose[mat], 2]
}];

bayesianLinearRegressionInternal[dMat_, yMat_, prior : Except[KeyValuePattern[{}] | {_, _, _, _, _}]] := 
    bayesianLinearRegressionInternal[dMat, yMat, {}];

bayesianLinearRegressionInternal[dMat_, yMat_, prior : KeyValuePattern[{}]] := With[{
    dimIn = Dimensions[dMat][[2]],
    dimOut = Dimensions[yMat][[2]]
},
    bayesianLinearRegressionInternal[
        dMat,
        yMat,
        With[{
            priorLambda = symmetrizeMatrix @ Lookup[prior, "Lambda", IdentityMatrix[dimIn]/100]
        },
            {   (* Prior that assumes ignorance but is still normalized *)
                Lookup[prior, "B", ConstantArray[0, {dimIn, dimOut}]],
                priorLambda,
                symmetrizeMatrix @ Lookup[prior, "LambdaInverse", Inverse[priorLambda]],
                Lookup[prior, "V", IdentityMatrix[dimOut]/100],
                Lookup[prior, "Nu", 1/100 + dimOut - 1]
            }
        ]
    ]
];

(* for univariate regression, flatten the y-dimension to a vector *)
bayesianLinearRegressionInternal[dMat_, yMat_?MatrixQ /; Dimensions[yMat][[2]] === 1 , prior : {_, _, _, _, _}] := bayesianLinearRegressionInternal[
    dMat,
    Flatten[yMat],
    Replace[
        prior,
        {b_?MatrixQ, lambda_?SquareMatrixQ, lambdaInv_?SquareMatrixQ, {{v_}}, nu_} :> {Flatten[b], lambda, lambdaInv, v, nu}
    ]
];

bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?MatrixQ ,
    prior : {b_?MatrixQ, lambda_?SquareMatrixQ, _, v_?SquareMatrixQ, nu : Except[_List]}
] /; Or[
    Dimensions[b] =!= {Length[lambda], Length[v]}, 
    Dimensions[yMat][[2]] =!= Length[v],
    Dimensions[designMat][[2]] =!= Length[lambda]
] := (
    Message[BayesianLinearRegression::prior, prior];
    $Failed
);

bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?VectorQ ,
    prior : {b_?VectorQ, lambda_?SquareMatrixQ, _, v : Except[_List], nu : Except[_List]}
] /; Length[b] =!= Length[lambda] || Dimensions[designMat][[2]] =!= Length[lambda] := (
    Message[BayesianLinearRegression::prior, prior];
    $Failed
);

(* Multivariate regression *)
bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?MatrixQ /; Dimensions[yMat][[2]] > 1,
    prior : {b_?MatrixQ, lambda_?SquareMatrixQ, invLambda_?SquareMatrixQ, v_?SquareMatrixQ, nu : Except[_List]}
] /; And[
    Dimensions[b] === {Length[lambda], Length[v]},
    Dimensions[yMat][[2]] === Length[v],
    Length[designMat] === Length[yMat],
    Dimensions[designMat][[2]] === Length[lambda],
    Dimensions[lambda] === Dimensions[invLambda]
] := Module[{
    posteriorParameters = updateParameters[prior, designMat, yMat]
},
    <|
        "LogEvidence" -> logEvidence[prior, posteriorParameters, designMat, yMat],
        "PriorParameters" -> AssociationThread[{"B", "Lambda", "LambdaInverse","V", "Nu"}, prior],
        "PosteriorParameters" -> AssociationThread[{"B", "Lambda", "LambdaInverse","V", "Nu"}, posteriorParameters],
        "Functions" -> <|
            "RegressionCoefficientDistribution" -> With[{
                d = Dimensions[b][[2]],
                fun = symmetrizeMatrix
            },
                Function[MatrixTDistribution[#B, fun @ #LambdaInverse, #V, #Nu - d + 1]]
            ],
            "ErrorDistribution" -> Function[InverseWishartMatrixDistribution[#Nu, #V]],
            "FullPosterior" -> Function[
                conditionalProductDistribution[
                    Distributed[\[FormalCapitalB], MatrixNormalDistribution[#B, #LambdaInverse, \[FormalCapitalSigma]]],
                    Distributed[\[FormalCapitalSigma], InverseWishartMatrixDistribution[#Nu, #V]]
                ]
            ]
        |>
    |>
];

(* special simplifications for univariate regression *)
bayesianLinearRegressionInternal[designMat_?MatrixQ, yVec_?VectorQ,
    prior : {b_?VectorQ, lambda_?SquareMatrixQ, invLambda_?SquareMatrixQ, v : Except[_List], nu : Except[_List]}
] /; And[
    Length[b] === Length[lambda] === Dimensions[designMat][[2]],
    Length[designMat] === Length[yVec],
    Dimensions[lambda] === Dimensions[invLambda] 
]:= Module[{
    posteriorParameters = updateParameters[prior, designMat, yVec]
},
    <|
        "LogEvidence" -> logEvidence[prior, posteriorParameters, designMat, yVec],
        "PriorParameters" -> AssociationThread[{"B", "Lambda", "LambdaInverse","V", "Nu"}, prior],
        "PosteriorParameters" -> AssociationThread[{"B", "Lambda", "LambdaInverse","V", "Nu"}, posteriorParameters],
        "Functions" -> <|
            "RegressionCoefficientDistribution" -> With[{
                fun = symmetrizeMatrix
            },
                Function[MultivariateTDistribution[#B, fun[(#V/#Nu) * #LambdaInverse], #Nu]]
            ],
            "ErrorDistribution" -> Function[InverseGammaDistribution[#Nu/2, #V/2]],
            "FullPosterior" -> Function[
                conditionalProductDistribution[
                    Distributed[\[FormalB], MultinormalDistribution[#B, #LambdaInverse * \[FormalCapitalV]]],
                    Distributed[\[FormalCapitalV], InverseGammaDistribution[#Nu/2, #V/2]]
                ]
            ]
        |>
    |>
];

updateParameters[
    {b0_?VectorQ, lambda0_?SquareMatrixQ, invLambda0_?SquareMatrixQ, v0 : Except[_List], nu0 : Except[_List]},
    designMat_,
    yVec_?VectorQ
] := Replace[
    updateParameters[
        {List /@ b0, lambda0, invLambda0, {{v0}}, nu0},
        designMat,
        List /@ yVec
    ],
    {bb_, ll_, llinv_, {{vv_}}, nn_} :> {Flatten[bb], ll, llinv, vv, nn}
];

updateParameters[
    {b0_?MatrixQ, lambda0_?SquareMatrixQ, invLambda0_?SquareMatrixQ, v0_?MatrixQ, nu0 : Except[_List]},
    designMat_?MatrixQ,
    yMat_?MatrixQ
] := Module[{
    designTrans = Transpose[designMat],
    designSq, nDat, nOut,
    bUpdate, lambdaUpdate, invLambdaUpdate, vUpdate, nuUpdate
},
    {nDat, nOut} = Dimensions[yMat];
    designSq = designTrans.designMat;
    lambdaUpdate = symmetrizeMatrix[designSq + lambda0];
    invLambdaUpdate = symmetrizeMatrix @ Inverse[lambdaUpdate];
    bUpdate = invLambdaUpdate.(designTrans.yMat + lambda0.b0);
    vUpdate = With[{
        residuals = yMat - designMat.bUpdate,
        bDiff = bUpdate - b0
    },
        v0 + Transpose[residuals].residuals + Transpose[bDiff].lambda0.bDiff
    ];
    nuUpdate = nu0 + nDat;
    {bUpdate, lambdaUpdate, invLambdaUpdate, vUpdate, nuUpdate}
];

(* Multivariate *)
logEvidence[
    prior : {b0_?MatrixQ, l0_?MatrixQ, invl0_?MatrixQ, v0_?MatrixQ, nu0_},
    posteriorParameters : {bn_?MatrixQ, ln_?MatrixQ, invln_?MatrixQ, vn_?MatrixQ, nun_},
    designMat_?MatrixQ, yMat_?MatrixQ
] /; NoneTrue[Flatten @ {Diagonal[l0], Diagonal[v0], nu0}, TrueQ @* NonPositive] := Simplify @ Module[{ 
    sampledB = bn,
    sampledCov = Divide[vn, nun],
    logLikelihood
},
    logLikelihood = Total[(* P[D\[Conditioned]B,\[CapitalSigma]]*)
        MapThread[
            LogLikelihood[
                MultinormalDistribution[#1.sampledB, symmetrizeMatrix @ sampledCov],
                {#2}
            ]&,
            {designMat, yMat}
        ]
    ];
    Plus[
        logLikelihood,
        Subtract @@ Apply[
            Plus[
                LogLikelihood[
                    InverseWishartMatrixDistribution[#5, symmetrizeMatrix @ #4],
                    {sampledCov}
                ],
                LogLikelihood[
                    MatrixNormalDistribution[#1, symmetrizeMatrix @ #3, sampledCov],
                    {sampledB}
                ]
            ]&,
            {prior, posteriorParameters},
            {1}
        ]
    ]
];

(* Univariate *)
logEvidence[
    prior : {b0_?VectorQ, l0_?MatrixQ, invl0_?MatrixQ, v0 : Except[_List], nu0_},
    posteriorParameters : {bn_?VectorQ, ln_?MatrixQ, invln_?MatrixQ, vn : Except[_List], nun_},
    designMat_?MatrixQ, yVec_?VectorQ
] /; NoneTrue[Flatten @ {Diagonal[l0], v0, nu0}, TrueQ @* NonPositive] := Simplify @ Module[{ 
    sampledB = bn,
    sampledVar = Divide[vn, nun],
    logLikelihood
},
    logLikelihood = Total[
        MapThread[
            LogLikelihood[
                NormalDistribution[#1.sampledB, Sqrt[sampledVar]], {#2}
            ]&,
            {designMat, yVec}
        ]
    ];
    Plus[
        logLikelihood,
        Subtract @@ Apply[
            Plus[
                LogLikelihood[
                    InverseGammaDistribution[#5/2, #4/2],
                    {sampledVar}
                ],
                LogLikelihood[
                    MultinormalDistribution[
                        #1,
                        symmetrizeMatrix[sampledVar * #3]
                    ],
                    {sampledB}
                ]
            ]&,
            {prior, posteriorParameters},
            {1}
        ]
    ]
];

logEvidence[___] := Undefined;

regressionDataNormalForm[
    correctFormat : (in : {{__} ..}?MatrixQ -> out : {{__} ..}?MatrixQ)
] /; Length[in] === Length[out] := correctFormat;
regressionDataNormalForm[listOfRules : {__Rule}] := regressionDataNormalForm[listOfRules[[All, 1]] -> listOfRules[[All, 2]]];
regressionDataNormalForm[in_List?VectorQ -> out_] := regressionDataNormalForm[List /@ in -> out];
regressionDataNormalForm[in_ -> out_List?VectorQ] := regressionDataNormalForm[in -> List /@ out];
regressionDataNormalForm[_] := $Failed;

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]