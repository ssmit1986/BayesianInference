BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

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

BayesianLinearRegression[data_, basis_List, independentVars_List, opts : OptionsPattern[]] := Module[{
    formattedData = regressionDataNormalForm[data],
    dimIn1 = Length[independentVars],
    dimIn2,
    dimOut,
    designMat,
    result
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
    If[ AssociationQ[result],
        AppendTo[
            result["Functions"],
            "PredictiveDistribution" -> With[{
                inVec = First @ DesignMatrix[
                    {Append[independentVars, 0]},
                    basis,
                    independentVars,
                    Sequence @@ FilterRules[{opts}, Options[DesignMatrix]]
                ]
            },
                If[ dimOut > 1,
                    Function[
                        With[{dim = #Nu - dimOut + 1},
                            Simplify @ MultivariateTDistribution[
                                inVec . #B,
                                (#V/dim) * (inVec.LinearSolve[#Lambda][inVec] + 1),
                                dim
                            ]
                        ]
                    ],
                    Function[
                        Simplify @ StudentTDistribution[inVec.#B, Sqrt[(#V/#Nu)*(inVec.LinearSolve[#Lambda][inVec] + 1)], #Nu]
                    ]
                ]
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
                "Basis" -> basis,
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
    mat_?SquareMatrixQ /; ! SymmetricMatrixQ[mat] :> Normal @ SymmetrizedArray[mat, Dimensions[mat], Symmetric[{1, 2}]]
}];

bayesianLinearRegressionInternal[dMat_, yMat_, prior : Except[KeyValuePattern[{}] | {_, _, _, _}]] := 
    bayesianLinearRegressionInternal[dMat, yMat, {}];

bayesianLinearRegressionInternal[dMat_, yMat_, prior : KeyValuePattern[{}]] := With[{
    dimIn = Dimensions[dMat][[2]],
    dimOut = Dimensions[yMat][[2]]
},
    bayesianLinearRegressionInternal[
        dMat,
        yMat,
        {   (* Prior that assumes ignorance but is still normalized *)
            Lookup[prior, "B", ConstantArray[0, {dimIn, dimOut}]],
            Lookup[prior, "Lambda", IdentityMatrix[dimIn]/100],
            Lookup[prior, "V", IdentityMatrix[dimOut]/100],
            Lookup[prior, "Nu", 1/100 + dimOut - 1]
        }
    ]
];

(* for univariate regression, flatten the y-dimension to a vector *)
bayesianLinearRegressionInternal[dMat_, yMat_?MatrixQ /; Dimensions[yMat][[2]] === 1 , prior : {_, _, _, _}] := bayesianLinearRegressionInternal[
    dMat,
    Flatten[yMat],
    Replace[
        prior,
        {b_?MatrixQ, lambda_?SquareMatrixQ, {{v_}}, nu_} :> {Flatten[b], lambda, v, nu}
    ]
];

bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?MatrixQ ,
    prior : {b_?MatrixQ, lambda_?SquareMatrixQ, v_?SquareMatrixQ, nu : Except[_List]}
] /; Or[
    Dimensions[b] =!= {Length[lambda], Length[v]}, 
    Dimensions[yMat][[2]] =!= Length[v],
    Dimensions[designMat][[2]] =!= Length[lambda]
] := (
    Message[BayesianLinearRegression::prior, prior];
    $Failed
);

bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?VectorQ ,
    prior : {b_?VectorQ, lambda_?SquareMatrixQ, v : Except[_List], nu : Except[_List]}
] /; Length[b] =!= Length[lambda] || Dimensions[designMat][[2]] =!= Length[lambda] := (
    Message[BayesianLinearRegression::prior, prior];
    $Failed
);

(* Multivariate regression *)
bayesianLinearRegressionInternal[designMat_?MatrixQ, yMat_?MatrixQ /; Dimensions[yMat][[2]] > 1,
    prior : {b_?MatrixQ, lambda_?SquareMatrixQ, v_?SquareMatrixQ, nu : Except[_List]}
] /; And[
    Dimensions[b] === {Length[lambda], Length[v]},
    Dimensions[yMat][[2]] === Length[v],
    Length[designMat] === Length[yMat],
    Dimensions[designMat][[2]] === Length[lambda]
] := Module[{
    posteriorParameters = updateParameters[prior, designMat, yMat],
    dimIn = Length[b],
    dimOut = Dimensions[b][[2]]
},
    <|
        "LogEvidence" -> logEvidence[prior, posteriorParameters, designMat, yMat],
        "PriorParameters" -> AssociationThread[{"B", "Lambda", "V", "Nu"}, prior],
        "PosteriorParameters" -> AssociationThread[{"B", "Lambda", "V", "Nu"}, posteriorParameters],
        "Functions" -> <|
            "RegressionCoefficientDistribution" -> With[{
                d = dimOut,
                id = IdentityMatrix[dimIn],
                fun = symmetrizeMatrix
            },
                Function[MatrixTDistribution[#B, fun @ LinearSolve[#Lambda, id], #V, #Nu - d + 1]]
            ],
            "ErrorDistribution" -> Function[InverseWishartMatrixDistribution[#Nu, #V]]
        |>
    |>
];

(* special simplifications for univariate regression *)
bayesianLinearRegressionInternal[designMat_?MatrixQ, yVec_?VectorQ,
    prior : {b_?VectorQ, lambda_?SquareMatrixQ, v : Except[_List], nu : Except[_List]}
] /; Length[b] === Length[lambda] === Dimensions[designMat][[2]] && Length[designMat] === Length[yVec] := Module[{
    posteriorParameters = updateParameters[prior, designMat, yVec],
    dimIn = Length[b]
},
    <|
        "LogEvidence" -> logEvidence[prior, posteriorParameters, designMat, yVec],
        "PriorParameters" -> AssociationThread[{"B", "Lambda", "V", "Nu"}, prior],
        "PosteriorParameters" -> AssociationThread[{"B", "Lambda", "V", "Nu"}, posteriorParameters],
        "Functions" -> <|
            "RegressionCoefficientDistribution" -> With[{
                id = IdentityMatrix[dimIn], fun = symmetrizeMatrix
            },
                Function[MultivariateTDistribution[#B, fun[(#V/#Nu) * LinearSolve[#Lambda, id]], #Nu]]
            ],
            "ErrorDistribution" -> Function[InverseGammaDistribution[#Nu/2, #V/2]]
        |>
    |>
];

updateParameters[
    {b0_?VectorQ, lambda0_?MatrixQ, v0 : Except[_List], nu0 : Except[_List]},
    designMat_,
    yVec_?VectorQ
] := Replace[
    updateParameters[
        {List /@ b0, lambda0, {{v0}}, nu0},
        designMat,
        List /@ yVec
    ],
    {bb_, ll_, {{vv_}}, nn_} :> {Flatten[bb], ll, vv, nn}
];

updateParameters[
    {b0_?MatrixQ, lambda0_?MatrixQ, v0_?MatrixQ, nu0 : Except[_List]},
    designMat_?MatrixQ,
    yMat_?MatrixQ
] := Module[{
    designTrans = Transpose[designMat],
    designSq, nDat, nOut,
    bUpdate, lambdaUpdate, vUpdate, nuUpdate
},
    {nDat, nOut} = Dimensions[yMat];
    designSq = designTrans.designMat;
    bUpdate = LinearSolve[designSq + lambda0, (designTrans.yMat + lambda0.b0)];
    lambdaUpdate = designSq + lambda0;
    vUpdate = With[{
        residuals = yMat - designMat.bUpdate,
        bDiff = bUpdate - b0
    },
        v0 + Transpose[residuals].residuals + Transpose[bDiff].lambda0.bDiff
    ];
    nuUpdate = nu0 + nDat;
    {bUpdate, lambdaUpdate, vUpdate, nuUpdate}
];

(* Multivariate *)
logEvidence[
    prior : {b0_?MatrixQ, l0_?MatrixQ, v0_?MatrixQ, nu0_},
    posteriorParameters : {bn_?MatrixQ, ln_?MatrixQ, vn_?MatrixQ, nun_},
    designMat_?MatrixQ, yMat_?MatrixQ
] /; NoneTrue[Flatten @ {Diagonal[l0], Diagonal[v0], nu0}, TrueQ @* NonPositive] := Simplify @ Module[{ 
    sampledB = bn,
    sampledCov = Divide[vn, nun],
    logLikelihood,
    dimIn = Length[bn]
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
                    InverseWishartMatrixDistribution[#4, symmetrizeMatrix @ #3],
                    {sampledCov}
                ],
                LogLikelihood[
                    MatrixNormalDistribution[#1, symmetrizeMatrix @ LinearSolve[#2, IdentityMatrix[dimIn]], sampledCov],
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
    prior : {b0_?VectorQ, l0_?MatrixQ, v0 : Except[_List], nu0_},
    posteriorParameters : {bn_?VectorQ, ln_?MatrixQ, vn : Except[_List], nun_},
    designMat_?MatrixQ, yVec_?VectorQ
] /; NoneTrue[Flatten @ {Diagonal[l0], v0, nu0}, TrueQ @* NonPositive] := Simplify @ Module[{ 
    sampledB = bn,
    sampledVar = Divide[vn, nun],
    logLikelihood,
    dimIn = Length[bn]
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
                    InverseGammaDistribution[#4/2, #3/2],
                    {sampledVar}
                ],
                LogLikelihood[
                    MultinormalDistribution[
                        #1,
                        symmetrizeMatrix[sampledVar * LinearSolve[#2, IdentityMatrix[dimIn]]]
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