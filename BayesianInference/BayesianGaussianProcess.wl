(* Wolfram Language Package *)

BeginPackage["BayesianGaussianProcess`", { "BayesianUtilities`", "BayesianStatistics`"}]
(* Exported symbols added here with SymbolName::usage *)  

gaussianProcessNestedSampling;
predictFromGaussianProcess;

Begin["`Private`"] (* Begin Private Context *) 

(*
usage example. In this example, the kernel function still has parameters that can be filled in later:

sym[] = covarianceMatrix[
    Range[5],
    Function[{pt1, pt2}, #2 + Exp[-(pt1 - pt2)^2/#1^2]],
    #3
];

sym[args__] := Function[Evaluate[sym[]]][args]
*)

nullKernelPattern = HoldPattern[Function[Repeated[_, {0, 1}], 0 | 0., ___]];

covarianceMatrix[points_List, kernel : nullKernelPattern, nugget_] :=
    nugget /@ points;

covarianceMatrix[points_List, kernel : Except[nullKernelPattern], nugget_] :=
    Plus[
        SymmetrizedArray[
            {i_, j_} :> kernel @@ points[[{i, j}]],
            ConstantArray[Length[points], 2],
            Symmetric[{1, 2}]
        ],
        SymmetrizedArray[
            {i_, i_} :> nugget[points[[i]]],
            ConstantArray[Length[points], 2],
            Symmetric[{1, 2}]
        ]
    ];

compiledCovarianceMatrix[points_List, kernel_, nugget_, vars : {__Symbol}, opts : OptionsPattern[]] :=
    With[{
        matrix = Normal @ covarianceMatrix[points, kernel, nugget]
    },
        Compile[
            Evaluate[
                Transpose[{
                    vars,
                    ConstantArray[_Real, Length[vars]]
                }]
            ],
            matrix,
            RuntimeAttributes -> {Listable},
            opts
        ]
    ];
Options[compiledCovarianceMatrix] = Options[Compile];

compiledKandKappa[
    points1_List,
    kernel : nullKernelPattern,
    nugget_,
    opts : OptionsPattern[]
] := With[{
    rank = Length[Dimensions[points1]] - 1,
    l1 = Length[points1]
},
    With[{
        cf1 = Function[{points2},
            SparseArray[{}, {l1, Length[points2]}]
        ],
        cf2 = Compile[{
            {points2, _Real, rank}
        },
            nugget[points2],
            RuntimeAttributes -> {Listable},
            opts
        ]
    },
        Function[
            <|
                "k" -> cf1[#],
                "kappa" -> Flatten[cf2[#]]
            |>
        ]
    ]
];

compiledKandKappa[
    points1_List,
    kernel : Except[nullKernelPattern],
    nugget_,
    opts : OptionsPattern[]
] := With[{
    rank1 = Length[Dimensions[points1]],
    rank2 = Length[Dimensions[points1]] - 1 
},
    With[{
        cf1 = Compile[{
            {points2, _Real, rank1}
        },
            Table[
                kernel[i, j],
                {i, points1},
                {j, points2}
            ],
            RuntimeAttributes -> {Listable},
            opts
        ],
        cf2 = Compile[{
            {points2, _Real, rank2}
        },
            kernel[points2, points2] + nugget[points2],
            RuntimeAttributes -> {Listable},
            opts
        ]
    },
        Function[
            <|
                "k" -> cf1[#],
                "kappa" -> Flatten[cf2[#]]
            |>
        ]
    ]
];
Options[compiledKandKappa] = Options[Compile];

matrixInverseAndDet[matrix_List?(MatrixQ[#, NumericQ]&)] :=
    Module[{
        ls = LinearSolve[matrix],
        absdet
    },
        absdet = Abs[Tr[ls[[2, 3, 1]], Times]];
        <|
            "Inverse" -> ls,
            "Det" -> absdet
        |>
    ];

matrixInverseAndDet[matrix_SparseArray?(MatrixQ[#, NumericQ]&)] :=
    Module[{
        ls = LinearSolve[matrix],
        absdet
    },
        absdet = Abs[Tr[ls["getL"], Times] * Tr[ls["getU"], Times]];
        <|
            "Inverse" -> ls,
            "Det" -> absdet
        |>
    ];

matrixInverseAndDet[matrixDiagonal_List?(VectorQ[#, NumericQ]&)] :=
    <|
        "Inverse" -> Function[Divide[#, matrixDiagonal]],
        "Det" -> Abs[Times @@ matrixDiagonal]
    |>

gaussianProcessLogLikelihood[data : {__Rule}, rest___] :=
    gaussianProcessLogLikelihood[data[[All, 1]] -> data[[All, 2]], rest];

gaussianProcessLogLikelihood[
    Rule[dataIn_List, dataOut_List] /; Length[dataIn] === Length[dataOut],
    kernel_, (* Kernel has to give numerical results after evaluation *)
    nugget_,
    meanFunction : _ : Function[0]
] := gaussianProcessLogLikelihood[
    dataOut - meanFunction /@ dataIn,
    matrixInverseAndDet @ covarianceMatrix[
        dataIn,
        kernel,
        nugget
    ]
];

gaussianProcessLogLikelihood[
    meanAdjustedOutputVector_List,
    inverseCov_Association
] := - 0.5 * Plus[
    Length[meanAdjustedOutputVector] * Log[2. * Pi],
    Log[inverseCov["Det"]],
    meanAdjustedOutputVector . inverseCov["Inverse"][meanAdjustedOutputVector]
];

gaussianProcessNestedSampling[data_, kernel_, nugget_, meanFunction_, variables : {_Symbol, _?NumericQ, _?NumericQ}, opts : OptionsPattern[]] :=
    gaussianProcessNestedSampling[data, kernel, meanFunction, {variables}, opts];

gaussianProcessNestedSampling[data : {__Rule}, rest___] :=
    gaussianProcessNestedSampling[data[[All, 1]], data[[All, 2]], rest];

gaussianProcessNestedSampling[Rule[dataIn_List, dataOut_List] /; Length[dataIn] === Length[dataOut], rest___] :=
    gaussianProcessNestedSampling[dataIn, dataOut, rest];

gaussianProcessNestedSampling[data_?(AssociationQ[#] && KeyExistsQ[#, "Input"] && KeyExistsQ[#, "Output"]&), rest___] :=
    Module[{
        tempResult = gaussianProcessNestedSampling[data["Input", "NormalizedData"], data["Output", "NormalizedData"], rest]
    },
        If[ AssociationQ[tempResult] && AssociationQ[tempResult["GaussianProcessData"]],
            AppendTo[
                tempResult["GaussianProcessData"],
                "DataPreProcessors" -> data[[All, {"Function", "InverseFunction"}]]
            ]
        ];
        tempResult
    ];

gaussianProcessNestedSampling[
    dataIn_?(MatrixQ[#, NumericQ] || VectorQ[#, NumericQ]&),
    dataOut_?(VectorQ[#, NumericQ]&),
    kernelFunction_,
    nuggetFunction_,
    meanFunction_,
    variablePrior_,
    variables : {{_Symbol, _?NumericQ, _?NumericQ}..},
    opts : OptionsPattern[]
] := With[{
    vars = variables[[All, 1]],
    inputData = Developer`ToPackedArray[dataIn],
    outputData = Developer`ToPackedArray[dataOut],
    parallelRuns = OptionValue["ParallelRuns"]
},
    Module[{
        nullKernelQ = MatchQ[kernelFunction, nullKernelPattern],
        kernel,
        nugget,
        mean,
        kAndKappa,
        invCovFun,
        logLikelihood,
        output
    },
        If[ Length[inputData] =!= Length[outputData],
            Return["Input and output data are not of same length"]
        ];
        
        {kernel, nugget, mean} = Function[
            Function[
                Evaluate[vars],
                #
            ]
        ] /@ {kernelFunction, nuggetFunction, meanFunction};
        
        With[{
            covarianceFunction = compiledCovarianceMatrix[
                inputData,
                kernelFunction,
                nuggetFunction,
                vars,
                Sequence @@ passOptionsDown[gaussianProcessNestedSampling, compiledCovarianceMatrix, {opts}]
            ],
            kernel = kernel,
            nugget = nugget,
            mean = mean
        },
            logLikelihood = Switch[OptionValue["Likelihood"],
                Automatic,
                    With[{
                        f = If[ nullKernelQ,
                                SparseArray @* DiagonalMatrix,
                                Identity
                            ]
                    },
                        Function[
                            LogLikelihood[
                                MultinormalDistribution[
                                    f[covarianceFunction[##]]
                                ],
                                {outputData - (mean[##]) /@ inputData}
                            ]
                        ]
                    ]
                    ,
                _Function,
                    OptionValue["Likelihood"],
                _,
                    Function[
                        gaussianProcessLogLikelihood[
                            outputData - (mean[##]) /@ inputData,
                            matrixInverseAndDet[covarianceFunction[##]]
                        ]
                    ]
            ];
            invCovFun = Function[matrixInverseAndDet[covarianceFunction[##]]];
            If[ TrueQ[IntegerQ[parallelRuns] && parallelRuns > 0],
                output = parallelNestedSampling[
                    logLikelihood,
                    variablePrior,
                    variables,
                    Sequence @@ passOptionsDown[gaussianProcessNestedSampling, parallelNestedSampling, {opts}]
                ]
                ,
                output = nestedSampling[
                    logLikelihood,
                    variablePrior,
                    variables,
                    Sequence @@ passOptionsDown[gaussianProcessNestedSampling, nestedSampling, {opts}]
                ]
            ];
            
            kAndKappa[args___] := With[{
                ker = kernel[args],
                nug = nugget[args]
            },
                compiledKandKappa[
                    inputData,
                    ker,
                    nug,
                    Sequence @@ passOptionsDown[gaussianProcessNestedSampling, compiledKandKappa, {opts}]
                ]
            ];
            
            output = Join[
                MapAt[
                    Function[{row},
                        Module[{
                            Cmat = covarianceFunction @@ row["Point"],
                            mf = mean @@ row["Point"],
                            inv
                        },
                            inv = matrixInverseAndDet[Cmat]["Inverse"];
                            Join[
                                row,
                                <|
                                    "PredictionParameters" ->
                                        Join[
                                            <|
                                                "CovarianceMatrix" -> SparseArray[Cmat],
                                                "InverseCovarianceMatrix" -> inv,
                                                "CInvY" -> inv[
                                                    Subtract[
                                                        outputData,
                                                        mf /@ inputData
                                                    ]
                                                ],
                                                "KandKappaFunction" -> kAndKappa @@ row["Point"],
                                                "MeanFunction" -> mf
                                            |>
                                        ]
                                |>
                            ]
                        ]
                    ],
                    output,
                    {"Samples", All}
                ],
                <|
                    "GaussianProcessData" ->
                        <|
                            "ModelFunctions" -> <|
                                "Kernel" -> kernelFunction,
                                "Nugget" -> nuggetFunction,
                                "MeanFunction" -> meanFunction,
                                "CovarianceFunction" -> covarianceFunction,
                                "InverseCovarianceFunction" -> invCovFun
                            |>,
                            <|
                                "OriginalData" -> <|
                                    "Input" -> inputData,
                                    "Output" -> outputData
                                |>
                            |>
                        |>
                |>
            ];
            Share[output];
            output
        ]
    ]
];
Options[gaussianProcessNestedSampling] = Join[
    {
        "Likelihood" -> Automatic
    },
    Options[parallelNestedSampling],
    Options[Compile]
];
SetOptions[gaussianProcessNestedSampling, "ParallelRuns" -> None];

predictFromGaussianProcess[
    result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"]&),
    predictionPoints_Integer /; predictionPoints > 1,
    posteriorFraction : _?(NumericQ[#] && Between[#, {0, 1}]&): 1,
    opts : OptionsPattern[]
] := predictFromGaussianProcess[
    result,
    If[ Length[Dimensions[result[["GaussianProcessData", "OriginalData", "Input"]]]] === 1,
        Subdivide[
            Sequence @@ MinMax @ result[["GaussianProcessData", "OriginalData", "Input"]],
            predictionPoints - 1
        ],
        Tuples[
            Subdivide[Sequence @@ #, predictionPoints - 1] & /@ MinMax /@ 
                Transpose[
                    result[["GaussianProcessData", "OriginalData", "Input"]]
                ]
        ]
    ],
    posteriorFraction,
    opts
]

predictFromGaussianProcess[
    result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"]&),
    predictionPoints_List,
    posteriorFraction : _?(NumericQ[#] && Between[#, {0, 1}]&) : 1,
    opts : OptionsPattern[]
] /; Between[posteriorFraction, {0, 1}]:= Module[{
    truncatedResult = takePosteriorFraction[result, posteriorFraction],
    weights
},
    weights = Values @ truncatedResult[["Samples", All, "CrudePosteriorWeight"]];
    AssociationThread[
        predictionPoints,
        Map[
            MixtureDistribution[weights, #]&,
            Transpose[
                Values @ Map[
                    With[{
                        kandKappa = #KandKappaFunction[predictionPoints]
                    },
                        Function[params, NormalDistribution @@ params] /@ Transpose[{
                            Flatten[Transpose[kandKappa["k"]] . #CInvY] + #MeanFunction /@ predictionPoints,
                            kandKappa["kappa"] - Total[kandKappa["k"] * #InverseCovarianceMatrix[kandKappa["k"]]]
                        }]
                    ]&,
                    truncatedResult[["Samples", All, "PredictionParameters"]]
                ]
            ]
        ]
    ]
];

Options[predictFromGaussianProcess] = {};

End[] (* End Private Context *)

EndPackage[]