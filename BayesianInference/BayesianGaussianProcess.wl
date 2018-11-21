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

paramSpecPattern = BayesianStatistics`Private`paramSpecPattern;

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

compiledCovarianceMatrix[points_List, kernel_, nugget_, vars : {__Symbol}] := With[{
    matrix = Function[
        paramSymbol,
        Evaluate @ Normal @ covarianceMatrix[
            points,
            varsToParamVector[kernel, vars -> paramSymbol],
            varsToParamVector[nugget, vars -> paramSymbol]
        ]
    ]
},
    Compile[{
        {pt, _Real, 1}
    },
        matrix[pt],
        RuntimeAttributes -> {Listable}
    ]
];

compiledKandKappa[
    points1_List,
    kernel : nullKernelPattern,
    nugget_
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
            RuntimeAttributes -> {Listable}
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
    nugget_
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
            RuntimeAttributes -> {Listable}
        ],
        cf2 = Compile[{
            {points2, _Real, rank2}
        },
            kernel[points2, points2] + nugget[points2],
            RuntimeAttributes -> {Listable}
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

logTotal = Function[ (* Take Abs because the covariance matrix has positive determinant *)
    Total @ Log @ Abs[#]
];

matrixInverseAndDet[matrix_List?numericMatrixQ] := With[{
    ls = LinearSolve[matrix]
},
    <|
        "Inverse" -> ls,
        "LogDet" -> logTotal[Diagonal @ ls[[2, 3, 1]]]
    |>
];

matrixInverseAndDet[matrix : ((_SparseArray | _StructuredArray)?numericMatrixQ)] := With[{
    ls = LinearSolve[matrix]
},
    <|
        "Inverse" -> ls,
        "LogDet" -> logTotal[Join[Diagonal @ ls["getL"], Diagonal @ ls["getU"]]]
    |>
];

matrixInverseAndDet[matrixDiagonal_List?numericVectorQ] := <|
    "Inverse" -> Function[Divide[#, matrixDiagonal]],
    "LogDet" -> logTotal[matrixDiagonal]
|>;

gaussianProcessLogLikelihood[data : {__Rule}, rest___] :=
    gaussianProcessLogLikelihood[data[[All, 1]] -> data[[All, 2]], rest];

gaussianProcessLogLikelihood[
    Rule[dataIn_List, dataOut_List] /; Length[dataIn] === Length[dataOut],
    kernel_, (* Kernel has to give numerical results after evaluation *)
    nugget_,
    meanFunction : _ : Function[0]
] := gaussianProcessLogLikelihood[][
    dataOut - meanFunction /@ dataIn,
    matrixInverseAndDet @ covarianceMatrix[
        dataIn,
        kernel,
        nugget
    ]
];

With[{
    logTwoPi = N[Log[2 * Pi]],
    limits = {- Abs[$MachineLogZero], Abs[$MachineLogZero]}
},
    gaussianProcessLogLikelihood[] := Function[
        (*
            #1 : mean adjusted output vector,
            #2 : output from matrixInverseAndDet 
        *)
        Clip[
            - 0.5 * Plus[
                Length[#1] * logTwoPi,
                #2["LogDet"],
                #1 . #2["Inverse"][#1]
            ],
            limits
        ]
    ]
];

gaussianProcessNestedSampling[data_, kernel_, nugget_, meanFunction_, variables : paramSpecPattern, opts : OptionsPattern[]] :=
    gaussianProcessNestedSampling[data, kernel, meanFunction, {variables}, opts];

gaussianProcessNestedSampling[data : {__Rule}, rest___] :=
    gaussianProcessNestedSampling[data[[All, 1]], data[[All, 2]], rest];

gaussianProcessNestedSampling[Rule[dataIn_List, dataOut_List] /; Length[dataIn] === Length[dataOut], rest___] :=
    gaussianProcessNestedSampling[dataIn, dataOut, rest];

gaussianProcessNestedSampling[data_?(AssociationQ[#] && KeyExistsQ[#, "Input"] && KeyExistsQ[#, "Output"]&), rest___] :=
    Module[{
        tempResult = gaussianProcessNestedSampling[data["Input", "NormalizedData"], data["Output", "NormalizedData"], rest]
    },
        If[ inferenceObjectQ[tempResult] && AssociationQ[tempResult["GaussianProcessData"]],
            AppendTo[
                tempResult["GaussianProcessData"],
                "DataPreProcessors" -> data[[All, {"Function", "InverseFunction"}]]
            ]
        ];
        tempResult
    ];

gaussianProcessNestedSampling[
    dataIn_List?(numericMatrixQ[#] || numericVectorQ[#]&),
    dataOut_List?(numericMatrixQ[#] || numericVectorQ[#]&),
    kerf_, nugf_, meanf_,
    variables : {paramSpecPattern..},
    variablePrior_,
    opts : OptionsPattern[]
] := Catch[
    With[{
        vars = variables[[All, 1]],
        inputData = Developer`ToPackedArray[dataNormalForm @ dataIn],
        outputData = Developer`ToPackedArray[Flatten @ dataNormalForm @ dataOut],
        parallelRuns = OptionValue["ParallelRuns"]
    },
        Module[{
            nullKernelQ,
            kernelFunction,
            nuggetFunction,
            meanFunction,
            kernel,
            nugget,
            mean,
            kAndKappa,
            invCovFun,
            logLikelihood,
            output,
            infObject
        },
            If[ Length[inputData] =!= Length[outputData],
                Return["Input and output data are not of same length"]
            ];
            
            {kernelFunction, nuggetFunction, meanFunction} = Replace[{kerf, nugf, meanf}, None -> (0&), {1}];
            nullKernelQ = MatchQ[kernelFunction, nullKernelPattern];
            {kernel, nugget, mean} = Function[
                expressionToFunction[
                    #,
                    vars -> paramVector
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
                                        f[covarianceFunction[#]]
                                    ],
                                    {outputData - mean[#] /@ inputData}
                                ]
                            ]
                        ]
                        ,
                    _Function,
                        OptionValue["Likelihood"],
                    _,
                        With[{fun = gaussianProcessLogLikelihood[]},
                            Function[
                                fun[
                                    outputData - (mean[#]) /@ inputData,
                                    matrixInverseAndDet[covarianceFunction[#]]
                                ]
                            ]
                        ]
                ];
                invCovFun = Function[matrixInverseAndDet[covarianceFunction[#]]];
                
                infObject = defineInferenceProblem[
                    "Data" -> dataNormalForm[dataIn -> dataOut],
                    "LogLikelihoodFunction" -> logLikelihood,
                    "PriorDistribution" -> variablePrior,
                    "Parameters" -> variables
                ];
                If[FailureQ[infObject], Return[infObject]];
                
                If[ TrueQ[IntegerQ[parallelRuns] && parallelRuns > 0],
                    output = Normal @ parallelNestedSampling[
                        infObject,
                        Sequence @@ passOptionsDown[gaussianProcessNestedSampling, parallelNestedSampling, {opts}]
                    ]
                    ,
                    output = Normal @ nestedSampling[
                        infObject,
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
                        nug
                    ]
                ];
                
                output = inferenceObject @ Join[
                    MapAt[
                        Function[{row},
                            Module[{
                                Cmat = covarianceFunction @ row["Point"],
                                mf = mean @ row["Point"],
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
                                                    "KandKappaFunction" -> kAndKappa @ row["Point"],
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
                                    "Kernel" -> kernel,
                                    "Nugget" -> nugget,
                                    "MeanFunction" -> mean,
                                    "CovarianceFunction" -> covarianceFunction,
                                    "InverseCovarianceFunction" -> invCovFun
                                |>
                            |>
                    |>
                ];
                Share[output];
                output
            ]
        ]
    ],
    "problemDef"
];
Options[gaussianProcessNestedSampling] = Join[
    {
        "Likelihood" -> Automatic
    },
    Options[parallelNestedSampling]
];
SetOptions[gaussianProcessNestedSampling, "ParallelRuns" -> None];

predictFromGaussianProcess[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"] && KeyExistsQ[#, "Data"]&)],
    predictionPoints_Integer /; predictionPoints > 1,
    opts : OptionsPattern[]
] := predictFromGaussianProcess[
    inferenceObject[result],
    CoordinateBoundsArray[
        CoordinateBounds[result["Data"][[1]]],
        Into[predictionPoints - 1]
    ],
    opts
]

predictFromGaussianProcess[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"]&)],
    pts_List,
    opts : OptionsPattern[]
] := Module[{
    weights,
    predictionPoints = dataNormalForm[pts]
},
    (
        weights = Values @ result[["Samples", All, "CrudePosteriorWeight"]];
        AssociationThread[
            predictionPoints,
            Map[
                MixtureDistribution[weights, #]&,
                Transpose[
                    Values @ Map[
                        With[{
                            kandKappa = #KandKappaFunction[predictionPoints]
                        },
                            MapThread[
                                Function[{mu, stdev}, NormalDistribution[mu, stdev]],
                                {
                                    #CInvY . kandKappa["k"] + #MeanFunction /@ predictionPoints,
                                    Sqrt @ Subtract[
                                        kandKappa["kappa"],
                                        Total[kandKappa["k"] * #InverseCovarianceMatrix[kandKappa["k"]]]
                                    ]
                                }
                            ]
                        ]&,
                        result[["Samples", All, "PredictionParameters"]]
                    ]
                ]
            ]
        ]
    ) /; numericMatrixQ[predictionPoints]
];

predictFromGaussianProcess[ex_, in_, kf_, nf_, mf_] := Catch[
    Module[{
        examples = dataNormalForm[ex],
        inputs = DeleteDuplicates @ dataNormalForm[in],
        kernelFunction,
        nuggetFunction,
        meanFunction,
        invCov,
        CInvY,
        kandKappa
    },
        {kernelFunction, nuggetFunction, meanFunction} = Replace[{kf, nf, mf}, None -> (0&), {1}];
        examples[[2]] -= meanFunction /@ examples[[1]];
        invCov = matrixInverseAndDet[covarianceMatrix[examples[[1]], kernelFunction, nuggetFunction]]["Inverse"];
        kandKappa = compiledKandKappa[examples[[1]], kernelFunction, nuggetFunction][inputs];
        CInvY = invCov[Flatten @ examples[[2]]];
        AssociationThread[
            inputs,
            MapThread[
                NormalDistribution,
                {
                    Plus[
                        meanFunction /@ inputs,
                        CInvY . kandKappa["k"]
                    ],
                    Sqrt @ Subtract[
                        kandKappa["kappa"],
                        Total[kandKappa["k"] * invCov[kandKappa["k"]]]
                    ]
                }
            ]
        ] 
    ],
    "problemDef"
];

Options[predictFromGaussianProcess] = {};

End[] (* End Private Context *)

EndPackage[]