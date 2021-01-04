(* Wolfram Language Package *)

BeginPackage["BayesianGaussianProcess`", { "BayesianUtilities`", "BayesianStatistics`"}]
(* Exported symbols added here with SymbolName::usage *)  

defineGaussianProcess::usage = "defineGaussianProcess[data, kernel, nugget, meanFunction, variables, rules...] defines an inference object for a GP";
predictFromGaussianProcess::usage = "predictFromGaussianProcess[obj, pts] predicts the posterior values of the GP at pts";

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

covarianceMatrix[points_List, kernel : nullKernelPattern, nugget_] := nugget /@ points;

covarianceMatrix[points_List, kernel : Except[nullKernelPattern], nugget_] := Quiet[
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
    ],
    {General::munfl}
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
    ls = quietCheck[
        LinearSolve[matrix],
        Throw[$MachineLogZero, "MatInv"], (* If matrix is (nearly) singular, the log-likelihood will be -infinite *)
        {LinearSolve::luc, LinearSolve::sing1}
    ]
},
    <|
        "Inverse" -> ls,
        "LogDet" -> logTotal[Diagonal @ ls[[2, 3, 1]]]
    |>
];

matrixInverseAndDet[matrix : ((_SparseArray | _StructuredArray)?numericMatrixQ)] := With[{
    ls = quietCheck[
        LinearSolve[matrix],
        Throw[$MachineLogZero, "MatInv"],
        {LinearSolve::luc, LinearSolve::sing1}
    ]
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
] := Catch[
    gaussianProcessLogLikelihood[][
        Subtract[dataOut, meanFunction /@ dataIn],
        matrixInverseAndDet @ covarianceMatrix[
            dataIn,
            kernel,
            nugget
        ]
    ],
    "MatInv"
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

defineGaussianProcess[data_, kernel_, nugget_, meanFunction_, variables : paramSpecPattern] :=
    defineGaussianProcess[data, kernel, meanFunction, {variables}];

defineGaussianProcess[$Failed, ___] := (
    Message[defineInferenceProblem::dataFormat];
    inferenceObject[$Failed]
);

defineGaussianProcess::outputDim = "Output data has has dimensions `1`. Only 1D output data is supported for GP regression at this time.";

defineGaussianProcess[data : Except[_?(dataNormalFormQ[#] || normalizedDataQ[#] || FailureQ[#]&)], rest___] :=
    defineGaussianProcess[dataNormalForm[data], rest];

defineGaussianProcess[data_?normalizedDataQ, rest___] := defineGaussianProcess[
    data["Input", "NormalizedData"] -> data["Output", "NormalizedData"],
    rest,
    "DataPreProcessors" -> data[[All, {"Function", "InverseFunction"}]]
];

defineGaussianProcess[
    dataIn_List?numericMatrixQ -> dataOut_List?numericMatrixQ,
    ___
] /; Dimensions[dataOut][[2]] =!= 1 := (
    Message[defineGaussianProcess::outputDim, Dimensions[dataOut][[2]]];
    inferenceObject[$Failed]
);

defineGaussianProcess[
    dataIn_List?numericMatrixQ -> dataOut_List?numericMatrixQ,
    kerf_, nugf_, meanf_,
    variables : {paramSpecPattern..},
    variablePrior_,
    rest___Rule
] /; Dimensions[dataOut][[2]] === 1 := Catch[
    With[{
        vars = variables[[All, 1]],
        inputData = Developer`ToPackedArray[dataIn],
        outputData = Developer`ToPackedArray[Flatten @ dataOut]
    },
        Module[{
            nullKernelQ,
            kernelFunction,
            nuggetFunction,
            meanFunction,
            kernel,
            nugget,
            mean,
            invCovFun,
            logLikelihood = Lookup[{rest}, "LogLikelihoodFunction"]
        },
            If[ Length[inputData] =!= Length[outputData],
                Throw["Input and output data are not of same length", "problemDef"]
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
                    vars
                ]
            },
                logLikelihood = Switch[logLikelihood,
                    Automatic,
                        With[{
                            f = If[ nullKernelQ,
                                    SparseArray @* DiagonalMatrix,
                                    Identity
                                ]
                        },
                            Function[
                                Quiet @ Replace[
                                    LogLikelihood[
                                        MultinormalDistribution[
                                            mean[#] /@ inputData,
                                            f[covarianceFunction[#]]
                                        ],
                                        {outputData}
                                    ],
                                    _LogLikelihood -> $MachineLogZero
                                ]
                            ]
                        ],
                    _Function | _CompiledFunction,
                        logLikelihood,
                    _,
                        With[{fun = gaussianProcessLogLikelihood[]},
                            Function[
                                Catch[
                                    fun[
                                        Subtract[outputData, mean[#] /@ inputData],
                                        matrixInverseAndDet[covarianceFunction[#]]
                                    ],
                                    "MatInv"
                                ]
                            ]
                        ]
                ];
                invCovFun = Function[matrixInverseAndDet[covarianceFunction[#]]];
                
                defineInferenceProblem[
                    "Data" -> dataNormalForm[dataIn -> dataOut],
                    "PriorDistribution" -> variablePrior,
                    "Parameters" -> variables,
                    "GaussianProcessData" -> <|
                        "ModelFunctions" -> <|
                            "KernelFunction" -> kernel,
                            "NuggetFunction" -> nugget,
                            "MeanFunction" -> mean,
                            "CovarianceFunction" -> covarianceFunction,
                            "InverseCovarianceFunction" -> invCovFun
                        |>
                    |>,
                    rest,
                    "LogLikelihoodFunction" -> logLikelihood
                ]
            ]
        ]
    ],
    "problemDef"
];

predictFromGaussianProcess[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"] && KeyExistsQ[#, "Data"]&)],
    predictionPoints_Integer /; predictionPoints > 1
] := predictFromGaussianProcess[
    inferenceObject[result],
    CoordinateBoundsArray[
        CoordinateBounds[result["Data"][[1]]],
        Into[predictionPoints - 1]
    ]
];

predictFromGaussianProcess[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "GaussianProcessData"] && KeyExistsQ[#, "Samples"]&)],
    pts_List
] := Module[{
    weights,
    predictionPoints = dataNormalForm[pts]
},
    (
        weights = Values @ result[["Samples", All, "CrudePosteriorWeight"]];
        Map[
            MixtureDistribution[weights, #]&,
            GeneralUtilities`AssociationTranspose[
                Map[
                    With[{
                        examples = result["Data"],
                        kernelFunction = result["GaussianProcessData", "ModelFunctions", "KernelFunction"],
                        nuggetFunction = result["GaussianProcessData", "ModelFunctions", "NuggetFunction"],
                        meanFunction = result["GaussianProcessData", "ModelFunctions", "MeanFunction"],
                        fun = predictFromGaussianProcessInternal
                    },
                        fun[
                            examples,
                            predictionPoints,
                            kernelFunction[#],
                            nuggetFunction[#],
                            meanFunction[#]
                        ]&
                    ],
                    Values[result[["Samples", All, "Point"]]]
                ]
            ]
        ]
    ) /; numericMatrixQ[predictionPoints]
];

predictFromGaussianProcess[ex : (_Rule | {__Rule}), in_List, kf_, nf_, mf_] := Module[{
    examples = dataNormalForm[ex],
    inputs = DeleteDuplicates @ dataNormalForm[in],
    kernelFunction,
    nuggetFunction,
    meanFunction
},
    If[ Or[
            AnyTrue[{examples, inputs}, FailureQ],
            !numericMatrixQ[inputs],
            !MatchQ[Dimensions[examples[[2]]], {_, 1}]
        ],
        Return[$Failed, Module]
    ];
    {kernelFunction, nuggetFunction, meanFunction} = Replace[{kf, nf, mf}, None -> (0&), {1}];
    predictFromGaussianProcessInternal[examples, inputs, kernelFunction, nuggetFunction, meanFunction]
];

predictFromGaussianProcessInternal = Function[
    {examples, inputs, kernelFunction, nuggetFunction, meanFunction},
    With[{
        invCov = matrixInverseAndDet[covarianceMatrix[examples[[1]], kernelFunction, nuggetFunction]]["Inverse"],
        kandKappa = compiledKandKappa[examples[[1]], kernelFunction, nuggetFunction][inputs]
    },
        AssociationThread[
            inputs,
            MapThread[
                NormalDistribution,
                {
                    Plus[
                        meanFunction /@ inputs,
                        Dot[
                            invCov @ Subtract[Flatten @ examples[[2]], meanFunction /@ examples[[1]]],
                            kandKappa["k"]
                        ]
                    ],
                    Sqrt @ Subtract[
                        kandKappa["kappa"],
                        Total[kandKappa["k"] * invCov[kandKappa["k"]]]
                    ]
                }
            ]
        ]
    ]
];

End[] (* End Private Context *)

EndPackage[]