(* Wolfram Language Package *)

BeginPackage["BayesianNeuralNetworks`"]
(* Exported symbols added here with SymbolName::usage *)

gaussianLossLayer;
regressionNet;
regressionLossNet;
logSumExpLayer;
alphaDivergenceLoss;
extractRegressionNet;
sampleTrainedNet;
netRegularizationLoss;
networkLogEvidence;
batchnormToChain;
crossValidateModel;

Begin["`Private`"] (* Begin Private Context *)

ClearAll["BayesianNeuralNetworks`*"];
ClearAll["BayesianNeuralNetworks`Private`*"];

(* Computes gaussian negative loglikelihood up to constants *)
gaussianLossLayer[] := gaussianLossLayer["LogPrecision"];

gaussianLossLayer["LogPrecision"] = With[{
    lossFunction = Function[
        {yObserved, yPredicted, logPrecision},
        (yPredicted - yObserved)^2 * Exp[logPrecision] - logPrecision
    ]
},
    ThreadingLayer[lossFunction]
];

gaussianLossLayer["Variance"] = With[{
    lossFunction = Function[
        {yObserved, yPredicted, variance},
        (yPredicted - yObserved)^2 / variance + Log[variance]
    ]
},
    ThreadingLayer[lossFunction]
];

gaussianLossLayer["StandardDeviation"] = With[{
    lossFunction = Function[
        {yObserved, yPredicted, stdev},
        ((yPredicted - yObserved) / stdev)^2 + 2 * Log[stdev]
    ]
},
    ThreadingLayer[lossFunction]
];

Options[regressionNet] = {
    "NetworkDepth" -> 4,
    "LayerSize" -> 100,
    "ActivationFunction" -> "SELU",
    "DropoutProbability" -> 0.25,
    "BatchNormalization" -> False
};

regressionNet[{input_, output_}, opts : OptionsPattern[]] := With[{
    pdrop = OptionValue["DropoutProbability"],
    size = OptionValue["LayerSize"],
    activation = OptionValue["ActivationFunction"],
    depth = OptionValue["NetworkDepth"],
    batchNormQ = TrueQ @ OptionValue["BatchNormalization"]
},
    NetChain[
        Flatten @ {
            Table[
                {
                    LinearLayer[
                        If[Head[size] === Function, size[i], size]
                    ],
                    If[ TrueQ[batchNormQ], BatchNormalizationLayer[], Nothing],
                    ElementwiseLayer[
                        If[Head[activation] === Function, activation[i], activation]
                    ],
                    Switch[ pdrop,
                        _?NumericQ,
                            DropoutLayer[pdrop],
                        _Function,
                            DropoutLayer[pdrop[i]],
                        _,
                            Nothing
                    ]
                },
                {i, depth}
            ],
            LinearLayer[]
        },
        "Input" -> input,
        "Output" -> output
    ]
];

regressionNet[opts : OptionsPattern[]] := regressionNet["HeteroScedastic", opts];

regressionNet[
    "HomoScedastic",
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "reg1" -> regressionNet[{Automatic, {1}}, opts],
        "const" -> ConstantArrayLayer["Output" -> {1}],
        "cat" -> CatenateLayer[]
    |>,
    {
        NetPort["Input"] -> "reg1",
        {"reg1", "const"} -> "cat"
    }
];

regressionNet["HeteroScedastic", opts : OptionsPattern[]] := regressionNet[{Automatic, {2}}, opts];

Options[regressionLossNet] = Join[
    Options[regressionNet],
    {
        "Input" -> Automatic,
        "LossModel" -> Automatic
    }
];

regressionLossNet[opts : OptionsPattern[]] := regressionLossNet["HeteroScedastic", opts];

regressionLossNet[
    errorModel : "HeteroScedastic" | "HomoScedastic",
    opts : OptionsPattern[]
] := regressionLossNet[
    regressionNet[errorModel, FilterRules[{opts}, Options[regressionNet]]],
    opts
];

regressionLossNet[
    net : (_NetGraph | _NetChain),
    opts : OptionsPattern[]
] := Module[{
    lossModel = Replace[
        OptionValue["LossModel"],
        {
            "AlphaDivergence" -> <||>,
            {"AlphaDivergence", subOpts : (___Rule | {___Rule} | _?AssociationQ)} :> Association[subOpts]
        }
    ],
    alpha,
    k
},
    (
        alpha = Lookup[lossModel, "Alpha", 0.5];
        k = Lookup[lossModel, "SampleNumber", 10];
        NetGraph[
            <|
                "repInput" -> ReplicateLayer[k],
                "regression" -> NetMapOperator[net],
                "part1" -> PartLayer[{All, 1}],
                "part2" -> PartLayer[{All, 2}],
                "repY" -> ReplicateLayer[k],
                "loss" -> gaussianLossLayer[],
                "alphaDiv" -> alphaDivergenceLoss[alpha]
            |>,
            {
                NetPort["Input"] -> "repInput" -> "regression",
                "regression" -> "part1",
                "regression" -> "part2",
                NetPort["Target"] -> "repY",
                {"repY", "part1", "part2"} -> "loss" -> "alphaDiv" -> NetPort["Loss"]
            },
            "Input" -> OptionValue["Input"]
        ]
    ) /; AssociationQ[lossModel]
];

regressionLossNet[
    net : (_NetGraph | _NetChain),
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> net,
        "part1" -> PartLayer[1],
        "part2" -> PartLayer[2],
        "loss" -> gaussianLossLayer[]
    |>,
    {
        NetPort["Input"] -> "regression",
        "regression" -> "part1",
        "regression" -> "part2",
        {NetPort["Target"], "part1", "part2"} -> "loss" -> NetPort["Loss"]
    },
    "Input" -> OptionValue["Input"]
];

Options[logSumExpLayer] = {
    "Input" -> Automatic,
    "Output" -> Automatic,
    "Aggregator" -> Total,
    "LevelSorting" -> True
};
logSumExpLayer[level_Integer, opts : OptionsPattern[]] := logSumExpLayer[{level}, opts];
logSumExpLayer[levels : {__Integer} : {1}, opts : OptionsPattern[]] := logSumExpLayer[levels, opts] = With[{
    sortedLevels = If[ TrueQ[OptionValue["LevelSorting"]],
        SortBy[{Sign, Abs}], (* Sorts the positive and negative levels for the ReplicateLayer chain *)
       Identity
    ][levels],
    aggregator = OptionValue["Aggregator"]
},
    NetGraph[
        <|
            "max" -> AggregationLayer[Max, sortedLevels],
            "replicate" -> NetChain[Map[ReplicateLayer[Automatic, #] &, sortedLevels]],
            "subtract" -> ThreadingLayer[Subtract],
            "exp" -> ElementwiseLayer[Exp],
            "sum" -> AggregationLayer[aggregator, sortedLevels],
            "logplusmax" -> ThreadingLayer[Function[{avg, max}, Log[avg] + max]]
        |>,
        {
            NetPort["Input"] -> "max" -> "replicate",
            {NetPort["Input"], "replicate"} -> "subtract" -> "exp" -> "sum",
            {"sum", "max"} -> "logplusmax"
        },
        "Input" -> OptionValue["Input"],
        "Output" -> OptionValue["Output"]
    ]
];

logSumExpLayer[All, opts : OptionsPattern[]] := logSumExpLayer[All, opts] = NetChain[
    {
        FlattenLayer[],
        logSumExpLayer[
            {1},
            Sequence @@ FilterRules[
                {opts},
                Except["Input" | "Output"]
           ]
        ]
    },
    "Input" -> OptionValue["Input"],
    "Output" -> OptionValue["Output"] 
];

Options[alphaDivergenceLoss] = {
    "Input" -> Automatic
};
alphaDivergenceLoss[alpha_?NumericQ /; alpha == 0, OptionsPattern[]] := 
    AggregationLayer[Mean, All, "Input" -> OptionValue["Input"]];
alphaDivergenceLoss[DirectedInfinity[1], OptionsPattern[]] := 
    AggregationLayer[Min, All, "Input" -> OptionValue["Input"]];
alphaDivergenceLoss[DirectedInfinity[-1], OptionsPattern[]] :=
    AggregationLayer[Max, All, "Input" -> OptionValue["Input"]];

alphaDivergenceLoss[alpha_?NumericQ /; alpha != 0, OptionsPattern[]] := NetChain[
    <|
        "timesAlpha" -> ElementwiseLayer[Function[-alpha * #]],
        "logMeanExp" -> logSumExpLayer[All, "Aggregator" -> Mean],
        "invalpha" -> ElementwiseLayer[Function[-Divide[#, alpha]]]
    |>,
    "Input" -> OptionValue["Input"],
    "Output" -> "Real"
];
alphaDivergenceLoss[layer_] := layer;

extractRegressionNet[net_NetTrainResultsObject] := extractRegressionNet[net["TrainedNet"]];

extractRegressionNet[net : (_NetChain | _NetGraph)] := With[{
    layers = Keys @ NetInformation[net, "Layers"]
},
    batchnormToChain @ Which[
        MemberQ[layers, {"regression", ___}],
            Replace[
                NetExtract[net, "regression"],
                map_NetMapOperator :> NetExtract[map, "Net"]
            ],
        True,
            net
    ]
];

netWeights[net_] := NetInformation[
    Quiet[NetReplace[net, _BatchNormalizationLayer -> Nothing], {NetReplace::norep}],
    "Arrays"
];

pNormChain[p_?NumericQ] := (
    pNormChain[p] = NetChain[{ElementwiseLayer[Abs[#]^p &], AggregationLayer[Total, All]}]
);

Options[sampleTrainedNet] = {
    TargetDevice -> "CPU"
};

sampleTrainedNet[
    net : (_NetTrainResultsObject | _NetChain | _NetGraph),
    xvalues_List,
    nSamples : (_Integer?Positive) : 100,
    opts : OptionsPattern[]
] := 
    Module[{
        regnet = extractRegressionNet[net],
        samples,
        mean,
        stdv
    },
        samples = Partition[
            regnet[
                Catenate[ConstantArray[xvalues, nSamples]],
                NetEvaluationMode -> "Train",
                TargetDevice -> OptionValue[TargetDevice]
            ],
            Length[xvalues]
        ];
        mean = Mean[samples[[All, All, 1]]];
        stdv = Sqrt[Variance[samples[[All, All, 1]]] + Mean[Exp[-samples[[All, All, 2]]]]];
        AssociationThread[
            xvalues,
            Thread[NormalDistribution[mean, stdv]]
        ]
    ];

netRegularizationLoss[obj_NetTrainResultsObject, rest___] := netRegularizationLoss[obj["TrainedNet"], rest];

netRegularizationLoss[net : (_NetChain | _NetGraph), rest___] := netRegularizationLoss[netWeights[net], rest];

netRegularizationLoss[
    weights : _List | _?AssociationQ /; AllTrue[weights, Head[#] === NumericArray &],
    lambda : _ : 1,
    p : (_?NumericQ) : 2
] := If[ TrueQ[p == 0]
    ,
    lambda * Total @ Map[Apply[Times] @* Dimensions, weights]
    ,
    lambda * Total[pNormChain[p] /@ weights, Infinity]
];

netRegularizationLoss[
    weights_List,
    lambdaList_List,
    pList_List
] /; Length[lambdaList] === Length[pList] := Total[
    MapThread[
        netRegularizationLoss[weights, #1, #2]&,
        {lambdaList, pList}
    ]
];

Options[networkLogEvidence] = {"Alpha" -> Automatic, "SampleNumber" -> 100, TargetDevice -> "CPU"};

networkLogEvidence[net_, data : {__Rule}, rest___] := networkLogEvidence[
    net,
    <|"Input" -> data[[All, 1]], "Target" -> data[[All, 2]]|>,
    rest
];

networkLogEvidence[net_, data_Rule, rest___] := networkLogEvidence[
    net,
    <|"Input" -> data[[1]], "Target" -> data[[2]]|>,
    rest
];

networkLogEvidence[obj_NetTrainResultsObject, rest___] := networkLogEvidence[obj["TrainedNet"], rest];

networkLogEvidence[net : (_NetChain | _NetGraph), data_?AssociationQ, lambda2_, opts : OptionsPattern[]] := Module[{
    nSamples = OptionValue["SampleNumber"],
    alpha = Replace[
        OptionValue["Alpha"],
        Automatic :> FirstCase[
            Keys @ NetInformation[net, "Layers"],
            layer : {___, "alphaDiv", "timesAlpha"} :> NetExtract[net, Append[layer, "Function"]][-1],
            0
        ]
    ],
    negLogLike,
    regularizationLoss
},
    negLogLike = Mean @ regressionLossNet[
        extractRegressionNet[net], 
        "LossModel" -> {"AlphaDivergence",
            "SampleNumber" -> nSamples,
            "Alpha" -> alpha
        }
    ][data, NetEvaluationMode -> "Train", TargetDevice -> OptionValue[TargetDevice]];
    regularizationLoss = netRegularizationLoss[net, lambda2];
    -(negLogLike + regularizationLoss)
];

batchnormToChain::usage = "batchnormToChain[net] replaces all instances of BatchNormalizationLayer with a NetChain consisting of ConstantPlusLayer and ConstantTimesLayer.";
batchnormToChain[batch_BatchNormalizationLayer] := Block[{
    biases, scaling, movMean, movVar, eps, sigma
},
    {biases, scaling, movMean, movVar, eps} = Normal @ NetExtract[
        batch,
        List /@ {"Biases", "Scaling", "MovingMean", "MovingVariance", "Epsilon"}
    ];
    sigma = Sqrt[movVar + eps];
    NetChain[{ (* It's possible to use only 2 layers instead of 3, but it seems like the numerical error is smaller with 3 layers *)
        ConstantPlusLayer["Biases" -> -movMean],
        ConstantTimesLayer["Scaling" -> Divide[scaling, sigma]],
        ConstantPlusLayer["Biases" -> biases]
    }]
];
batchnormToChain[net : _NetGraph | _NetChain] := Quiet[
    NetReplace[
        net,
        b_BatchNormalizationLayer :> batchnormToChain[b]
    ],
    {NetReplace::norep}
];

crossValidateModel::unknownMethod = "Unknow method `1`";

Options[crossValidateModel] = Join[
    {
        Method -> "KFold",
        "ValidationFunction" -> Automatic,
        "ParallelQ" -> False
    }
];
crossValidateModel[data_, dist_?DistributionParameterQ, opts : OptionsPattern[]] := crossValidateModel[
    data,
    Function[EstimatedDistribution[#1, dist]],
    opts
];
crossValidateModel[data_,
    dists_?(Function[ListQ[#] || AssociationQ[#]]) /; AllTrue[dists, DistributionParameterQ],
    opts : OptionsPattern[]
] := crossValidateModel[
    data,
    If[ AssociationQ[dists], Map, AssociationMap][
        Function[dist, Function[EstimatedDistribution[#1, dist]]],
        dists
    ],
    opts
];

crossValidateModel[data : (_List | _Rule | _?AssociationQ), trainingFun : Except[_List], opts : OptionsPattern[]] := Module[{
    method,
    nDat = dataSize[data],
    rules,
    methodFun,
    validationFunction
},
    method = Replace[
        Flatten @ {OptionValue[Method]},
        {
            {"LeaveOneOut", rest___} :> {"KFold", "Folds" -> nDat, Sequence @@ FilterRules[{rest}, Except["Folds"]]},
            {"BootStrap", rest___} :> {"RandomSubSampling",
                "SamplingFunction" -> {"BootStrap", Lookup[{rest}, "BootStrapSize", nDat]},
                Sequence @@ FilterRules[{rest}, {"Runs", "ParallelQ"}]
            }
        }
    ];
    rules = Join[Rest[method], FilterRules[{opts}, {"ParallelQ"}]];
    methodFun = Replace[
        First[method],
        {
            "KFold" :> kFoldValidation,
            "RandomSubSampling" :> subSamplingValidation,
            other_ :> (
                Message[crossValidateModel::unknownMethod, other];
                Return[$Failed]
            )
        }
    ];
    validationFunction = Replace[
        OptionValue["ValidationFunction"],
        {
            assoc_?AssociationQ :> parseValidationOption /@ assoc,
            other_ :> parseValidationOption[other]
        }
    ];
    If[ AssociationQ[trainingFun],
        If[ !AssociationQ[validationFunction],
            validationFunction = Function[validationFunction] /@ trainingFun
            ,
            (* Make sure the keys are sorted in the same order so that MapThread will work without issue *)
            validationFunction = AssociationThread[
                Keys[trainingFun],
                Lookup[validationFunction, Keys[trainingFun], defaultValidationFunction[]]
            ]
        ]
    ];
    
    methodFun[
        data,
        quietReporting @ listOperator1[trainingFun],
        listOperator2[validationFunction],
        Sequence @@ FilterRules[rules, Options[methodFun]]
    ]
];

parseValidationOption = Replace[{
    {Automatic, args___} :> defaultValidationFunction[args],
    None :> Function[Missing[]],
    Automatic :> defaultValidationFunction[]
}];

listOperator1[funs_?AssociationQ][args___] := Map[#[args]&, funs];
listOperator1[f : Except[_?AssociationQ]][args___] := f[args];

listOperator2[funs_?AssociationQ][results_?AssociationQ, args___] := MapThread[#1[#2, args]&, {funs, results}];
listOperator2[f : Except[_?AssociationQ]][args___] := f[args];

dataSize[data_List] := Length[data];
dataSize[data_] := Length[First[data]];

quietReporting = ReplaceAll[
    {
        (method : Classify | Predict | NetTrain | LearnDistribution)[args___] :> method[args, TrainingProgressReporting -> None]
    }
];

slotFunctionPattern = HoldPattern[Function[_] | Function[Null, __]];

(* Turns a function with multiple slots into a function that accepts all arguments as a list in the first slot *)
multiArgToVectorArgFunction[function : slotFunctionPattern] := Replace[
    function,
    {
        Slot[i_Integer] :> Slot[1][[i]],
        insideFun : slotFunctionPattern :> insideFun (* Make sure only the outer function is affected *)
    },
    {1, DirectedInfinity[1]}
];
multiArgToVectorArgFunction[other_] := Function[other @@ #];

defaultValidationFunction[___][dist_?DistributionParameterQ, val_] := Divide[-LogLikelihood[dist, val], Length[val]];
defaultValidationFunction[___][dist_LearnedDistribution, val_] := - Mean[Log @ PDF[dist, val]];

defaultValidationFunction[
    aggregationFunction : _ : Automatic,
    dataPreProcessor : _ : Identity
][fit_FittedModel, val_] := With[{
    matrix = dataPreProcessor[val] (* this should return a matrix in the same format as accepted by, e.g., LinearModelFit *)
},
    Replace[aggregationFunction, Automatic :> Function[RootMeanSquare @ Subtract[#1, #2]]][
        Map[ (* Turn the function into a form that can be efficiently mapped over a matrix *)
            multiArgToVectorArgFunction[fit["Function"]],
            matrix[[All, 1 ;; -2 ;; 1]]
        ], (* fitted values *)
        matrix[[All, -1]] (* True values*)
    ] /; MatrixQ[matrix] && Dimensions[matrix][[2]] > 1
];

defaultValidationFunction[args___][pred_PredictorFunction, val_] := PredictorMeasurements[pred, val, args];
defaultValidationFunction[args___][class_ClassifierFunction, val_] := ClassifierMeasurements[class, val, args];

defaultValidationFunction[args__][net : (_NetGraph | _NetChain | _NetTrainResultsObject), val_] := NetMeasurements[
    Replace[net, obj_NetTrainResultsObject :> obj["TrainedNet"]],
    val,
    args
];
defaultValidationFunction[][net : (_NetGraph | _NetChain | _NetTrainResultsObject), val_] := With[{
    args = If[ Head[net] === NetTrainResultsObject,
        Cases[Flatten @ Drop[List @@ net["NetTrainInputForm"], 2], _Rule],
        {}
    ]
},
    NetTrain[
        Replace[net, obj_NetTrainResultsObject :> obj["TrainedNet"]],
        Replace[val,
            {
                l_List :> l[[{1}]],
                other_ :> other[[All, {1}]]
            }
        ],
        "ValidationLoss",
        ValidationSet -> val,
        Method -> {"SGD", "LearningRate" -> 0},
        MaxTrainingRounds -> 1,
        Sequence @@ args,
        TrainingProgressReporting -> None
    ]
];

defaultValidationFunction[___][_, val_] := val;

extractIndices[data_List, indices_List] := Developer`ToPackedArray @ data[[indices]];
extractIndices[data : _Rule | _?AssociationQ, indices_List] := Developer`ToPackedArray /@ data[[All, indices]];

kFoldIndices[n_Integer, k_Integer] := Replace[
    Flatten[ (* This essentially transposes a ragged array *)
        Partition[
            RandomSample[Range[n]], 
            k, k, {1, 1}, Nothing
        ],
        {{2}, {1}}
    ],
    array : Except[_?Developer`PackedArrayQ] :> Developer`ToPackedArray /@ array
];

parseParallelOptions[True] := parseParallelOptions[{True}];
parseParallelOptions[{True, args___Rule}] := Function[Null, 
    ParallelTable[##, args,
        DistributedContexts -> Automatic,
        Method -> "CoarsestGrained"
    ],
    HoldAll
];
parseParallelOptions[___] := Table;

Options[kFoldValidation] = {
    "Runs" -> 1,
    "Folds" -> 5,
    "ParallelQ" -> False
};
kFoldValidation[data_, estimator_, tester_, opts : OptionsPattern[]] := Module[{
    nRuns = OptionValue["Runs"],
    nData = dataSize[data],
    nFolds,
    partitions
},
    nFolds = Clip[Round @ OptionValue["Folds"], {1, nData}];
    partitions = Table[kFoldIndices[nData, nFolds], nRuns];
    Flatten @ parseParallelOptions[OptionValue["ParallelQ"]][
        With[{
            estimate = estimator[extractIndices[data, Join @@ Delete[partition, fold]]]
        },
            <|
                "FittedModel" -> estimate,
                "ValidationResult" -> tester[estimate, extractIndices[data, partition[[fold]]]]
            |>
        ],
        {fold, nFolds},
        {partition, partitions}
    ]
];

subSamplingIndices[n_Integer, k_Integer] := AssociationThread[
    {"TrainingSet", "ValidationSet"},
    TakeDrop[RandomSample[Range[n]], Subtract[n, k]]
];

Options[subSamplingValidation] = {
    "Runs" -> 5,
    ValidationSet -> Scaled[1/5],
    "ParallelQ" -> False,
    "SamplingFunction" -> Automatic
};
subSamplingValidation[data_, estimator_, tester_, opts : OptionsPattern[]] := Module[{
    nRuns = OptionValue["Runs"],
    nVal,
    nData = dataSize[data],
    samplingFunction
},
    nVal = Clip[
        Round @ Replace[
            OptionValue[ValidationSet],
            Scaled[f_] :> Floor[f * nData]
        ],
        {1, nData - 1}
    ];
    samplingFunction = Replace[
        OptionValue["SamplingFunction"],
        {
            Automatic :> Function[subSamplingIndices[nData, nVal]],
            "BootStrap" :> Function[RandomChoice[Range[nData], nData]],
            {"BootStrap", n_Integer} :> Function[RandomChoice[Range[nData], n]],
            {"BootStrap", Scaled[f_]} :> With[{n = Max[1, Floor[f * nData]]},
                Function[RandomChoice[Range[nData], n]]
            ],
            other_ :> Function[other[nData, nVal]]
        }
    ];
    parseParallelOptions[OptionValue["ParallelQ"]][
        With[{
            partitionedData = Replace[
                samplingFunction[],
                {
                    assoc_?AssociationQ :> (extractIndices[data, #]& /@ assoc),
                    other_ :> <|"TrainingSet" -> extractIndices[data, other]|>
                }
            ]
        },
            With[{
                estimate = estimator[partitionedData["TrainingSet"]]
            },
                <|
                    "FittedModel" -> estimate,
                    If[ !MissingQ[partitionedData["ValidationSet"]],
                        "ValidationResult" -> tester[estimate, partitionedData["ValidationSet"]],
                        <||>
                    ]
                |>
            ]
        ],
        {run, nRuns}
    ]
];

End[] (* End Private Context *)

EndPackage[]