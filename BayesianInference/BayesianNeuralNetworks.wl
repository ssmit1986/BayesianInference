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
logSumExpLayer[levels : (_Integer | {__Integer}) : 1, opts : OptionsPattern[]] := With[{
    sortedLevels = If[ TrueQ[OptionValue["LevelSorting"]],
        SortBy[{Sign, Abs}], (* Sorts the positive and negative levels for the ReplicateLayer chain *)
       Identity
    ][Flatten@{levels}],
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

logSumExpLayer[All, opts : OptionsPattern[]] := NetChain[
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

End[] (* End Private Context *)

EndPackage[]