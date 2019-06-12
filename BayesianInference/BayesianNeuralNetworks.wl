(* Wolfram Language Package *)

BeginPackage["BayesianNeuralNetworks`"]
(* Exported symbols added here with SymbolName::usage *)

gaussianLossLayer;
regressionNet;
regressionLossNet;
alphaDivergenceLoss;
extractRegressionNet;
sampleTrainedNet;
netRegularizationLoss;

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
    "NetworkDepth" -> 3,
    "LayerSize" -> 100,
    "ActivationFunction" -> Ramp,
    "DropoutProbability" -> 0.25
};

regressionNet[{input_, output_}, opts : OptionsPattern[]] := With[{
    pdrop = OptionValue["DropoutProbability"],
    size = OptionValue["LayerSize"],
    activation = OptionValue["ActivationFunction"],
    depth = OptionValue["NetworkDepth"]
},
    NetChain[
        Flatten @ {
            Table[
                {
                    LinearLayer[
                        If[Head[size] === Function, size[i], size]
                    ],
                    BatchNormalizationLayer[], 
                    ElementwiseLayer[
                        If[Head[activation] === Function, activation[i], activation]
                    ],
                    If[ i === depth,
                        Nothing,
                        Switch[ pdrop,
                            _?NumericQ,
                                DropoutLayer[pdrop],
                            _Function,
                                DropoutLayer[pdrop[i]],
                            _,
                                Nothing
                        ]
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

regressionNet[opts : OptionsPattern[]] := regressionNet["HeteroScedastic", Automatic, opts];

regressionNet[
    "HomoScedastic",
    trainingModel : Automatic : Automatic,
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

regressionNet[
    "HeteroScedastic",
    trainingModel : Automatic : Automatic,
    opts : OptionsPattern[]
] := regressionNet[{Automatic, {2}}, opts];

regressionNet[
    errorModel_,
    trainingModel : {"AlphaDivergence", {_, k_Integer} | k_Integer},
    opts : OptionsPattern[]
] := NetChain[
    <|
        "repInput" -> ReplicateLayer[k],
        "map" -> NetMapOperator[regressionNet[errorModel, Automatic, opts]]
    |>
];

Options[regressionLossNet] = Join[
    Options[regressionNet],
    {"Input" -> Automatic}
];

regressionLossNet[opts : OptionsPattern[]] := regressionLossNet["HeteroScedastic", Automatic, opts];

regressionLossNet[
    errorModel_,
    trainingModel : Automatic : Automatic,
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> regressionNet[errorModel, trainingModel, FilterRules[{opts}, Options[regressionNet]]],
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

regressionLossNet[
    errorModel_,
    trainingModel : {"AlphaDivergence", {alpha_, k_Integer}},
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> regressionNet[errorModel, trainingModel, FilterRules[{opts}, Options[regressionNet]]],
        "part1" -> PartLayer[{All, 1}],
        "part2" -> PartLayer[{All, 2}],
        "repY" -> ReplicateLayer[k],
        "loss" -> gaussianLossLayer[],
        "alphaDiv" -> alphaDivergenceLoss[alpha, k]
    |>,
    {
        NetPort["Input"] -> "regression",
        "regression" -> "part1",
        "regression" -> "part2",
        NetPort["Target"] -> "repY",
        {"repY", "part1", "part2"} -> "loss" -> "alphaDiv" -> NetPort["Loss"]
    },
    "Input" -> OptionValue["Input"]
];

alphaDivergenceLoss[alpha_?NumericQ /; alpha == 0, _] := AggregationLayer[Mean, All];
alphaDivergenceLoss[DirectedInfinity[1], _]     := AggregationLayer[Min,    All];
alphaDivergenceLoss[DirectedInfinity[-1], _]    := AggregationLayer[Max,    All];

alphaDivergenceLoss[alpha_?NumericQ /; alpha != 0, k_Integer] := NetGraph[
    <|
        "timesAlpha" -> ElementwiseLayer[Function[-alpha #]],
        "max" -> AggregationLayer[Max, 1],
        "rep" -> ReplicateLayer[k],
        "sub" -> ThreadingLayer[Subtract],
        "expAlph" -> ElementwiseLayer[Exp],
        "average" -> AggregationLayer[Mean, 1],
        "logplusmax" ->  ThreadingLayer[Function[{avg, max}, Log[avg] + max]],
        "invalpha" -> ElementwiseLayer[Function[-(# / alpha)]]
    |>,
    {
        NetPort["Input"] -> "timesAlpha",
        "timesAlpha" -> "max" -> "rep",
        {"timesAlpha", "rep"} -> "sub" -> "expAlph" -> "average" ,
        {"average", "max"} -> "logplusmax" -> "invalpha"
    },
    "Input" -> {k}
];
alphaDivergenceLoss[layer_, _] := layer;

Options[sampleTrainedNet] = {
    TargetDevice -> "CPU",
    "StandardDeviations" -> 1
};

extractRegressionNet[net_NetTrainResultsObject] := extractRegressionNet[net["TrainedNet"]];

extractRegressionNet[net : (_NetChain | _NetGraph)] := With[{
    layers = Keys @ NetInformation[net, "Layers"]
},
    Which[
        MemberQ[layers, {"alphaDiv", ___}],
            NetExtract[net, {"regression", "map", "Net"}],
        MemberQ[layers, {"regression", ___}],
            NetExtract[net, "regression"],
        True,
            net
    ]
];

netWeights[net_] := Flatten @ Normal @ Values @ NetInformation[
    NetReplace[net, _BatchNormalizationLayer -> Nothing],
    "Arrays"
];

sampleTrainedNet[
    net : (_NetTrainResultsObject | _NetChain | _NetGraph),
    xvalues_List,
    nSamples : (_Integer?Positive) : 100,
    opts : OptionsPattern[]
] := 
    Module[{
        regnet = extractRegressionNet[net],
        nstdevs = OptionValue["StandardDeviations"],
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
        stdv = nstdevs * Sqrt[Variance[samples[[All, All, 1]]] + Mean[Exp[-samples[[All, All, 2]]]]];
        AssociationThread[
            xvalues,
            Transpose[{
                mean - stdv,
                mean,
                mean + stdv
            }]
        ]
    ];

netRegularizationLoss[net : (_NetTrainResultsObject | _NetChain | _NetGraph), rest__] :=
    netRegularizationLoss[netWeights[net], rest];

netRegularizationLoss[weights_List, lambda_, p_?NumericQ] := If[
    TrueQ[p == 0]
    ,
    lambda * Length[weights]
    ,
    lambda * Total[Abs[weights]^p]
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

End[] (* End Private Context *)

EndPackage[]