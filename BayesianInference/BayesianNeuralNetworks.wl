(* Wolfram Language Package *)

BeginPackage["BayesianNeuralNetworks`"]
(* Exported symbols added here with SymbolName::usage *)

gaussianLossLayer;
regressionNet;
regressionLossNet;
alphaDivergenceLoss;
sampleTrainedNet;

Begin["`Private`"] (* Begin Private Context *)



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
    activation = OptionValue["ActivationFunction"]
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
                    Switch[ pdrop,
                        _?NumericQ,
                            DropoutLayer[pdrop],
                        _Function,
                            DropoutLayer[pdrop[i]],
                        _,
                            Nothing
                    ]
                },
                {i, OptionValue["NetworkDepth"]}
            ],
            LinearLayer[]
        },
        "Input" -> input,
        "Output" -> output
    ]
];

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
        NetPort["x"] -> "regression",
        "regression" -> "part1",
        "regression" -> "part2",
        {NetPort["y"], "part1", "part2"} -> "loss" -> NetPort["Loss"]
    },
    "x" -> OptionValue["Input"]
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
        NetPort["x"] -> "regression",
        "regression" -> "part1",
        "regression" -> "part2",
        NetPort["y"] -> "repY",
        {"repY", "part1", "part2"} -> "loss" -> "alphaDiv" -> NetPort["Loss"]
    },
    "x" -> OptionValue["Input"]
];

alphaDivergenceLoss[alpha_?NumericQ /; alpha == 0, _] := AggregationLayer[Mean,   All];
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
    TargetDevice -> "CPU"
};

sampleTrainedNet[net_NetTrainResultsObject, rest___] := sampleTrainedNet[net["TrainedNet"], rest];

sampleTrainedNet[
    net : (_NetChain | _NetGraph),
    xvalues_List,
    nSamples : (_Integer?Positive) : 100,
    opts : OptionsPattern[]
] := 
    With[{
        regnet = If[
            MemberQ[
                Keys @ NetInformation[net, "Layers"],
                {"alphaDiv", ___}
            ]
            ,
            NetExtract[net, {"regression", "map", "Net"}]
            ,
            NetExtract[net, "regression"]
        ]
    },
        AssociationThread[
            xvalues,
            Map[
                With[{
                    mean = Mean[#[[All, 1]]],
                    stdv = Sqrt[Variance[#[[All, 1]]] + Mean[Exp[-#[[All, 2]]]]]
                },
                    mean + stdv * {-1, 0, 1}
                ]&,
                Transpose @ Table[
                    regnet[xvalues, NetEvaluationMode -> "Train", TargetDevice -> OptionValue[TargetDevice]],
                    {i, nSamples}
                ]
            ]
        ]
    ];

End[] (* End Private Context *)

EndPackage[]