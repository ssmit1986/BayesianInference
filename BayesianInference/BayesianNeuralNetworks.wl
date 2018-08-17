(* Wolfram Language Package *)

BeginPackage["BayesianNeuralNetworks`"]
(* Exported symbols added here with SymbolName::usage *)


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
    "DropoutProbability" -> 0.25,
    "Input" -> Automatic,
    "Output" -> Automatic
}
regressionNet[opts : OptionsPattern[]] := With[{
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
        "Input" -> OptionValue["Input"],
        "Output" -> OptionValue["Output"]
    ]
];

regressionNet[
    "HomoScedastic",
    trainingModel : Automatic : Automatic,
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "reg1" -> regressionNet["Output" -> {1}, opts],
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
] := regressionNet["Output" -> {2}, opts];

regressionNet[
    errorModel_,
    trainingModel : {"AlphaDivergence", k_Integer},
    opts : OptionsPattern[]
] := NetChain[
    <|
        "repInput" -> ReplicateLayer[k],
        "map" -> NetMapOperator[regressionNet[errorModel, Automatic, opts]]
    |>
];

(*lossNet[
    regressionNet_,
    s_String,
    opts : OptionsPattern[]
] := lossNet[
    regressionNet,
    {s, gaussianLossLayer[]},
    opts
];

lossNet[
    regressionNet_,
    {"HomoScedastic", lossLayer : Except[_String]},
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> NetGraph[
            <|
                "reg1" -> regressionNet,
                "const" -> ConstantArrayLayer[]
            |>,
            {
                NetPort["Input"] -> "reg1" -> NetPort["prediction"],
                "const" -> NetPort["logTau"]
            }
        ],
        "loss" -> lossLayer
    |>,
    {
        NetPort["x"] -> "regression",
        {NetPort["y"], NetPort[{"regression", "prediction"}], NetPort[{"regression", "logTau"}]} -> "loss"
    },
    "y" -> {1},
    opts
];

lossNet[
    regressionNet_,
    {"HeteroScedastic", lossLayer : Except[_String]},
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> NetGraph[
            <|
                "reg1" -> NetReplacePart[regressionNet, "Output" -> {2}],
                "part1" -> PartLayer[{{1}}],
                "part2" -> PartLayer[{{2}}]
            |>,
            {
                NetPort["Input"] -> "reg1",
                "reg1" -> "part1" -> NetPort["prediction"],
                "reg1" -> "part2" -> NetPort["logTau"]
            }
        ],
        "loss" -> lossLayer
    |>,
    {
        NetPort["x"] -> "regression",
        {NetPort["y"], NetPort[{"regression", "prediction"}], NetPort[{"regression", "logTau"}]} -> "loss"
    },
    "y" -> {1},
    opts
];

lossNet[
    regressionNet_,
    lossLayer : Except[_List | _String],
    opts : OptionsPattern[]
] := NetGraph[
    <|
        "regression" -> regressionNet,
        "loss" -> lossLayer
    |>,
    {
        NetPort["x"] -> "regression",
        {NetPort["y"], "regression"} -> "loss"
    },
    "y" -> {1},
    opts
];

lossNet[
    regressionNet_,
    loss_,
    {alpha_, k_Integer},
    opts : OptionsPattern[]
] := Module[{
    input,
    tag = "DataDimensions"
},
    input = Lookup[{opts}, "x", Throw[$Failed, tag]];
    If[ !MatchQ[input, {_Integer}],
        Throw[$Failed, tag]
    ];
    input = First[input];
    NetGraph[
        <|
            "repInput" -> ReplicateLayer[k],
            "repOutput" -> ReplicateLayer[{k, 1}],
            "combine" -> CatenateLayer[2],
            "mapLossNet" -> NetMapOperator[
                NetGraph[
                    <|
                        "inputPart" -> PartLayer[1 ;; input],
                        "outputPart" -> PartLayer[input + 1],
                        "lossnet" -> lossNet[regressionNet, loss, opts]
                    |>,
                    {
                        NetPort["Input"] -> "inputPart",
                        NetPort["Input"] -> "outputPart",
                        "inputPart" -> NetPort[{"lossnet", "x"}],
                        "outputPart" -> NetPort[{"lossnet", "y"}]
                    }
                ]
            ],
            "alphaDivergence" -> alphaDivergenceLoss[alpha, k]
        |>,
        {
            NetPort["x"] -> "repInput",
            NetPort["y"] -> "repOutput",
            {"repInput", "repOutput"} -> "combine" -> "mapLossNet" -> "alphaDivergence"
        },
        "y" -> {1},
        opts
    ]
];*)

alphaDivergenceLoss[0, _]                       := AggregationLayer[Mean,   All];
alphaDivergenceLoss[DirectedInfinity[1], _]     := AggregationLayer[Min,    All];
alphaDivergenceLoss[DirectedInfinity[-1], _]    := AggregationLayer[Max,    All];

alphaDivergenceLoss[alpha_?NumericQ /; alpha != 0, k_Integer] := NetGraph[
    <|
        "timesAlpha" -> ElementwiseLayer[Function[-alpha #]],
        "max" -> AggregationLayer[Max, 1],
        "rep" -> ReplicateLayer[k],
        "sub" -> ThreadingLayer[Subtract],
        "expAlph" -> ElementwiseLayer[Exp],
        "sum" -> SummationLayer[],
        "logplusmax" ->  ThreadingLayer[Function[{sum, max}, Log[sum] + max]],
        "invalpha" -> ElementwiseLayer[Function[-(# / alpha)]]
    |>,
    {
        NetPort["Input"] -> "timesAlpha",
        "timesAlpha" -> "max" -> "rep",
        {"timesAlpha", "rep"} -> "sub" -> "expAlph" -> "sum" ,
        {"sum", "max"} -> "logplusmax" -> "invalpha"
    },
    "Input" -> {k}
];

End[] (* End Private Context *)

EndPackage[]