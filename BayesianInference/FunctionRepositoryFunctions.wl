(* Wolfram Language Package *)

BeginPackage["FunctionRepositoryFunctions`"]
(* Exported symbols added here with SymbolName::usage *)

crossValidateModel;

Begin["`Private`"] (* Begin Private Context *)

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