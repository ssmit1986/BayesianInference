(* Wolfram Language Package *)

BeginPackage["FunctionRepositoryFunctions`"]
(* Exported symbols added here with SymbolName::usage *)

crossValidateModel::usage = "crossValidateModel[data, fitFunction] repeatedly splits the data into training/validation subsets; then fits a model using fitFunction on the training set and validates the result with the validation set.";
conditionedMultinormalDistribution::usage = "conditionedMultinormalDistribution[dist, {i1 -> val1, ...}, {j1, j2, ...}] gives the {j1, j2, ...} marginal of dist when the indices {i1, ...} are conditioned to values {val1, ...}";
kullbackLeiblerDivergence::usage = "kullbackLeiblerDivergence[P, Q] computes the Kullback-Leibler divergence from distribution Q to P";
multiNonlinearModelFit;
sparseAssociation;
firstMatchingValue::usage = "firstMatchingValue[{expr_1, expr_2, ...}, pattern] evalutates held expr_i in turn, returning the value of the first expression that evaluates to a result matching the pattern.";
deleteContainedStrings::usage = "deleteContainedStrings[{str1, str2, ...}] deletes every string that is a substring of at least one other string in the list. Preserves ordering.";

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
        data, nDat,
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
kFoldValidation[data_, nData_, estimator_, tester_, opts : OptionsPattern[]] := Module[{
    nRuns = OptionValue["Runs"],
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
subSamplingValidation[data_, nData_, estimator_, tester_, opts : OptionsPattern[]] := Module[{
    nRuns = OptionValue["Runs"],
    nVal,
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


conditionedMultinormalDistribution::noDim = "Distribution has no dimensions left after conditioning on indices `1`";
conditionedMultinormalDistribution::dupIndex = "Duplicate indices found among the conditioning indices `1` and marginalization indices `2`";
conditionedMultinormalDistribution[dist_, {}] := dist;
conditionedMultinormalDistribution[dist_, {}, All] := dist;

conditionedMultinormalDistribution[dist_, {}, marginals_] := 
    MarginalDistribution[dist, marginals];

conditionedMultinormalDistribution[dist_, rule_Rule, rest___] :=
    conditionedMultinormalDistribution[dist, Flatten @ {Thread[rule]}, rest];

conditionedMultinormalDistribution[Inactive[MultinormalDistribution][cov_?SquareMatrixQ], rest___] := 
    conditionedMultinormalDistribution[
        Inactive[MultinormalDistribution][ConstantArray[0, Length[cov]], cov],
        rest
    ];

conditionedMultinormalDistribution[
    Alternatives[
        (head : MultinormalDistribution)[mu_, cov_]?DistributionParameterQ,
        (head : Inactive[MultinormalDistribution])[mu_ , cov_] /; With[
            {lm = Length[mu]},
            lm === Length[cov] && lm > 1
        ]
    ],
    rules : {(_Integer -> _) ..},
    marginals : (_Integer | {__Integer} | All) : All
] := With[{
    eval = conditionedMultinormalDistribution[{mu, cov}, rules, marginals]
},
    Replace[
        conditionedMultinormalDistribution[{mu, cov}, rules, marginals],
        {
            {m_?VectorQ, c_?MatrixQ} :> head[m, c],
            {m_, var_} :> NormalDistribution[m, Sqrt[var]]
        }
    ] /; ListQ[eval]
];

conditionedMultinormalDistribution[
    {mu_?VectorQ, cov_?SquareMatrixQ},
    rules : {(_Integer -> _) ..},
    marginals : (_Integer | {__Integer} | All) : All
] /; Replace[
    DuplicateFreeQ[Flatten @ {rules[[All, 1]], marginals}],
    False :> (Message[conditionedMultinormalDistribution::dupIndex, rules[[All, 1]], marginals]; False)
]:= Module[{
    dim = Length[mu],
    indexKeep, indexDrop,
    partitionedMu, partionedCov ,
    rulesNoDup, conditionValues,
    inv22, dist,
    sparseQ, symmetrizedQ,
    numericQ
},
    Condition[
        sparseQ = Head[cov] === SparseArray;
        symmetrizedQ = Head[cov] === StructuredArray;
        rulesNoDup = AssociationThread[Mod[rules[[All, 1]], dim, 1], rules[[All, 2]]];
        indexDrop = Keys[rulesNoDup];
        conditionValues = Values[rulesNoDup];
        numericQ = MatrixQ[cov, NumericQ] && VectorQ[conditionValues, NumericQ];
        indexKeep = Replace[
            marginals,
            {
                All :> Complement[Range[dim], indexDrop], 
                i_Integer :> {Mod[i, dim, 1]},
                ints_List :> Mod[ints, dim, 1]
            }
        ];
        partitionedMu = mu[[#]] & /@ {indexKeep, indexDrop};
        partionedCov = {
            {cov[[indexKeep, indexKeep]], cov[[indexKeep, indexDrop]]},
            {cov[[indexDrop, indexKeep]], cov[[indexDrop, indexDrop]]}
        };
        inv22 = Which[
            numericQ && sparseQ,
                LinearSolve[partionedCov[[2, 2]]],
            numericQ && symmetrizedQ, (* LinearSolve is better optimized for sparse numerical arrays *)
                LinearSolve[SparseArray @ partionedCov[[2, 2]]],
            True,
                With[{inv = Inverse[partionedCov[[2, 2]]]},
                    Function[inv . #]
                ]
        ];
        dist = Quiet[
            {
                partitionedMu[[1]] + partionedCov[[1, 2]] . inv22[Subtract[conditionValues, partitionedMu[[2]]]],
                Replace[
                    Subtract[
                        partionedCov[[1, 1]], 
                        partionedCov[[1, 2]] . If[ sparseQ,
                            SparseArray @ inv22[partionedCov[[2, 1]]],
                            inv22[partionedCov[[2, 1]]]
                        ]
                    ],
                    m_?(MatrixQ[#, NumericQ]&) :> Divide[Transpose[m] + m, 2] (* guarantees symmetry of numerical results *)
                ]
            },
            LinearSolve::exanexb
        ];
        If[ IntegerQ[marginals],
            Flatten[dist],
            If[ symmetrizedQ,
                MapAt[SymmetrizedArray[#, Automatic, Symmetric[{1, 2}]]&, dist, 2],
                dist
            ]
        ]
        ,
        And[
            Replace[
                Length[rules] < dim,
                False :> (Message[conditionedMultinormalDistribution::noDim, rules[[All, 1]]]; False)
            ],
            Length[cov] === dim
        ]
    ]
];

Options[kullbackLeiblerDivergence] = {
    Method -> Expectation,
    Assumptions :> $Assumptions
};
kullbackLeiblerDivergence::method =  "Method `1` is not Expectation or NExpectation.";
kullbackLeiblerDivergence::randomSample = "Unable to sample from `1` and `2`. Cannot use Method NExpectation.";
kullbackLeiblerDivergence::supportPQ =  "The support of `1` is not a subset of the support of `2`.";
kullbackLeiblerDivergence::supportValidationFail  = "Failed to verify that the support of `1` is a subset of the support of `2`. Calculation will still be attempted.";

(* The divergence from a distribution to itself is 0 *)
kullbackLeiblerDivergence[p_, p_, OptionsPattern[]] := 0;

kullbackLeiblerDivergence[p_?DistributionParameterQ, q_?DistributionParameterQ, opts : OptionsPattern[]] := Block[{
    $Assumptions = OptionValue[Assumptions]
},
    Module[{
        methodSpec = Replace[OptionValue[Method], sym : Except[_List] :> {sym}],
        method, methodOpts,
        domainp, domainq,
        assumptions,
        rv, Global`x
    },
        If[ FreeQ[{p, q}, \[FormalX]],
            (* 
                If p and q are free of FormalX it can be used as a dummy variable, which typesets nicer if Expectation returns unevaluated. 
                Otherwise use a temporary Global`x localized within this Module. Most of the time x shouldn't appear in the output anyway.
            *)
            Global`x = \[FormalX]
        ];
        {method, methodOpts} = TakeDrop[methodSpec, 1];
        method = First[method];
        Switch[ method,
            Expectation, Null,
            NExpectation,
            With[{rand = Quiet[RandomVariate[#, 5] & /@ {p, q}]}, (* 
                Test if p and q can be sampled from *)
                If[! AllTrue[rand, ArrayQ],
                    Message[kullbackLeiblerDivergence::randomSample, p, q];
                    Return[$Failed]
                ]
            ],
            _, (Message[kullbackLeiblerDivergence::method, method]; Return[$Failed])
        ];
        domainp = DistributionDomain[p];
        domainq = DistributionDomain[q];
        assumptions = And @@ Map[DistributionParameterAssumptions, {p, q}];
        Switch[(* Test supports of p and q *)
            Assuming[assumptions, Simplify @ supportSubSetQ[domainp, domainq]],
            True, Null,
            False,
            (
                Message[kullbackLeiblerDivergence::supportPQ, p, q];
                Return[Undefined]
            ),
            _, Message[kullbackLeiblerDivergence::supportValidationFail, p, q]
        ];
        rv = Replace[domainp, (* initialize dummy variable used in Expectation or NExpectation *)
            {
                l : {domainPattern ..} :> Array[Global`x, Length[l]],
                _ -> Global`x
            }
        ];
        Assuming[ assumptions,
            Simplify[
                method[
                    LogLikelihood[p, {rv}] - LogLikelihood[q, {rv}],
                    Distributed[rv, p],
                    Sequence @@ methodOpts
                ],
                TimeConstraint -> {2, 10}
            ]
        ]
    ]
];

empiricalDistDomainPattern = {Except[_Span | _Interval | _List] ..};
domainPattern = Alternatives[
    empiricalDistDomainPattern,(* Empirical distributions *)
    _Span,(* Discrete distributions *)
    _Interval  (*Continuous distributions*)
];

(*Multi-dimensional distributions *)
supportSubSetQ[p : {domainPattern ..}, q : {domainPattern ..}] /; Length[p] =!= Length[q] := False;
supportSubSetQ[p : {domainPattern ..}, q : {domainPattern ..}] := And @@ MapThread[supportSubSetQ, {p, q}];

supportSubSetQ[Span[p__?NumericQ], q_] := supportSubSetQ[Range[p], q];
supportSubSetQ[p_, Span[q__?NumericQ]] := supportSubSetQ[p, Range[q]];

supportSubSetQ[p : empiricalDistDomainPattern, q : empiricalDistDomainPattern] := SubsetQ[q, p];

(* Backups for infinite/symbolic spans *)
supportSubSetQ[p_?( VectorQ[#, IntegerQ] &), q : Span[_, __]] := With[{minmaxp = MinMax[p]},
    q[[1]] <= minmaxp[[1]] && minmaxp[[2]] <= q[[2]]
];

supportSubSetQ[p : Span[_, __], q_?( VectorQ[#, IntegerQ] &)] := With[{minmaxq = MinMax[q]},
    minmaxq[[1]] <= p[[1]] && p[[2]] <= minmaxq[[2]]
];

supportSubSetQ[
    Span[pmin_, pmax_] | Interval[{pmin_, pmax_}],
    Span[qmin_, qmax_] | Interval[{qmin_, qmax_}]
] := qmin <= pmin && pmax <= qmax;


supportSubSetQ[p_Interval, q_Interval] := With[{int = IntervalIntersection[p, q]},
    Condition[
        And @@ MapThread[Equal, {First[int], First[p]}],
        Head[int] === Interval
    ]
];

supportSubSetQ[p_, q_] /; Head[p] =!= Head[q] := False;
supportSubSetQ[__] := Undefined;

Options[multiNonlinearModelFit] = Join[
    Options[NonlinearModelFit],
    {
        "DatasetIndexSymbol" -> \[FormalN]
    }
];

multiNonlinearModelFit[datasets_, form_, fitParams_, independents : Except[_List], opts : OptionsPattern[]] := 
    multiNonlinearModelFit[datasets, form, fitParams, {independents}, opts];
 
multiNonlinearModelFit[datasets_, form : Except[{__Rule}, _List], fitParams_, independents_, opts : OptionsPattern[]] := 
    multiNonlinearModelFit[datasets, <|"Expressions" -> form, "Constraints" -> True|>, fitParams, independents, opts];
 
multiNonlinearModelFit[
    datasets : {__?(MatrixQ[#1, NumericQ] &)}, 
    KeyValuePattern[{"Expressions" -> expressions_List, "Constraints" -> constraints_}], 
    fitParams_List, 
    independents_List,
    opts : OptionsPattern[]
] := Module[{
    fitfun, weights,
    numSets = Length[expressions], 
    augmentedData = Join @@ MapIndexed[
        Join[ConstantArray[N[#2], Length[#1]], #1, 2]&,
        datasets
    ], 
    indexSymbol = OptionValue["DatasetIndexSymbol"]
},
    Condition[
        fitfun = With[{
            conditions = Join @@ ({#1, expressions[[#1]]} & ) /@ Range[numSets]
        }, 
            Switch @@ Prepend[conditions, Round[indexSymbol]]
        ]; 
        weights = Replace[
            OptionValue[Weights],
            {
                (list_List)?(VectorQ[#1, NumericQ]& ) /; Length[list] === numSets :> 
                    Join @@ MapThread[ConstantArray, {list, Length /@ datasets}], 
                list : {__?(VectorQ[#1, NumericQ] & )} /; Length /@ list === Length /@ datasets :>
                    Join @@ list, 
                "InverseLengthWeights" :> Join @@ (ConstantArray[1./#1, #1] & ) /@ Length /@ datasets
            }
        ]; 
        NonlinearModelFit[
            augmentedData,
            If[TrueQ[constraints], fitfun, {fitfun, constraints}], 
            fitParams,
            Flatten[{indexSymbol, independents}],
            Weights -> weights, 
            Sequence @@ FilterRules[{opts}, Options[NonlinearModelFit]]
        ]
        ,
        numSets === Length[datasets]
    ]
];

Options[sparseAssociation] = {"Level" -> Automatic};

sparseAssociation[{}, ___] := <||>;

sparseAssociation[array_?ArrayQ, keys : Except[{__List}, _List], default : Except[_List | _Rule] : 0, opts : OptionsPattern[]] :=
    sparseAssociation[array, ConstantArray[keys, ArrayDepth[array]], default, opts];

sparseAssociation[
    array_?ArrayQ,
    keys : {__List},
    default : Except[_List | _Rule] : 0,
    opts : OptionsPattern[]
] := With[{
    dims = Dimensions[array],
    lvl = OptionValue["Level"]
},
    Condition[
        isparseAssociation[
            ArrayRules[array, default],
            keys
        ]
        ,
        lvl === Automatic && checkKeyDims[dims, Length /@ keys]
    ]
];

sparseAssociation[array_?ArrayQ, default : _ : 0, opts : OptionsPattern[]] := With[{
    lvl = OptionValue["Level"]
},
    isparseAssociation[ArrayRules[array, default]] /; lvl === Automatic
];

sparseAssociation[expr_, keys_List, default : _ : 0, opts : OptionsPattern[]] := Module[{
    level = OptionValue["Level"],
    assoc, keyList
},
    Condition[
        keyList = Replace[keys, l : Except[{__List}] :> ConstantArray[l, level]];
        assoc = positionAssociation[expr, Except[default], {level}];
        If[ And[
                AssociationQ[assoc],
                checkKeyDims[
                    Activate[Thread[Inactive[Max] @@ Keys[assoc]]],
                    Length /@ keyList
                ]
            ],
            isparseAssociation[
                Append[Normal[assoc], {_} -> default],
                keyList
            ],
            $Failed
        ]
        ,
        IntegerQ[level]
    ] 
];
sparseAssociation[expr_, default : _ : 0, opts : OptionsPattern[]] := Module[{
    level = OptionValue["Level"],
    assoc
},
    Condition[
        assoc = positionAssociation[expr, Except[default], {level}];
        If[ AssociationQ[assoc],
            isparseAssociation[Append[Normal[assoc], {_} -> default]],
            $Failed
        ],
        IntegerQ[level]
    ]
];

checkKeyDims[arrayDims_List, keyDims_List] := TrueQ @ And[
    Length[arrayDims] === Length[keyDims],
    And @@ Thread[keyDims >= arrayDims]
];
checkKeyDims[___] := False;

isparseAssociation[{{Verbatim[_]..} -> default_}, ___] := <|"Data" -> <||>, "Default" -> default|>;

isparseAssociation[rules_List] := Module[{
    depth = Length[rules[[1, 1]]],
    assoc
},
    Condition[
        assoc = GroupBy[
            Most @ rules,
            Map[ (* generate list of grouping rules *)
                Function[ind,
                    Function[#[[1, ind]]]
                ],
                Range[depth]
            ],
            #[[1, 2]]& (* extract the element at the given position *)
        ];
        <|
            "Data"-> assoc,
            "Default" -> rules[[-1, 2]]
        |>
        ,
        depth > 0
    ]
];

isparseAssociation[rules_, keys : {__List}] := isparseAssociation[indexRulesToKeys[rules, keys]];

indexRulesToKeys[list_, keys_] := Module[{
    rules = list
},
    rules[[;; -2, 1]] = MapIndexed[
        keys[[#2[[2]], #1]] &,
        rules[[;; -2, 1]],
        {2}
    ];
    rules
];

Options[positionAssociation] = {Heads -> False};
positionAssociation[expr_, args__, opts : OptionsPattern[]] := With[{
    pos = Position[expr, args, Heads -> OptionValue[Heads]]
},
    AssociationThread[pos, Extract[expr, pos]] /; ListQ[pos]
];

SetAttributes[firstMatchingValue, HoldFirst];
Options[firstMatchingValue] = Options[FirstCase];
firstMatchingValue[expr_, pattern_, args___] := FirstCase[
    Unevaluated[expr],
    _?(MatchQ[pattern]),
    args
];

Options[deleteContainedStrings] = Options[StringContainsQ];
deleteContainedStrings[{}, ___] := {};
deleteContainedStrings[strings : {__String}, opts : OptionsPattern[]] := Module[{
    sorted = ReverseSortBy[strings, StringLength]
},
    SortBy[
        DeleteDuplicates[sorted, StringContainsQ[##, opts] &],
        FirstPosition[strings, #, Missing[], {1}, Heads -> False] &
    ]
];

End[] (* End Private Context *)

EndPackage[]