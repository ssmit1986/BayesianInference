(* Wolfram Language Package *)

BeginPackage["BayesianUtilities`"]
(* Exported symbols added here with SymbolName::usage *)
passOptionsDown::usage = "passOptionsDown[mainFunction, subFunction, {opts}] passes options down correctly from the main function into a sub function, even when the default options for both functions are different";
quietCheck::usage = "quietCheck[expr, failexr, {msg1, msg2, ...}] combines the functionalities of Quiet and Check";
normalizeData;
takePosteriorFraction;
$BayesianContexts;

Begin["`Private`"] (* Begin Private Context *)

$BayesianContexts = Flatten[
    {
        Map[
            {#, # <> "Private`"}&,
            {
                "BayesianUtilities`",
                "BayesianStatistics`",
                "BayesianGaussianProcess`",
                "BayesianVisualisations`"
            }
        ],
        "Global`"
    }
];

quietCheck[expr_, failexpr_, msgs : {__MessageName}] :=
    Quiet[
        Check[
            expr,
            failexpr,
            msgs
        ],
        msgs
    ];
quietCheck[expr_, failexpr_] :=
    Quiet[
        Check[
            expr,
            failexpr
        ]
    ];
SetAttributes[quietCheck, {HoldAll}]

passOptionsDown[functionName_Symbol, {opts : OptionsPattern[]}] := passOptionsDown[functionName, functionName, {opts}];

passOptionsDown[mainFunctionName_Symbol, subFunctionName_Symbol, {opts : OptionsPattern[]}] :=
    FilterRules[
        Thread[
            Rule[
                Options[mainFunctionName][[All, 1]],
                OptionValue[
                    mainFunctionName,
                    Join[
                        {opts},
                        Options[mainFunctionName]
                    ],
                    Options[mainFunctionName][[All, 1]]
                ]
            ]
        ],
        Options[subFunctionName]
    ];

xLogx := Compile[{
    {x, _Real}
},
    If[ x == 0. || x == 1.,
        0.,
        x * Log[x]
    ],
    RuntimeAttributes -> {Listable}
];

xLogy := Compile[{
    {x, _Real},
    {y, _Real}
},
    Which[
        x == 0.,
            0.,
        y == 0.,
            - Sign[x] * $MaxMachineNumber,
        True,
            x * Log[y]
    ],
    RuntimeAttributes -> {Listable}
];

normalizeData[data : {__Rule}, opts : OptionsPattern[]] := normalizeData[
    Developer`ToPackedArray[data[[All, 1]]],
    Developer`ToPackedArray[data[[All, 2]]],
    opts
];

normalizeData[data : Rule[_List, _List], opts : OptionsPattern[]] := normalizeData[data[[1]], data[[2]], opts];

normalizeData[dataIn_List, dataOut_List, opts : OptionsPattern[]] := AssociationThread[
    {"Input", "Output"},
    normalizeData[#, opts]& /@ {dataIn, dataOut}
];

normalizeData[dataSequence : Repeated[_List, {3, Infinity}], opts : OptionsPattern[]] := AssociationThread[
    Range[Length[{dataSequence}]],
    normalizeData[#, opts]& /@ {dataSequence}
];

normalizeData[data_?(MatrixQ[#, NumericQ] || VectorQ[#, NumericQ]&), opts : OptionsPattern[]] := With[{
    mean = First[OptionValue["StandardizationFunctions"], Mean] @ data,
    std = Quiet[
        Replace[
            Last[OptionValue["StandardizationFunctions"], StandardDeviation] @ data,
            _?PossibleZeroQ -> 1,
            {-1}
        ],
        "Packing"
    ]
},
    With[{
        fun = If[ MatrixQ[data]
            ,
            Function[
                Transpose[
                    Divide[Subtract[Transpose[#], mean], std]
                ]
            ]
            ,
            Function[
                Divide[Subtract[#, mean], std]
            ]
        ],
        inv = If[ MatrixQ[data]
            ,
            Function[
                Transpose[
                    Plus[Times[Transpose[#], std], mean]
                ]
            ]
            ,
            Function[
                Plus[Times[#, std], mean]
            ]
        ]
    },
        <|
            "NormalizedData" -> Developer`ToPackedArray[fun[data]],
            "Function" -> fun,
            "InverseFunction" -> inv
        |>
    ]
];
Options[normalizeData] = {
    "StandardizationFunctions" -> {Mean, StandardDeviation}
};

takePosteriorFraction[result_, 1] := MapAt[
    SortBy[-#CrudePosteriorWeight &],
    result,
    {"Samples"}
];

takePosteriorFraction[result_?(AssociationQ[#] && KeyExistsQ[#, "Samples"]&), frac_?NumericQ] /; 0 <= frac < 1 := Module[{
    newSamples = result,
    count = 0
},
    newSamples["Samples"] = TakeWhile[
        SortBy[newSamples["Samples"], -#CrudePosteriorWeight &],
        Function[
            With[{
                boole = count <= frac
            },
                count += #CrudePosteriorWeight;
                boole
            ]
        ]
    ];
    newSamples
];

End[] (* End Private Context *)

EndPackage[]