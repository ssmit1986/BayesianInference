(* Wolfram Language Package *)

BeginPackage["BayesianVisualisations`", { "BayesianUtilities`"}]
(* Exported symbols added here with SymbolName::usage *)  
covarianceMatrixPlot;
posteriorMarginalPDFPlot1D;
posteriorMarginalPDFDensityPlot2D;
posteriorBubbleChart;
regressionPlot1D;


Begin["`Private`"] (* Begin Private Context *) 

covarianceMatrixPlot[inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "EmpiricalPosteriorDistribution"]&)], opts : OptionsPattern[]] := Column[{
    BarChart[
        Mean @ result["EmpiricalPosteriorDistribution"], 
        ChartLabels -> result["ParameterSymbols"],
        ImageSize -> 400,
        PlotLabel -> "Posterior mean values"
    ],
    MatrixPlot[
        Covariance[result["EmpiricalPosteriorDistribution"]],
        Sequence @@ FilterRules[{opts}, Options[MatrixPlot]],
        PlotLegends -> Automatic,
        FrameTicks -> ConstantArray[
            Transpose[{Range[Length[result["ParameterSymbols"]]], result["ParameterSymbols"]}],
            {2, 2}
        ],
        ImageSize -> 400,
        PlotLabel -> "Posterior covariance"
    ]
}, Alignment -> Left];

Options[covarianceMatrixPlot] = Join[
    {},
    Options[MatrixPlot]
];

posteriorMarginalPDFPlot1D[result_, parameter_Symbol, range : _ : Automatic, opts : OptionsPattern[]] /; MemberQ[result["ParameterSymbols"], parameter] :=
    posteriorMarginalPDFPlot1D[result, First @ FirstPosition[result["ParameterSymbols"], parameter, Missing["Error"], {1}], range, opts];

posteriorMarginalPDFPlot1D[inferenceObject[result_?AssociationQ], plotIndex_Integer, range : (Automatic | {_, _}) : Automatic, opts : OptionsPattern[]] /;
    (AllTrue[{"ParameterRanges", "EmpiricalPosteriorDistribution"}, KeyExistsQ[result, #]&] && plotIndex <= Length[result["ParameterRanges"]]) :=
    Module[{
        x, pdf,
        plotRange = Replace[range, Automatic :> result["ParameterRanges"][[plotIndex]]]
    },
        pdf = PDF[
            SmoothKernelDistribution[
                WeightedData @@ Map[
                    MarginalDistribution[
                        result["EmpiricalPosteriorDistribution"],
                        plotIndex
                    ],
                    {"Domain", "Weights"}
                ],
                Sequence @@ OptionValue["SmoothKernelDistributionOptions"]
            ],
            x
        ];
        Plot[
            pdf,
            Evaluate[Flatten @ {x, plotRange}],
            Evaluate[Sequence @@ FilterRules[{opts}, Options[Plot]]],
            PlotRange -> All,
            Filling -> Axis,
            Evaluate[AxesLabel -> {result["ParameterSymbols"][[plotIndex]], "PDF"}]
        ]
    ];

Options[posteriorMarginalPDFPlot1D] = Join[
    {
        "SmoothKernelDistributionOptions" -> {}
    },
    Options[Plot]
];

posteriorMarginalPDFDensityPlot2D[result_, parameters : {_Symbol, _Symbol}, range : _ : Automatic, opts : OptionsPattern[]] /; (
    ListQ[result["ParameterSymbols"]] && SubsetQ[result["ParameterSymbols"], parameters]
) := posteriorMarginalPDFDensityPlot2D[
    result,
    Flatten[
        Position[
            result["ParameterSymbols"],
            Alternatives @@ parameters,
            {1},
            Length[parameters]
        ]
    ],
    range,
    opts
];

posteriorMarginalPDFDensityPlot2D[inferenceObject[result_?AssociationQ], plotIndices : {_Integer, _Integer},
    range : (Automatic | {{_, _}, {_, _}}) : Automatic, opts : OptionsPattern[]
] /; And[
    AllTrue[{"ParameterRanges", "EmpiricalPosteriorDistribution"}, KeyExistsQ[result, #]&],
    Max[plotIndices] <= Length[result["ParameterRanges"]]
] := Quiet[
    Module[{
        x, y, pdf,
        plotRange = Replace[range, Automatic :> result["ParameterRanges"][[plotIndices]]]
    },
        pdf = PDF[
            KernelMixtureDistribution[
                WeightedData @@ MapAt[
                    Transpose,
                    Map[
                        MarginalDistribution[
                            result["EmpiricalPosteriorDistribution"],
                            plotIndices
                        ],
                        {"Domain", "Weights"}
                    ],
                    1
                ],
                Sequence @@ OptionValue["SmoothKernelDistributionOptions"]
            ],
            {x, y}
        ];
        DensityPlot[
            pdf,
            Evaluate[Flatten @ {x, plotRange[[1]]}],
            Evaluate[Flatten @ {y, plotRange[[2]]}],
            Evaluate[Sequence @@ FilterRules[{opts}, Options[DensityPlot]]],
            PlotLegends -> Automatic,
            Evaluate[PlotRange -> Join[plotRange, {All}]],
            Evaluate[FrameLabel -> result["ParameterSymbols"][[plotIndices]]]
        ]
    ],
    {General::munfl}
];

Options[posteriorMarginalPDFDensityPlot2D] = Join[
    {
        "SmoothKernelDistributionOptions" -> {}
    },
    Options[DensityPlot]
];

posteriorMarginalCDFPlot1D[result_, parameter_Symbol, opts : OptionsPattern[]] /; MemberQ[result["ParameterSymbols"], parameter] :=
    posteriorMarginalCDFPlot1D[result, First @ FirstPosition[result["ParameterSymbols"], parameter, Missing["Error"], {1}], opts];

posteriorMarginalCDFPlot1D[inferenceObject[result_?AssociationQ], plotIndex_Integer, range : (Automatic | {_, _}) : Automatic, opts : OptionsPattern[]] /;
    (AllTrue[{"ParameterRanges", "EmpiricalPosteriorDistribution"}, KeyExistsQ[result, #]&] && plotIndex <= Length[result["ParameterRanges"]]) :=
    Module[{
        x, cdf,
        plotRange = Replace[range, Automatic :> result["ParameterRanges"][[plotIndex]]]
    },
        cdf = CDF[
            MarginalDistribution[
                result["EmpiricalPosteriorDistribution"],
                plotIndex
            ],
            x
        ];
        If[ MatchQ[cdf, Plus[Times[__]..]],
            ListStepPlot[
                Transpose[
                    MapAt[
                        Accumulate, 
                        Transpose[
                            SortBy[
                                {#[[2, 1, 1]], #[[1]]} & /@ List @@ cdf, 
                                First
                            ]
                        ],
                        2
                    ]
                ],
                Sequence @@ FilterRules[{opts}, Options[ListStepPlot]],
                PlotRange -> {0, 1},
                Filling -> Axis,
                AxesLabel -> {result["ParameterSymbols"][[plotIndex]], "CDF"}
            ],
            Plot[
                cdf,
                Evaluate[Flatten @ {x, plotRange}],
                Evaluate[Sequence @@ FilterRules[{opts}, Options[Plot]]],
                PlotRange -> {0, 1},
                Filling -> Axis,
                Evaluate[AxesLabel -> {result["ParameterSymbols"][[plotIndex]], "CDF"}]
            ]
        ]
    ];

Options[posteriorMarginalCDFPlot1D] = Join[
    {},
    Options[Plot]
];

posteriorMarginalCDFDensityPlot2D[result_, parameters : {_Symbol, _Symbol},range_, opts : OptionsPattern[]] /;
    (ListQ[result["ParameterSymbols"]] && SubsetQ[result["ParameterSymbols"], parameters]):=
    posteriorMarginalCDFDensityPlot2D[
        result,
        Flatten[
            Position[
                result["ParameterSymbols"],
                Alternatives @@ parameters,
                {1},
                Length[parameters]
            ]
        ],
        range,
        opts
    ];


posteriorMarginalCDFDensityPlot2D[inferenceObject[result_?AssociationQ], plotIndices : {_Integer, _Integer},
    range : (Automatic | {{_, _}, {_, _}}) : Automatic, opts : OptionsPattern[]
] /; (AllTrue[{"ParameterRanges", "EmpiricalPosteriorDistribution"}, KeyExistsQ[result, #]&] && Max[plotIndices] <= Length[result["ParameterRanges"]]):=
    Module[{
        x, y, cdf,
        plotRange = Replace[range, Automatic :> result["ParameterRanges"][[plotIndices]]]
    },
        cdf = CDF[
            MarginalDistribution[
                result["EmpiricalPosteriorDistribution"],
                plotIndices
            ],
            {x, y}
        ];
        ContourPlot[
            cdf,
            Evaluate[Flatten @ {x, plotRange[[1]]}],
            Evaluate[Flatten @ {y, plotRange[[2]]}],
            Evaluate[Sequence @@ FilterRules[{opts}, Options[DensityPlot]]],
            PlotLegends -> Automatic,
            Evaluate[PlotRange -> Join[plotRange, {0, 1}]],
            Evaluate[FrameLabel -> result["ParameterSymbols"][[plotIndices]]]
        ]
    ];

Options[posteriorMarginalCDFDensityPlot2D] = Join[
    {},
    Options[ContourPlot]
];


posteriorBubbleChart[result_, parameters : {Repeated[_Symbol, {2, 3}]}, opts : OptionsPattern[]] /;
    (ListQ[result["ParameterSymbols"]] && SubsetQ[result["ParameterSymbols"], parameters]):=
    posteriorBubbleChart[
        result,
        Flatten[
            Position[
                result["ParameterSymbols"],
                Alternatives @@ parameters,
                {1},
                Length[parameters]
            ]
        ],
        opts
    ];

posteriorBubbleChart[inferenceObject[result_?AssociationQ], plotIndices : {Repeated[_Integer, {2, 3}]}, opts : OptionsPattern[]] /; 
    (KeyExistsQ[result, "Samples"] && Max[plotIndices] <= Length[result[["Samples", 1, "Point"]]]) :=
    Module[{
        data = Query[
            "Samples",
            Values,
            Flatten @ {#Point[[plotIndices]], #CrudePosteriorWeight}&
        ] @ result,
        plotFunction,
        label
    },
        If[ Length[plotIndices] === 2,
            plotFunction = BubbleChart;
            label = FrameLabel
            ,
            plotFunction = BubbleChart3D;
            label = AxesLabel
        ];
        plotFunction[
            data,
            Sequence @@ FilterRules[{opts}, Options[plotFunction]],
            label -> result["ParameterSymbols"][[plotIndices]],
            ColorFunction -> Function[Opacity[0.7]]
        ]
    ];

Options[posteriorBubbleChart] = Join[
    {},
    DeleteDuplicatesBy[
        Join[
            Options[BubbleChart],
            Options[BubbleChart3D]
        ],
        First
    ]
];

regressionPlot1D[
    inferenceObject[result_?(AssociationQ[#] && KeyExistsQ[#, "Data"]&)],
    predictedDistributions_?AssociationQ,
    opts : OptionsPattern[]
] := Show[
        regressionPlot1D[
            predictedDistributions,
            opts,
            PlotLabel -> Style[StringForm[
                "Log evidence: `1` \[PlusMinus] `2`",
                Sequence @@ (
                    NumberForm[#, 4]& /@ Values[result["LogEvidence"]]
                )
            ], "Text"]
        ],
        Graphics[
            {
                Red,
                Point[
                    Transpose[List @@ (Flatten /@ result["Data"])]
                ]
            }
        ]
    ];

regressionPlot1D[predictedDistributions_?AssociationQ, opts : OptionsPattern[]] := Quiet[
    With[{
        distributionPercentiles = Replace[
            OptionValue["DistributionPercentiles"],
            {
                "Moments" -> Function[
                    Dot[
                        {
                            {1,  1,   1},
                            {1,  0,   0},
                            {1,  -1,  1}
                        },
                        {Mean[#], StandardDeviation[#], Surd[CentralMoment[#, 3], 3]}
                    ]
                ]
                ,
                levels : {__?NumericQ} /; (Min[levels] > 0 && Max[levels] < 1) :>
                    Function[InverseCDF[#, levels]]
            }
        ]
    },
        Module[{
            plotPoints = Map[
                distributionPercentiles,
                KeySort[predictedDistributions]
            ]
        },
            ListPlot[
                plotPoints[[All, #]]& /@ Range[Length[First @ plotPoints]],
                Sequence @@ FilterRules[{opts}, Options[ListPlot]],
                Joined -> True,
                PlotLegends -> Quiet[Thread @ distributionPercentiles["y[x]"]]
            ]
        ]
    ],
    {General::munfl}
];
Options[regressionPlot1D] = Join[
    {
        "DistributionPercentiles" -> {0.95, 0.5, 0.05}
    },
    Options[ListPlot]
];

End[] (* End Private Context *)

EndPackage[]