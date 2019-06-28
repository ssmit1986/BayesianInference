BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

naturalParameters;
naturalParametersCount;
logPartition;
sufficientStatistic;
baseMeasure;
cannonicalPDF;
priorKernel;

Begin["`Private`"]

specifiedDefinitionPattern = _Symbol[___Symbol];

naturalParameters[dist_Symbol] := Array[Indexed[\[FormalEta], #]&, naturalParametersCount[dist]];
naturalParametersCount[dist_Symbol[___]] := naturalParametersCount[dist];

logPartition[dist_Symbol] := logPartition[dist, \[FormalEta]];
logPartition[dist : specifiedDefinitionPattern] := With[{
    params = naturalParameters[dist]
},
    With[{
        symbols = naturalParameters[Head[dist]]
    },
        ReplaceAll[
            logPartition[Head @ dist, symbols],
            \[FormalEta] -> params
        ]
    ]
];

baseMeasure[dist_] := baseMeasure[dist, \[FormalX]];
sufficientStatistic[dist_] := sufficientStatistic[dist, \[FormalX]];

cannonicalPDF[dist_Symbol] :=
    baseMeasure[dist] * Exp[naturalParameters[dist] . sufficientStatistic[dist] - logPartition[dist]];
cannonicalPDF[dist : specifiedDefinitionPattern, x : _ : \[FormalX]] :=
    baseMeasure[Head @ dist, x] * Exp[naturalParameters[dist] . sufficientStatistic[Head @ dist, x] - logPartition[dist]];

priorKernel[dist_] := With[{
    chi = Array[\[FormalChi], naturalParametersCount[dist]]
},
    Exp[naturalParameters[dist] . chi - \[FormalNu] * logPartition[dist]]
];

(* ExponentialDistribution *)
naturalParameters[ExponentialDistribution[lambda_]] := {-lambda};
naturalParametersCount[ExponentialDistribution] = 1;

baseMeasure[ExponentialDistribution, x_] := 1;
sufficientStatistic[ExponentialDistribution, x_] := {Indexed[x, 1]};
logPartition[ExponentialDistribution, sym_] := - Log[- Indexed[sym, 1]];

(* NormalDistribution *)
naturalParameters[NormalDistribution[m_, s_]] := {m/s^2, -1/(2 * s^2)};
naturalParametersCount[NormalDistribution] = 2;

baseMeasure[NormalDistribution, x_] := 1/Sqrt[2 * Pi];
sufficientStatistic[NormalDistribution, x_] := {Indexed[x, 1], Indexed[x, 1]^2};
logPartition[NormalDistribution, sym_] := - Indexed[sym, 1]^2 / (4 * Indexed[sym, 2]) - 1/2 * Log[-2 * Indexed[sym, 2]];

(* PoissonDistribution *)
naturalParameters[PoissonDistribution[lambda_]] := {Log[lambda]};
naturalParametersCount[PoissonDistribution] = 1;

baseMeasure[PoissonDistribution, x_] := 1/x!;
sufficientStatistic[PoissonDistribution, x_] := {Indexed[x, 1]};
logPartition[PoissonDistribution, sym_] := Exp[Indexed[sym, 1]];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]