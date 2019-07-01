BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

naturalParameters;
naturalParametersCount;
logPartition;
sufficientStatistic;
baseMeasure;
cannonicalPDF;
priorKernel;
naturalParametersAssumptions;
naturalParametersRegion;

Begin["`Private`"]

specifiedDistributionPattern = _Symbol[___Symbol]?DistributionParameterQ;

naturalParameters[dist_Symbol] := Array[Indexed[\[FormalEta], #]&, naturalParametersCount[dist]];
naturalParametersCount[dist_Symbol[___]] := naturalParametersCount[dist];

logPartition[dist_Symbol] := logPartition[dist, \[FormalEta]];
logPartition[dist : specifiedDistributionPattern] := With[{
    params = naturalParameters[dist]
},
    ReplaceAll[
        logPartition[Head @ dist],
        \[FormalEta] -> params
    ] /; ListQ[params]
];

baseMeasure[dist_] := baseMeasure[dist, \[FormalX]];
sufficientStatistic[dist_] := sufficientStatistic[dist, \[FormalX]];

cannonicalPDF[dist_Symbol] :=
    baseMeasure[dist] * Exp[naturalParameters[dist] . sufficientStatistic[dist] - logPartition[dist]];
cannonicalPDF[dist : specifiedDistributionPattern, x : _ : \[FormalX]] :=
    baseMeasure[Head @ dist, x] * Exp[naturalParameters[dist] . sufficientStatistic[Head @ dist, x] - logPartition[dist]];

priorKernel[dist_] := With[{
    chi = Array[Indexed[\[FormalChi], #]&, naturalParametersCount[dist]]
},
    ConditionalExpression[
        Exp[naturalParameters[dist] . chi - \[FormalNu] * logPartition[dist]],
        Element[chi, Reals] && \[FormalNu] > 0
    ]
];

naturalParametersAssumptions[dist : specifiedDistributionPattern] := With[{
    eta = naturalParameters[Head @ dist]
},
    Simplify @ And[
        FunctionRange[
            {naturalParameters[dist], DistributionParameterAssumptions[dist]},
            List @@ dist,
            eta,
            Reals
        ],
        Element[eta, Reals]
    ]
];

naturalParametersRegion[dist : specifiedDistributionPattern] := With[{
    assum = naturalParametersAssumptions[dist],
    eta = naturalParameters[Head @ dist]
},
    ImplicitRegion[assum, eta]
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

baseMeasure[PoissonDistribution, x_] := 1/(Indexed[x, 1]!);
sufficientStatistic[PoissonDistribution, x_] := {Indexed[x, 1]};
logPartition[PoissonDistribution, sym_] := Exp[Indexed[sym, 1]];

(* LogNormalDistribution *)
naturalParameters[LogNormalDistribution[m_, s_]] := naturalParameters[NormalDistribution[m, s]];
naturalParametersCount[LogNormalDistribution] = 2;

baseMeasure[LogNormalDistribution, x_] := 1/(Sqrt[2 * Pi] * Indexed[x, 1]);
sufficientStatistic[LogNormalDistribution, x_] := {Log[Indexed[x, 1]], Log[Indexed[x, 1]]^2};
logPartition[LogNormalDistribution, sym_] := logPartition[NormalDistribution, sym];

(* GammaDistribution *)
naturalParameters[GammaDistribution[k_, theta_]] := {k - 1, -1/theta};
naturalParametersCount[GammaDistribution] = 2;

baseMeasure[GammaDistribution, x_] := 1;
sufficientStatistic[GammaDistribution, x_] := {Log[Indexed[x, 1]], Indexed[x, 1]};
logPartition[GammaDistribution, sym_] := Log[Gamma[Indexed[sym, 1] + 1]] - (Indexed[sym, 1] + 1) * Log[-Indexed[sym, 2]];


End[]

EndPackage[(* "BayesianConjugatePriors`" *)]