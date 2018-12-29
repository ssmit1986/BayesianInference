BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

posteriorNormal;
posteriorMultivariateNormal;

Begin["`Private`"]

(*
    normalInverseGammaDistribution[mu0, lambda0, beta0, nu0] :
    mu0: estimate of mean
    lambda0: number of samples upon which mu0 was estimated. lambda0 > 0
    beta0: estimate of variance * 2 nu0 (i.e., sum of square deviations)
    nu0: 2 * the number of samples used to estimate beta0. nu0 > 0
*)

updateDistributionParameters[
    data_List,
    normalInverseGammaDistribution[mu0_, lambda0_, beta0_, nu0_]
] := With[{
    mean = Mean[data],
    var = Variance[data],
    nDat = Length[data]
},
    normalInverseGammaDistribution[
        Divide[
            lambda0 * mu0 + nDat * mean,
            lambda0 + nDat
        ],
        lambda0 + nDat,
        beta0 + Divide[(nDat-1) * var, 2] + Divide[lambda0 * nDat, 2 * (lambda0 + nDat)] * (mean - mu0)^2,
        nu0 + nDat/2
    ]
];

normalInverseGammaPDF[{mu_, lambda_, beta_, nu_}, {x_, var_}]:=
    PDF[NormalDistribution[mu, Sqrt[var/lambda]], x] * PDF[InverseGammaDistribution[nu, beta], var];

normalInverseGammaLogPDF[{mu_, lambda_, beta_, nu_}, {x_, var_}]:=
    LogLikelihood[NormalDistribution[mu, Sqrt[var/lambda]], {x}] + LogLikelihood[InverseGammaDistribution[nu, beta], {var}];

Options[posteriorNormal] = {
    "Prior" -> {"Mu" -> 0, "Lambda" -> 1/100, "Beta" -> 1, "Nu" -> 1/100}
};

posteriorNormal[
    data_List?(VectorQ[#, NumericQ]&),
    opts : OptionsPattern[]
] := Module[{
    mu0, lambda0, beta0, nu0,
    mu, lambda, beta, nu,
    mean = Mean[data],
    var = Variance[data],
    nDat = Length[data],
    meanDiff,
    varDist,
    defaultPrior = OptionValue[posteriorNormal, {}, "Prior"],
    prior
},
    prior = Replace[
        OptionValue["Prior"],
        Except[{___Rule} | _?AssociationQ] :> defaultPrior
    ];
    {mu0, lambda0, beta0, nu0} = Lookup[prior, #, Lookup[defaultPrior, #, 0]]& /@ {"Mu","Lambda","Beta", "Nu"};
    meanDiff = mean - mu0;
    beta = beta0 + Divide[(nDat-1) * var, 2] + Divide[lambda0 * nDat, 2 * (lambda0 + nDat)] * meanDiff^2;
    mu = Divide[
        lambda0 * mu0 + nDat * mean,
        lambda0 + nDat
    ];
    lambda = lambda0 + nDat;
    nu = nu0 + nDat/2;
    varDist = InverseGammaDistribution[nu, beta];
    <|
        "Mean"-> mean,
        "Variance"->var,
        "StandardDeviation"-> Sqrt[var],
        "MuDistribution" -> StudentTDistribution[mu, Sqrt[beta/(lambda * nu)], 2 * nu](* == ParameterMixtureDistribution[
            NormalDistribution[mu, Sqrt[\[FormalV] / lambda]],
            Distributed[\[FormalV], varDist]
        ]*),
        "PosteriorPredictiveDistribution"-> StudentTDistribution[mu, Sqrt[beta * (lambda + 1)/(lambda * nu)], 2 * nu] (* == ParameterMixtureDistribution[
            ParameterMixtureDistribution[
                NormalDistribution[\[FormalU], Sqrt[\[FormalV]]],
                Distributed[\[FormalU], NormalDistribution[mu, Sqrt[\[FormalV]/lambda]]]
            ],
            Distributed[\[FormalV], varDist]
        ]*),
        "VarianceDistribution" -> varDist,
        "Mu"-> mu,
        "Lambda" -> lambda,
        "Beta" -> beta,
        "Nu" -> nu,
        "LogEvidence" ->If[ TrueQ[lambda0 > 0 && nu0 > 0&& beta0 > 0],
            With[{
                muTest = mean,
                varTest = var
            },
                Subtract[
                    LogLikelihood[NormalDistribution[muTest, Sqrt[varTest]], data] + normalInverseGammaLogPDF[{mu0, lambda0, beta0, nu0}, {muTest, varTest}],
                    normalInverseGammaLogPDF[{mu, lambda, beta, nu}, {muTest, varTest}]
                ]
            ],
            Undefined
        ]
    |>
];

(*
    normalInverseWishartDistribution[mu0, lambda0, psi0, nu0] :
    mu0: estimate of mean
    lambda0: number of samples upon which mu0 was estimated. lambda0 > 0
    psi0: estimate of covariance matrix * nu0 (dimensions p x p)
    nu0: number of samples used to estimate psi0. nu0 > p - 1
*)

updateDistributionParameters[
    data_List,
    normalInverseWishartDistribution[mu0_, lambda0_, psi0_, nu0_]
] := Module[{
    mean = Mean[data],
    cov = Covariance[data],
    nDat = Length[data],
    meanDiff
},
    meanDiff = mean - mu0;
    normalInverseWishartDistribution[
        Divide[
            lambda0 * mu0 + nDat * mean,
            lambda0 + nDat
        ],
        lambda0 + nDat,
        psi0 + (nDat-1) * cov + Divide[lambda0 * nDat, lambda0 + nDat] * (List /@ meanDiff) . {meanDiff},
        nu0 + nDat
    ]
]

multiVariateGamma[a_, 1] := Gamma[a];
multiVariateGamma[a_, p_Integer /; p > 1] := (
    multiVariateGamma[a, p] = Pi^((p-1)/2) * multiVariateGamma[a, p - 1] * Gamma[a + (1 - p)/2]
);

inverseWishartPDF[{nu_,psi_?SquareMatrixQ}, sigma_?SquareMatrixQ] /; Dimensions[psi] === Dimensions[sigma] := With[{
    p = Length[sigma]
},
    Det[psi]^(nu/2)/(2^((nu * p)/2) * multiVariateGamma[nu/2, p]) * Det[sigma]^(-((nu + p + 1)/2)) * Exp[-Tr[LinearSolve[sigma, psi]]/2]
];

inverseWishartLogPDF[{nu_, psi_?SquareMatrixQ}, sigma_?SquareMatrixQ]/; Dimensions[psi] === Dimensions[sigma] := With[{
    p = Length[sigma]
},
    Log[Det[psi]] * nu/2 - Log[multiVariateGamma[nu/2, p]] - Log[2] * (nu * p)/2 - Log[Det[sigma]] * (nu + p + 1)/2 - (1/2) * Tr[LinearSolve[sigma,psi]]
];

normalInverseWishartPDF[{mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_},{x_?VectorQ, sigma_?SquareMatrixQ}] /;
    Dimensions[psi] === Dimensions[sigma] && Length[mu] === Length[x] === Length[psi] :=
        PDF[MultinormalDistribution[mu, sigma/lambda], x] * inverseWishartPDF[{nu, psi}, sigma];

normalInverseWishartLogPDF[{mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_},{x_?VectorQ, sigma_?SquareMatrixQ}] /; 
    Dimensions[psi] === Dimensions[sigma]&&Length[mu]===Length[x]===Length[psi] :=
        LogLikelihood[MultinormalDistribution[mu, sigma/lambda], {x}] + inverseWishartLogPDF[{nu,psi}, sigma];

Options[posteriorMultivariateNormal] = {
    "Prior" -> {"Mu" -> 0, "Lambda" -> 1/100, "Psi" -> 1, "Nu" -> Automatic},
    "CovarianceSamples" -> 100
};

posteriorMultivariateNormal[
    data_List?(MatrixQ[#, NumericQ]&),
    opts : OptionsPattern[]
] := Module[{
    mu0, lambda0, psi0, nu0,
    mu, lambda, psi, nu,
    mean = Mean[data],
    cov = Covariance[data],
    nDat, nFeat,
    meanDiff,
    sampledCovariances,
    covDist,
    defaultPrior = OptionValue[posteriorMultivariateNormal, {}, "Prior"],
    prior,
    nSamples = Replace[
        OptionValue["CovarianceSamples"], 
        {n_?NumericQ :> Round[n], _ -> 1000}
    ]
},
    prior = Replace[
        OptionValue["Prior"],
        Except[{___Rule} | _?AssociationQ] :> defaultPrior
    ];
    {nDat, nFeat} = Dimensions[data];
    {mu0, lambda0} = Lookup[prior, #, Lookup[defaultPrior, # , 0]]& /@ {"Mu","Lambda"};
    mu0 = Replace[mu0, n_?NumericQ :> ConstantArray[n, nFeat]];
    nu0 = Replace[
        Lookup[prior,"Nu", Lookup[defaultPrior, "Nu" , 0]],
        Except[_?NumericQ]-> nFeat - 1 + 1/100
    ];
    psi0 = Replace[
        Lookup[prior,"Psi", Lookup[defaultPrior, "Psi" , 0]],
        {
            n_?NumericQ:> n * IdentityMatrix[nFeat],
            vec_?(VectorQ[#, NumericQ]&) :> DiagonalMatrix[vec]
        }
    ];
    meanDiff = mean - mu0;
    psi = psi0 + (nDat-1) * cov + Divide[lambda0 * nDat, lambda0 + nDat] * (List /@ meanDiff) . {meanDiff};
    mu = Divide[
        lambda0 * mu0 + nDat * mean,
        lambda0 + nDat
    ];
    lambda = lambda0 + nDat;
    nu = nu0 + nDat;
    covDist = InverseWishartMatrixDistribution[nu, psi];
    sampledCovariances = Divide[
        RandomVariate[covDist, nSamples],
        lambda
    ];
    <|
        "MuDistribution"-> MixtureDistribution[ConstantArray[1 / Length[#], Length[#]], #]& @ Table[
            MultinormalDistribution[mu, cv],
            {cv, sampledCovariances}
        ],
        "CovarianceDistribution" -> covDist,
        "Mu"-> mu,
        "Lambda" -> lambda,
        "Psi" ->psi,
        "Nu" -> nu,
        "LogEvidence"-> With[{
            muTest = mean,
            covTest = cov
        },
            Replace[Except[_?NumericQ]-> Undefined] @ Quiet @ Subtract[
                LogLikelihood[MultinormalDistribution[muTest, covTest], data] + normalInverseWishartLogPDF[{mu0, lambda0, psi0, nu0}, {muTest, covTest}],
                normalInverseWishartLogPDF[{mu, lambda, psi, nu},{muTest, covTest}]
            ]
        ]
    |>
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]