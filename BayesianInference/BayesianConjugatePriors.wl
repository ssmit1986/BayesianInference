BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

posteriorNormal;
posteriorMultivariateNormal;
updateDistributionParameters::usage = "posterior = updateDistributionParameters[data, model, conjugate prior] updates the distribution of the parameters of a model";
normalInverseGammaDistribution;
normalInverseWishartDistribution;
linearModelDistribution;

Begin["`Private`"]

(*
    normalInverseGammaDistribution[mu0, lambda0, beta0, nu0] :
    mu0: estimate of mean
    lambda0: number of samples upon which mu0 was estimated. lambda0 > 0
    beta0: estimate of variance * 2 nu0 (i.e., sum of square deviations)
    nu0: 2 * the number of samples used to estimate beta0. nu0 > 0
*)
normalInverseGammaDistribution /: MarginalDistribution[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    1
] := ParameterMixtureDistribution[
    NormalDistribution[mu, Sqrt[\[FormalV] / lambda]],
    Distributed[\[FormalV], InverseGammaDistribution[nu, beta]]
];

normalInverseGammaDistribution /: MarginalDistribution[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    2
] := InverseGammaDistribution[nu, beta];

normalInverseGammaDistribution /: RandomVariate[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    n_Integer?Positive
] := With[{
    samples = RandomVariate[InverseGammaDistribution[nu, beta], n]
},
    Table[
        {RandomVariate[NormalDistribution[mu, Sqrt[var / lambda]]], var},
        {var, samples}
    ]
];


normalInverseGammaDistribution /: PDF[normalInverseGammaDistribution[mu_, lambda_, beta_, nu_], {x_, var_}] :=
    PDF[NormalDistribution[mu, Sqrt[var/lambda]], x] * PDF[InverseGammaDistribution[nu, beta], var];

normalInverseGammaDistribution /: LogLikelihood[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    {x : Except[_List], var : Except[_List]}
] := LogLikelihood[NormalDistribution[mu, Sqrt[var/lambda]], {x}] + LogLikelihood[InverseGammaDistribution[nu, beta], {var}];

normalInverseGammaDistribution /: LogLikelihood[normalInverseGammaDistribution[mu_, lambda_, beta_, nu_], pts : {{_, _}..}] :=
    Sum[
        LogLikelihood[normalInverseGammaDistribution[mu, lambda, beta, nu], pt],
        {pt, pts}
    ];

(* Default non-informative prior *)
updateDistributionParameters[NormalDistribution[_Symbol, _Symbol]] := normalInverseGammaDistribution[0, 1/100, 1/200, 1/200];

updateDistributionParameters[
    data_List?VectorQ,
    dist_NormalDistribution
] := updateDistributionParameters[
    data,
    dist,
    updateDistributionParameters[dist]
];

updateDistributionParameters[
    data_List?VectorQ,
    NormalDistribution[_Symbol, _Symbol],
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

Options[posteriorNormal] = {
    "Prior" -> {"Mu" -> 0, "Lambda" -> 1/100, "Beta" -> 1/200, "Nu" -> 1/200}
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
                    Plus[
                        LogLikelihood[NormalDistribution[muTest, Sqrt[varTest]], data],
                        LogLikelihood[normalInverseGammaDistribution[mu0, lambda0, beta0, nu0], {muTest, varTest}]
                    ],
                    LogLikelihood[normalInverseGammaDistribution[mu, lambda, beta, nu], {muTest, varTest}]
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

(*
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
*)

normalInverseWishartDistribution /: MarginalDistribution[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    2
] := InverseWishartMatrixDistribution[nu, psi];

normalInverseWishartDistribution /: RandomVariate[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    n_Integer?Positive
] /; Length[mu] === Length[psi] := With[{
    samples = RandomVariate[InverseWishartMatrixDistribution[nu, psi], n]
},
    Table[
        {RandomVariate[MultinormalDistribution[mu, cov/lambda]], cov},
        {cov, samples}
    ]
];

normalInverseWishartDistribution /: PDF[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    {x_?VectorQ, sigma_?SquareMatrixQ}
] := Exp @ LogLikelihood[normalInverseWishartDistribution[{mu, lambda, psi, nu}], {x, sigma}];

normalInverseWishartDistribution /: LogLikelihood[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    {x_?VectorQ, sigma_?SquareMatrixQ}
] /; Dimensions[psi] === Dimensions[sigma] && Length[mu] === Length[x] === Length[psi] := Plus[
    LogLikelihood[MultinormalDistribution[mu, sigma/lambda], {x}], 
    LogLikelihood[InverseWishartMatrixDistribution[nu, psi], {sigma}]
];

normalInverseWishartDistribution /: LogLikelihood[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    pts : {{_?VectorQ, _?SquareMatrixQ}..}
] := Sum[
    LogLikelihood[normalInverseWishartDistribution[mu, lambda, psi, nu], pt],
    {pt, pts}
];

(* Default non-informative prior *)
updateDistributionParameters[{MultinormalDistribution[_Symbol, _Symbol], dim_Integer?Positive}] := 
    normalInverseWishartDistribution[
        ConstantArray[0, dim],
        1/100,
        IdentityMatrix[dim]/100,
        dim - 1 + 1/100
    ];

updateDistributionParameters[
    data_List?MatrixQ,
    dist_MultinormalDistribution
] := updateDistributionParameters[
    data,
    dist,
    updateDistributionParameters[{dist, Dimensions[data][[2]]}]
];

updateDistributionParameters[
    data_List?MatrixQ,
    MultinormalDistribution[_Symbol, _Symbol],
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
];

Options[posteriorMultivariateNormal] = {
    "Prior" -> {"Mu" -> 0, "Lambda" -> 1/100, "Psi" -> 1/100, "Nu" -> Automatic},
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
                Plus[
                    LogLikelihood[MultinormalDistribution[muTest, covTest], data],
                    LogLikelihood[normalInverseWishartDistribution[mu0, lambda0, psi0, nu0], {muTest, covTest}]
                ],
                LogLikelihood[normalInverseWishartDistribution[mu, lambda, psi, nu], {muTest, covTest}]
            ]
        ]
    |>
];

precisionMultinormalDistribution /: LogLikelihood[precisionMultinormalDistribution[mu_, lambda_], list : {__List}] :=
    Sum[
        LogLikelihood[precisionMultinormalDistribution[mu, lambda], x],
        {x, list}
    ];

precisionMultinormalDistribution /: LogLikelihood[precisionMultinormalDistribution[mu_, lambda_], x_List?VectorQ] :=
    (1/2) * Log[Det[lambda/ (2 * Pi)]] - With[{diff = x - mu}, (diff.lambda.diff)]/2;

linearModelDistribution /: MarginalDistribution[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    1
] /; Length[mu] === Length[lambda] := ParameterMixtureDistribution[
    MultinormalDistribution[mu, \[FormalV] * LinearSolve[lambda, IdentityMatrix[Length[lambda]]]],
    Distributed[\[FormalV], InverseGammaDistribution[alpha, beta]] 
];

linearModelDistribution /: MarginalDistribution[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    2
] /; Length[mu] === Length[lambda] := InverseGammaDistribution[alpha, beta];

linearModelDistribution /: RandomVariate[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    n_Integer?Positive
] := With[{
    inv = LinearSolve[lambda, IdentityMatrix[Length[lambda]]],
    samples = RandomVariate[InverseGammaDistribution[alpha, beta], n]
},
    Transpose @ {
        RandomVariate[MultinormalDistribution[mu, inv], n] * Sqrt[samples], (* == Table[RandomVariate[MultinormalDistribution[mu, var * inv], n], {var, samples}]*)
        samples
    }
];

linearModelDistribution /: PDF[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    {x_?VectorQ, var : Except[_List]}
] := Exp @ LogLikelihood[linearModelDistribution[mu, lambda, alpha, beta], {x, var}];

linearModelDistribution /: LogLikelihood[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    {x_?VectorQ, var : Except[_List]}
] /; Length[x] === Length[mu] := Plus[
    LogLikelihood[precisionMultinormalDistribution[mu, lambda/var], x],
    LogLikelihood[InverseGammaDistribution[alpha, beta], {var}]
];

linearModelDistribution /: LogLikelihood[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    pts : {{_?VectorQ,  Except[_List]}..}
] := Sum[
    LogLikelihood[linearModelDistribution[mu, lambda, alpha, beta], pt],
    {pt, pts}
];


updateDistributionParameters[{"LinearModel", basis_List, symbols_List}] :=
    linearModelDistribution[{"LinearModel", Length[basis]}];

(* General non-informative prior *)
updateDistributionParameters[{"LinearModel", dim_Integer?Positive}] :=
    linearModelDistribution[
        ConstantArray[0, dim],
        IdentityMatrix[dim]/200,
        1/200,
        1/200
    ];

updateDistributionParameters[
    data : {__Rule},
    {"LinearModel", basis_List, symbols_List},
    rest___
] := With[{
    inputs = Replace[
        data[[All, 1]],
        vec_List?VectorQ :> ArrayReshape[vec, {Length[vec], 1}]
    ],
    outputs = data[[All, 2]]
},
    updateDistributionParameters[
        inputs -> outputs,
        {"LinearModel", basis, symbols},
        rest
    ]
];

updateDistributionParameters[
    input_List?MatrixQ -> yvec_List?VectorQ,
    {"LinearModel", basis_List, symbols_List},
    rest___
] := updateDistributionParameters[
    DesignMatrix[
        Join[input, ArrayReshape[yvec, {Length[yvec], 1}], 2],
        basis,
        symbols,
        IncludeConstantBasis -> False
    ] -> yvec,
    "LinearModel",
    rest
];

updateDistributionParameters[
    designMatrix_List?MatrixQ -> yVec_List?VectorQ,
    "LinearModel"
] := updateDistributionParameters[
    designMatrix -> yVec,
    "LinearModel",
    updateDistributionParameters[{"LinearModel", Dimensions[designMatrix][[2]]}]
];

updateDistributionParameters[
    designMatrix_List?MatrixQ -> yVec_List?VectorQ,
    "LinearModel",
    linearModelDistribution[mu0_List?VectorQ, lambda0_List?SquareMatrixQ, a0_, b0_]
] /; Length[designMatrix] === Length[yVec] && Dimensions[designMatrix][[2]] === Length[mu0] === Length[lambda0] := Module[{
    designSq = Transpose[designMatrix] . designMatrix,
    mun,
    nDat = Length[yVec]
},
    mun = LinearSolve[designSq + lambda0, (lambda0 . mu0 + Transpose[designMatrix] . yVec)];
    linearModelDistribution[
        mun,
        designSq + lambda0,
        a0 + nDat/2,
        b0 + (yVec.yVec + mu0.lambda0.mu0 - mun.lambda0.mun)/2
    ]
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]