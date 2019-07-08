BeginPackage["BayesianConjugatePriors`", {"BayesianUtilities`", "GeneralUtilities`"}]

conjugatePriorModel::usage = "posterior = conjugatePriorModel[data, model, conjugate prior] updates the distribution of the parameters of a model";
normalInverseGammaDistribution;
normalInverseWishartDistribution;
linearModelDistribution;
linearModel;
linearModelPredictiveDistribution;
multiLinearModel;
multiLinearModelDistribution;
multiLinearModelPredictiveDistribution;
makeDesignMatrix;
normalInverseWishartPredictiveDistribution;

Begin["`Private`"]

integerOrListIntegerPattern = Alternatives[_Integer?Positive, {_Integer?Positive}];

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
] := StudentTDistribution[mu, Sqrt[beta/(nu * lambda)], 2 nu];
(* == ParameterMixtureDistribution[
    NormalDistribution[mu, Sqrt[\[FormalV]] / Sqrt[lambda]],
    Distributed[\[FormalV], InverseGammaDistribution[nu, beta]]
]*)

normalInverseGammaDistribution /: MarginalDistribution[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    2
] := InverseGammaDistribution[nu, beta];

normalInverseGammaDistribution /: RandomVariate[
    normalInverseGammaDistribution[mu_, lambda_, beta_, nu_],
    n : integerOrListIntegerPattern : 1
] := Module[{
    varSamples = RandomVariate[InverseGammaDistribution[nu, beta], n],
    muSamples
},
    muSamples = RandomVariate[NormalDistribution[], n] * Sqrt[varSamples / lambda] + mu; (* == Table[RandomVariate[NormalDistribution[mu, Sqrt[var / lambda]]], {var, varSamples}]*)
    Transpose[{muSamples, varSamples}]
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

conjugatePriorModel[{} | {{}} | (_ -> {}), _, prior_] := prior; (* Cannot update without data *)

conjugatePriorModel[ (* Update a previously computed model with new data by using the posterior as a new prior *)
    data : _List | _Rule,
    model : KeyValuePattern[{"Model" -> _, "Posterior" -> _, "LogEvidence" -> _, "Prior" -> _}]?AssociationQ
] := Module[{
    updatedModel
},
    updatedModel = conjugatePriorModel[data, model["Model"], model["Posterior"]];
    Scan[
        Function[updatedModel[#] = model[#]],
        {"Prior", "PriorPredictiveDistribution"}
    ];
    updatedModel["LogEvidence"] += model["LogEvidence"];
    
    updatedModel
];

(* Default non-informative prior *)
conjugatePriorModel[NormalDistribution[_Symbol, _Symbol]] := normalInverseGammaDistribution[0, 1/100, 1/200, 1/200];

conjugatePriorModel[
    data_List?VectorQ,
    dist_NormalDistribution
] := conjugatePriorModel[
    data,
    dist,
    conjugatePriorModel[dist]
];

conjugatePriorModel[
    data_List?VectorQ,
    model : NormalDistribution[_Symbol, _Symbol],
    prior : normalInverseGammaDistribution[mu0_, lambda0_, beta0_, nu0_]
] := Module[{
    mean = Mean[data],
    var,
    mu, lambda, beta, nu,
    nDat = Length[data],
    post,
    logEvidence,
    predictiveDist
},
    var = If[ nDat === 1, 1, Variance[data]];
    post = normalInverseGammaDistribution[
        mu = Divide[
            lambda0 * mu0 + nDat * mean,
            lambda0 + nDat
        ],
        lambda = lambda0 + nDat,
        beta = beta0 + Divide[(nDat-1) * var, 2] + Divide[lambda0 * nDat, 2 * (lambda0 + nDat)] * (mean - mu0)^2,
        nu = nu0 + nDat/2
    ];
    logEvidence = If[ TrueQ[lambda0 > 0 && nu0 > 0&& beta0 > 0],
        Simplify @ With[{
            muTest = mean,
            varTest = var
        },
            Plus[
                LogLikelihood[NormalDistribution[muTest, Sqrt[varTest]], data],
                LogLikelihood[prior, {muTest, varTest}] - LogLikelihood[post, {muTest, varTest}]
            ]
        ],
        Undefined
    ];
    predictiveDist = Function[{m, lamb, bet, n},
        StudentTDistribution[m, Sqrt[bet * (lamb + 1)/(lamb * n)], 2 * n]
    ]; (* ==
        ParameterMixtureDistribution[
            ParameterMixtureDistribution[
                NormalDistribution[\[FormalU], Sqrt[\[FormalV]]],
                Distributed[\[FormalU], NormalDistribution[mu, Sqrt[\[FormalV]/lambda]]]
            ],
            Distributed[\[FormalV], varDist]
        ]
    *)
    <|
        "Model" -> model,
        "Prior" -> prior,
        "Posterior" -> post,
        "LogEvidence" -> logEvidence,
        "PriorPredictiveDistribution" -> predictiveDist @@ prior,
        "PosteriorPredictiveDistribution" -> predictiveDist @@ post
    |>
];

normalInverseWishartDistribution /: MarginalDistribution[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    1
] := With[{
    dim = Length[mu]
},
    MultivariateTDistribution[mu, psi / (lambda * (nu - dim + 1)), nu - dim + 1];
];

normalInverseWishartDistribution /: MarginalDistribution[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    2
] := InverseWishartMatrixDistribution[nu, psi];

normalInverseWishartDistribution /: RandomVariate[
    dist_normalInverseWishartDistribution,
    n : integerOrListIntegerPattern : 1
] := Flatten[RandomVariate[dist, Flatten @ {n, 1}], 1]

normalInverseWishartDistribution /: RandomVariate[
    normalInverseWishartDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    {n_Integer?Positive, m_Integer?Positive}
] /; Length[mu] === Length[psi] := With[{
    samples = RandomVariate[InverseWishartMatrixDistribution[nu, psi], n]
},
    Table[
        Transpose[{
            RandomVariate[MultinormalDistribution[mu, cov/lambda], m],
            ConstantArray[cov, m]
        }],
        {cov, samples}
    ]
];

normalInverseWishartPredictiveDistribution /: RandomVariate[
    dist_normalInverseWishartPredictiveDistribution,
    n : integerOrListIntegerPattern : 1
] := Flatten[RandomVariate[dist, Flatten @ {n, 1, 1}], 2];

normalInverseWishartPredictiveDistribution /: RandomVariate[
    dist_normalInverseWishartPredictiveDistribution,
    {k_Integer?Positive, l_Integer?Positive}
] := Flatten[RandomVariate[dist, {k, l, 1}], {{1}, {2, 3}}];

normalInverseWishartPredictiveDistribution /: RandomVariate[
    normalInverseWishartPredictiveDistribution[mu_?VectorQ, lambda_, psi_?SquareMatrixQ, nu_],
    {k_Integer?Positive, l_Integer?Positive, m_Integer?Positive}
] /; Length[mu] === Length[psi] := Module[{
    distSamples = RandomVariate[normalInverseWishartDistribution[mu, lambda, psi, nu], {k, l}]
},
    Table[
        RandomVariate[MultinormalDistribution[samp[[1]], samp[[2]]], m],
        {sampOuter, distSamples},
        {samp, sampOuter}
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
conjugatePriorModel[{MultinormalDistribution[_Symbol, _Symbol], dim_Integer?Positive}] := 
    normalInverseWishartDistribution[
        ConstantArray[0, dim],
        1/100,
        IdentityMatrix[dim]/100,
        dim - 1 + 1/100
    ];

conjugatePriorModel[
    data_List?MatrixQ,
    dist_MultinormalDistribution
] := conjugatePriorModel[
    data,
    dist,
    conjugatePriorModel[{dist, Dimensions[data][[2]]}]
];

conjugatePriorModel[
    data_List?MatrixQ,
    model : MultinormalDistribution[_Symbol, _Symbol],
    prior : normalInverseWishartDistribution[mu0_, lambda0_, psi0_, nu0_]
] := Module[{
    mean = Mean[data],
    cov,
    dim, nDat,
    meanDiff,
    post,
    mun, lambdan, psin, nun,
    logEvidence,
    predictiveDist
},
    {nDat, dim} = Dimensions[data];
    cov = If[ nDat === 1, IdentityMatrix[dim], Covariance[data]];
    meanDiff = mean - mu0;
    post = normalInverseWishartDistribution[
        mun = Divide[
            lambda0 * mu0 + nDat * mean,
            lambda0 + nDat
        ],
        lambdan = lambda0 + nDat,
        psin = psi0 + (nDat - 1) * cov + Divide[lambda0 * nDat, lambda0 + nDat] * (List /@ meanDiff) . {meanDiff},
        nun = nu0 + nDat
    ];
    logEvidence = Simplify @ With[{
        muTest = mean,
        covTest = cov
    },
        Replace[Except[_?NumericQ]-> Undefined] @ Quiet @ Plus[
            LogLikelihood[MultinormalDistribution[muTest, covTest], data],
            LogLikelihood[prior, {muTest, covTest}] - LogLikelihood[post, {muTest, covTest}]
        ]
    ];
    predictiveDist = Function[{m, lamb, ps, n},
        MultivariateTDistribution[m, (lamb + 1) * ps/(lamb * (n - dim + 1)), n - dim + 1]; (* == normalInverseWishartPredictiveDistribution[mun, lambdan, psin, nun] *)
    ];
    <|
        "Model" -> model,
        "Prior" -> prior,
        "Posterior" -> post,
        "LogEvidence" -> logEvidence,
        "PriorPredictiveDistribution" -> predictiveDist @@ prior,
        "PosteriorPredictiveDistribution" -> predictiveDist @@ post
    |>
];


precisionMultinormalDistribution /: LogLikelihood[precisionMultinormalDistribution[mu_, lambda_], list : {__List}] :=
    Sum[
        LogLikelihood[precisionMultinormalDistribution[mu, lambda], x],
        {x, list}
    ];

precisionMultinormalDistribution /: LogLikelihood[precisionMultinormalDistribution[mu_, lambda_], x_List?VectorQ] :=
    (1/2) * Log[Det[lambda/ (2 * Pi)]] - With[{diff = x - mu}, (diff.lambda.diff)]/2;


(*Bayesian linear regression https://en.wikipedia.org/wiki/Bayesian_linear_regression*)
linearModelDistribution /: MarginalDistribution[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    1
] /; Length[mu] === Length[lambda] := MultivariateTDistribution[mu, 
    beta/alpha * LinearSolve[lambda, IdentityMatrix[Length[lambda]]],
    2 * alpha
]; (* == ParameterMixtureDistribution[
    MultinormalDistribution[mu, \[FormalV] * LinearSolve[lambda, IdentityMatrix[Length[lambda]]]],
    Distributed[\[FormalV], InverseGammaDistribution[alpha, beta]] 
]*)

linearModelDistribution /: MarginalDistribution[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    2
] /; Length[mu] === Length[lambda] := InverseGammaDistribution[alpha, beta];

linearModelDistribution /: RandomVariate[
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, alpha_, beta_],
    n : integerOrListIntegerPattern : 1
] := With[{
    inv = LinearSolve[lambda, IdentityMatrix[Length[lambda]]],
    samples = RandomVariate[InverseGammaDistribution[alpha, beta], n]
},
    Transpose @ {
        RandomVariate[MultinormalDistribution[mu, inv], n] * Sqrt[samples], (* == Table[RandomVariate[MultinormalDistribution[mu, var * inv]], {var, samples}]*)
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

makeDesignMatrix[lm_, input : Except[{__Rule} | _Rule | _List]] := makeDesignMatrix[lm, {{input}}];
makeDesignMatrix[lm_, input : Except[{__Rule}, _List?VectorQ]] := makeDesignMatrix[lm, List /@ input];

makeDesignMatrix[lm_, input_List?MatrixQ] := makeDesignMatrix[
    lm,
    input -> ConstantArray[Missing[], Length[input]]
];

makeDesignMatrix[lm_, data : {__Rule}] := With[{
    inputs = Replace[
        data[[All, 1]],
        vec_List?VectorQ :> ArrayReshape[vec, {Length[vec], 1}]
    ]
},
    makeDesignMatrix[lm, inputs -> data[[All, 2]]]
];

makeDesignMatrix[
    (linearModel | multiLinearModel)[basis_List, symbols : {__Symbol}, ___],
    input_List?MatrixQ -> yvec_List?(VectorQ[#] || MatrixQ[#]&)
] /; Length[input] === Length[yvec] := <|
    "DesignMatrix" -> DesignMatrix[
        Join[input, ConstantArray[0, {Length[yvec], 1}], 2],
        basis,
        symbols,
        IncludeConstantBasis -> False
    ],
    "Output" -> yvec
|>;

designMatrixPattern = PatternTest[
    KeyValuePattern[{
        "DesignMatrix" -> _List?MatrixQ,
        "Output" -> _List?(VectorQ[#] || MatrixQ[#]&) 
    }],
    AssociationQ[#] && Length[#["DesignMatrix"]] === Length[#["Output"]]&
];

linearModelPredictiveDistribution[lm_linearModel, input_List?MatrixQ] :=
    linearModelPredictiveDistribution[lm, makeDesignMatrix[lm, input]];

linearModelPredictiveDistribution[
    linearModel[basis_List, symbols : {__Symbol}, {coefficientVector_List?VectorQ, var_}],
    designMatrix : designMatrixPattern
] /; Length[coefficientVector] === Dimensions[designMatrix["DesignMatrix"]][[2]] := With[{
    stdev = Sqrt[var]
},
    ProductDistribution @@ Map[
        NormalDistribution[#, stdev]&,
        designMatrix["DesignMatrix"] . coefficientVector
    ]
];

linearModelPredictiveDistribution[
    lm_linearModel,
    dist_linearModelDistribution,
    input_List?MatrixQ
] := linearModelPredictiveDistribution[lm, dist] /@ input;

linearModelPredictiveDistribution[
    linearModel[basis_List, symbols : {__Symbol}, ___],
    linearModelDistribution[mu_List?VectorQ, lambda_List?SquareMatrixQ, a_, b_]
] /; Length[basis] === Length[mu] === Length[lambda]:= With[{
    (*meanVec = Array[\[FormalM], Length[mu]],*)
    invLambda = LinearSolve[Replace[lambda, mat_?numericMatrixQ :> N[mat]]],
    dMat = First @ makeDesignMatrix[
        linearModel[basis, symbols],
        {symbols}
    ]["DesignMatrix"]
},
    ReleaseHold @ expressionToFunction[
        StudentTDistribution[dMat . mu, Sqrt[(b/a) * (dMat . Hold[invLambda[dMat]] + 1)], 2 * a],
        (* == ParameterMixtureDistribution[
            ParameterMixtureDistribution[
                NormalDistribution[
                    dMat . meanVec,
                    Sqrt[\[FormalV]]
                ],
                Distributed[
                    meanVec,
                    MultinormalDistribution[mu, \[FormalV] * invLambda]
                ]
            ],
            Distributed[\[FormalV], InverseGammaDistribution[a, b]]
        ]*)
        symbols
    ]
];

linearModel /: LogLikelihood[
    linearModel[basis_List, symbols : {__Symbol}, {coefficientVector_List?VectorQ, var_}],
    data : (_List | _Rule)
] := LogLikelihood[
    linearModel[basis, symbols, {coefficientVector, var}],
    makeDesignMatrix[linearModel[basis, symbols, {coefficientVector, var}], data]
];

linearModel /: LogLikelihood[
    linearModel[basis_List, symbols : {__Symbol}, {coefficientVector_List?VectorQ, var_}],
    designMatrix : designMatrixPattern
] := LogLikelihood[
    linearModelPredictiveDistribution[linearModel[basis, symbols, {coefficientVector, var}], designMatrix],
    {designMatrix["Output"]}
];

(* General non-informative prior *)
conjugatePriorModel[linearModel[basis_List, symbols : {__Symbol}, ___]] := With[{
    dim = Length[basis]
},
    linearModelDistribution[
        ConstantArray[0, dim],
        IdentityMatrix[dim]/200,
        1/200,
        1/200
    ]
];

conjugatePriorModel[
    data : ((_List?MatrixQ -> _List?VectorQ) | {__Rule}),
    linearModel[basis_List, symbols : {__Symbol}, ___],
    rest___
] := conjugatePriorModel[
    makeDesignMatrix[linearModel[basis, symbols], data],
    linearModel[basis, symbols],
    rest
];

conjugatePriorModel[
    data : ((_List?MatrixQ -> _List?MatrixQ) | {__Rule}),
    multiLinearModel[basis_List, symbols : {__Symbol}, ___],
    rest___
] := conjugatePriorModel[
    makeDesignMatrix[multiLinearModel[basis, symbols], data],
    multiLinearModel[basis, symbols],
    rest
];

conjugatePriorModel[
    assoc : designMatrixPattern,
    (lm : (linearModel|multiLinearModel))[basis_List, symbols : {__Symbol}, ___]
] := conjugatePriorModel[
    assoc,
    linearModel[basis, symbols],
    conjugatePriorModel[lm[basis, symbols]]
];

conjugatePriorModel[
    assoc : designMatrixPattern,
    linearModel[basis_List, symbols : {__Symbol}, ___],
    prior : linearModelDistribution[mu0_List?VectorQ, lambda0_List?SquareMatrixQ, a0_, b0_]
] := Module[{
    model = linearModel[basis, symbols],
    designMatrix = assoc["DesignMatrix"],
    yVec = assoc["Output"],
    mun, lambdan, an, bn,
    designSq,
    designTrans,
    nDat,
    post,
    rv,
    logEvidence,
    predictiveDist
},
    (
        designTrans = Transpose[designMatrix];
        designSq = designTrans . designMatrix;
        nDat = Length[yVec];
        mun = LinearSolve[designSq + lambda0, (lambda0 . mu0 + designTrans . yVec)];
        post = linearModelDistribution[
            mun,
            lambdan = designSq + lambda0,
            an = a0 + nDat/2,
            bn = b0 + (yVec.yVec + mu0.lambda0.mu0 - mun.lambdan.mun)/2
        ];
        rv = First @ RandomVariate[post];
        logEvidence = Simplify @ Plus[
            LogLikelihood[linearModel[basis, symbols, rv], assoc],
            LogLikelihood[prior, {rv}]- LogLikelihood[post, {rv}]
        ];
        predictiveDist = Function[linearModelPredictiveDistribution[model, #]];
        <|
            "Model" -> model,
            "Prior" -> prior,
            "Posterior" -> post,
            "LogEvidence" -> logEvidence,
            "PriorPredictiveDistribution" -> predictiveDist @ prior,
            "PosteriorPredictiveDistribution" -> predictiveDist @ post
        |>
    ) /; Length[designMatrix] === Length[yVec] && Dimensions[designMatrix][[2]] === Length[mu0] === Length[lambda0]
];

(* Multivariate regression https://en.wikipedia.org/wiki/Bayesian_multivariate_linear_regression*)
multiLinearModelDistribution /: MarginalDistribution[
    multiLinearModelDistribution[mu_List?MatrixQ, lambda_List?SquareMatrixQ, psi_?SquareMatrixQ, nu_],
    1
] /; Dimensions[mu] === {Length[lambda], Length[psi]} := MatrixTDistribution[
    mu,
    LinearSolve[lambda, IdentityMatrix[Length[lambda]]],
    psi,
    nu - Length[mu] + 1
];

multiLinearModelDistribution /: MarginalDistribution[
    multiLinearModelDistribution[mu_List?MatrixQ, lambda_List?SquareMatrixQ, psi_?SquareMatrixQ, nu_],
    2
] /; Dimensions[mu] === {Length[lambda], Length[psi]} := InverseWishartMatrixDistribution[nu, psi];

(*
Hypothesis:
If B \[Distributed] MatrixNormalDistribution[bMat, rowMat, colMat], and x a constant vector, then

x . B \[Distributed] MultinormalDistribution[x . bMat, colMat * (x . rowMat . x)]
*)
linearModelPredictiveDistribution[
    lm_multiLinearModel,
    dist_multiLinearModelDistribution,
    input_List?MatrixQ
] := linearModelPredictiveDistribution[lm, dist] /@ input;

linearModelPredictiveDistribution[
    multiLinearModel[basis_List, symbols : {__Symbol}, ___],
    multiLinearModelDistribution[mu_List?MatrixQ, lambda_List?SquareMatrixQ, psi_?SquareMatrixQ, nu_]
] /; Dimensions[mu] === {Length[lambda], Length[psi]} && Length[basis] === Length[mu] := With[{
    invLambda = LinearSolve[Replace[lambda, mat_?numericMatrixQ :> N[mat]]],
    dVec = First @ makeDesignMatrix[
        linearModel[basis, symbols],
        {symbols}
    ]["DesignMatrix"],
    dim = nu - Length[mu] + 1
},
    (* TODO: verify *)
    ReleaseHold @ expressionToFunction[
        MultivariateTDistribution[dVec . mu, (psi/dim) * (dVec . Hold[invLambda[dVec]] + 1), dim],
        symbols
    ]
];


linearModelPredictiveDistribution[lm_multiLinearModel, input_List?MatrixQ] :=
    linearModelPredictiveDistribution[lm, makeDesignMatrix[lm, input]];

linearModelPredictiveDistribution[
    multiLinearModel[basis_List, symbols : {__Symbol}, {coefficientMatrix_List?MatrixQ, cov_List?SquareMatrixQ}],
    designMatrix : designMatrixPattern
] /; And[
    Length[coefficientMatrix] === Dimensions[designMatrix["DesignMatrix"]][[2]],
    Dimensions[coefficientMatrix][[2]] === Length[cov]
] := (
    ProductDistribution @@ Map[
        MultinormalDistribution[#, cov]&,
        designMatrix["DesignMatrix"] . coefficientMatrix
    ]
);

conjugatePriorModel[multiLinearModel[basis_List, symbols : {__Symbol}, dimOut_Integer, ___]] := With[{
    dimIn = Length[basis]
},
    multiLinearModelDistribution[
        ConstantArray[0, {dimIn, dimOut}], (* B on wiki*)
        IdentityMatrix[dimIn]/100,
        IdentityMatrix[dimOut]/100, (* V on wiki*)
        1/100
    ]
];

conjugatePriorModel[
    assoc : designMatrixPattern,
    multiLinearModel[basis_List, symbols : {__Symbol}, ___]
] /; Length[Dimensions[assoc["Output"]]] === 2 := conjugatePriorModel[
    assoc,
    multiLinearModel[basis, symbols],
    conjugatePriorModel[multiLinearModel[basis, symbols, Dimensions[assoc["Output"]][[2]]]] (* TODO: does not work yet *)
];

conjugatePriorModel[
    assoc : designMatrixPattern,
    multiLinearModel[basis_List, symbols : {__Symbol}, ___],
    prior : multiLinearModelDistribution[mu0_List?MatrixQ, lambda0_List?SquareMatrixQ, psi0_?SquareMatrixQ, nu0_]
] /; Length[Dimensions[assoc["Output"]]] === 2 := Module[{
    model,
    designMatrix = assoc["DesignMatrix"],
    yMat = assoc["Output"],
    mun, lambdan, nun, psin,
    designSq,
    designTrans,
    nDat,
    nOut,
    post,
    rv,
    logEvidence,
    predictiveDist
},
    (
        designTrans = Transpose[designMatrix];
        designSq = designTrans . designMatrix;
        {nDat, nOut} = Dimensions[yMat];
        model = multiLinearModel[basis, symbols, nOut];
        mun = LinearSolve[designSq + lambda0, (lambda0 . mu0 + designTrans . yMat)];
        post = multiLinearModelDistribution[
            mun,
            lambdan = designSq + lambda0,
            psin = With[{
                residuals = yMat - designMatrix . mun,
                muUpdate = mun - mu0
            },
                psi0 + Transpose[residuals].residuals + Transpose[muUpdate].lambda0.muUpdate
            ],
            nun = nu0 + nDat
        ]
        
        (* TODO 
        rv = First @ RandomVariate[post];
        logEvidence = Plus[
            LogLikelihood[linearModel[basis, symbols, rv], assoc],
            LogLikelihood[prior, {rv}]- LogLikelihood[post, {rv}]
        ];
        predictiveDist = multiLinearModelPredictiveDistribution[model, post];
        <|
            "Model" -> model,
            "Prior" -> prior,
            "Posterior" -> post,
            "LogEvidence" -> logEvidence,
            "PosteriorPredictiveDistribution" -> predictiveDist
        |>*)
    ) /; And[
        Length[designMatrix] === Length[yMat],
        Dimensions[designMatrix][[2]] === Length[mu0] === Length[lambda0],
        Dimensions[yMat][[2]] === Dimensions[mu0][[2]]
    ]
];

End[]

EndPackage[(* "BayesianConjugatePriors`" *)]