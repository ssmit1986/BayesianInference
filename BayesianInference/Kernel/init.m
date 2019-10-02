(* Wolfram Language Init File *)

ClearAll[
    "BayesianUtilities`*", "BayesianUtilities`Private`*",
    "BayesianStatistics`*","BayesianStatistics`Private`*",
    "BayesianGaussianProcess`*", "BayesianGaussianProcess`Private`*",
    "BayesianVisualisations`*", "BayesianVisualisations`Private`*",
    "BayesianNeuralNetworks`*", "BayesianNeuralNetworks`Private`*",
    "BayesianConjugatePriors`*", "BayesianConjugatePriors`Private`*",
    "LaplaceApproximation`*", "LaplaceApproximation`Private`*"
];
Needs["GeneralUtilities`"];
Get["BayesianInference`BayesianUtilities`"];
Get["BayesianInference`BayesianStatistics`"];
Get["BayesianInference`BayesianGaussianProcess`"];
Get["BayesianInference`BayesianVisualisations`"];
Get["BayesianInference`BayesianNeuralNetworks`"];
Get["BayesianInference`ExponentialFamilyDefinitions`"];
Get["BayesianInference`BayesianConjugatePriors`"];
Get["BayesianInference`BayesianLinearRegression`"];
Get["BayesianInference`LaplaceApproximation`"];
