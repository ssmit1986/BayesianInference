# BayesianInference
Wolfram Language application for Bayesian inference and Gaussian process regression

This is a package that implements the nested sampling algorithm in pretty much the same way as described by John Skilling in his 2006 paper "Nested Sampling for General Bayesian Computation" (Bayesian Analysis, 1, number 4, pp. 833 - 860; available at http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.117.5542&rep=rep1&type=pdf)

## Installation:
- Open your user base directory (e.g., evaluate SystemOpen[$UserBaseDirectory] in a notebook)
- Go into the Applications directory
- Drop the whole BayesianInference directory in the Applications directory (i.e., the folder structure should be $UserBaseDirectory/Applications/BayesianInference)
- Restart Mathematica

You can now load the package by evaluating
<< BayesianInference`


## Using the package:

The main functions exposed to the user are nestedSampling and parallelNestedSampling (which uses similar syntax as nestedSampling). Several examples of usage of these functions are given in the notebook example_code.nb. Real documentation on these functions is to follow in future releases, but the main idea is that the user supplies 3 main ingredients to nestedSampling:

1: A log likelihood function (which is a function R^n -> R). The arguments to the log likelihood function are the parameters that the user wishes to infer. Multiple arguments have to be provided sequentially, so the expected syntax for evaluating the function is logLikelihood[param1, param2, param3, ...]. List syntax (such as logLikelihood[{param1, param2, param3, ...}]) will not work.

Note that the data has to be included in the log likelihood function. A simple way construct a log likelihood function for a standard Mathematica distribution and user data 'dat' is by using the function LogLikelihood:

dist = NormalDistribution
dat = RandomVariate[dist[0,1], 100];
logLikelihoodFunction = Function[{mu, sigma}, LogLikelihood[dist[mu, sigma], dat]];
(*
(* This also works *)
logLikelihoodFunction = Function[LogLikelihood[dist[##], dat]];
*)
logLikelihoodFunction[0, 1]
logLikelihoodFunction[1, 2]

Evaluation of the log likelihood function can be sped up by using Compile instead of Function.

2: A prior specification. There are two ways to define priors on the parameters that are to be estimated: by specifying a Mathematica distribution, or by using a special syntax that constructs an ignorance prior.

If a Mathematica distribution is used, the user has to define a distribution that has the same dimensionality as the number of parameters that are to be estimated. The function ProductDistribution can be used to combine priors on individual parameters into a prior on all parameters. 

Taking the above example, if one has a prior specification such as mu ~ UniformDistribution[{5, 10}], sigma ~ ExponentialDistribution[5], then the prior one should insert into nestedSampling is:

prior = ProductDistribution[UniformDistribution[{5, 10}], ExponentialDistribution[5]]

test the dimensionality of the prior to verify that it's a 2D distribution:

RandomVariate[prior]

Instead of creating their own prior distribution, the user can also give a list composed of the strings "LocationParameter" and "ScaleParameter" to construct an ignorance prior. This will result in a product distribution where the location parameters are uniform and the scale parameters follow a 1/x Jeffrey's prior. The bounds for these priors are taken from the 3rd argument to nestedSampling (see below). Only normalized priors can be used.

3: The parameter names and bounds specification. This should be a list of the form:

{
    {symbol1, lowerBound1, upperBound1},
    {symbol2, lowerBound2, upperBound2},
    ...
}

The bounds are only used if the user uses the "LocationParameter"/"ScaleParameter" syntax to specify the prior.


### Using parallelNestedSampling

parallelNestedSampling has the same syntax as nestedSampling, but it will not show a progress overview during evaluation. Parallelization is achieved by running the nested sampling on different cores and then combining the results afterwards in the way Skilling describes in his paper. This means that in order to make good use of the paralelization, the user has to tweak the number of living samples (through the option "SamplePoolSize") and the number of parallel runs (option "ParallelRuns"). After the parallel computation is done, the effective number of living samples will be multiplied by the number of parallel runs. The upshot of this is that the user can use a smaller "SamplePoolSize" per run (which leads to faster convergence) by doing parallel runs.

As a simple example: if the user wishes to have 100 living points and has 4 kernels available, then they can do 4 parallel runs with 25 living samples instead of 1 run with 100 living samples. 

