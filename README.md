# BayesianInference
Wolfram Language application for Bayesian inference and Gaussian process regression.

This is a package that implements the nested sampling algorithm in pretty much the same way as described by John Skilling in his 2006 paper "Nested Sampling for General Bayesian Computation" (Bayesian Analysis, 1, number 4, pp. 833 - 860; available at: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.117.5542&rep=rep1&type=pdf).

It also provides some functionality for Markov Chain Monte Carlo sampling (MCMC) based on built-in (but undocumented) functions in the ``Statistics`MCMC` `` context.

A new recently added function called `BayesianLinearRegression` provides the Bayesian alternative to Mathematica's `LinearModelFit`.

Finally, there is also some code that helps to construct neural networks for quasi-Bayesian regression as explained on the following pages:
* http://mlg.eng.cam.ac.uk/yarin/blog_3d801aa532c1ce.html
* http://blog.wolfram.com/2018/05/31/how-optimistic-do-you-want-to-be-bayesian-neural-network-regression-with-prediction-errors/


## Installation:
- Open your user base directory (e.g., evaluate `SystemOpen[$UserBaseDirectory]` in a notebook)
- Go into the Applications directory
- Drop the whole BayesianInference directory in the Applications directory (i.e., the folder structure should be `$UserBaseDirectory`/Applications/BayesianInference)
- Restart Mathematica

You can now load the package by evaluating:

    << BayesianInference`

Alternatively, you can just set the working directory of your notebook to the same directory as `example_code.nb` and load the package using the line above (see the initialisation cell in the notebook for an example).

## Using the package:

See the `example_code.nb` notebook for a general explanation of the code and several examples. Note that the package underwent significant changes since the previous release and most functionality is invoked in a different way than before.

## Update history

### Version 2.0
* 23 November 2018
    * The package has been overhauled significantly and now relies largely on the MCMC sampler hidden in the Statistics\`MCMC\` context. This means that this version may not be compatible with older versions of Mathematica, so please check out the `release1` tag of this package if you prefer/need the old code. I will probably continue to find small bugs to fix and improvements to make in the near future, so there will most likely be more updates to come.

* 24 November 2018
    * Add an example section that shows how to use nested sampling for time series regression with a `GeometricBrownianMotionProcess`.
    * Improve the numerical stability of the evidence computation.

* 25 November 2018
    * Expand the section on time series process regression. Now contains explanation of how to compile the loglikelihood function of a geometric Brownian motion process.

* 26 November 2018
    * Make sure that parallel runs in `parallelNestedSampling` always generate their own starting points.

* 28 November 2018
    * Add a new section to the example notebook that explains the goals of the package in broader terms. Also features an animated visualisation of the nested sampling algorithm. Check it out!
    * Add example of classification using logistic regression.

* 30 November 2018
    * Add an example of Bayesian logistic classification for the Fisher Iris data set.

* 18 December 2018
    * Add a new use case for `predictiveDistribution` where you can specify different keys in the 3rd argument to populate the output association with. This is useful when the inputs contain duplicates (such as can happen in the time series regression example in the last section) or when you need to undo a transformation you applied to the independent coordinates.
    * Some small updates to the example notebook.

* 12 July 2019
    * Add code for Bayesian linear regression. See the appropriate section in the example notebook.
    * Add code for (pseudo) Bayesian regression methods using neural networks. See the appropriate section in the example notebook.
