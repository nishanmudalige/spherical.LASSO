\name{spherical.design}
\alias{spherical.design}
\title{A function to create the appropriate design matrix for data over the hypersphere}
\description{A function which creates the appropriate design matrix for regression analysis. The design matrix returned from this can be used with the spherical LASSO or with Beran's regression estimator. 
    We use the general spherical harmonics as defined by Dai and Xu in "Approximation Theory and Harmonic Analysis on Spheres and Balls. This package works up to the second order spherical order q-vector. Requires data in p>=3 dimensions.}
\usage{
spherical.design(x)
}
\arguments{
  \item{x}{Data matrix. Should be in p>=3 dimensions.}
  \item {normalize.by.volume}{Logical argument. Whether to normalize by the volume of the hyper-sphere. If TRUE, then the value returned with be normalized by the volume element.}
}
\value{Design matrix after the spherical harmonics have been aplied, up to the second order q-vector.}
\references{[1]Dai, F. and Xu, Y. (2013), Approximation Theory and Harmonic Analysis on Spheres and Balls, Springer Science & Business Media.

[2] Beran, R.(1979), Exponential Models for Directional Data, Ann Statist 71162-1178.}
\author{Nishan Mudalige}
}
\examples{
## Requires simmd by Kent et. al.
## See Kent, J. T., Ganeiber A.M., Mardia, K.V. (2017), A New Unified Approach for the Simulation of a Wide Class of Directional Distributions, Journal of Computational and Graphical Statistics, 27:2, 291-301

## Number of simulations to run
# n.to.sim = 3000

## Generate data from a Fisher-Bingham with chosen parameters
# x.mfb = rFisherBingham(nsim = n.to.sim, mu = c(0, 0, 0, 0, 234),
#                       Aplus = c(101, 101, 101, -303, 0))
# x.mfb = as.matrix(x.mfb)

## Create design matrix
# x.d = gen.spherical.design(x.mfb, T)
}
