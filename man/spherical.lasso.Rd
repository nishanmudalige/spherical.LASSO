\name{spherical.lasso}
\alias{spherical.lasso}
\title{A function to evaluate a variation of the LASSO as applied to data over the hypersphere}
\description{A function which applied the LASSO on data over the hypersphere. The von Mises Fisher Kernel from the `Directional` package is used to evaluate the estimated density for the LASSO.}
\usage{
spherical.lasso(x)
}
\arguments{
  \item{x.entered}{Data matrix. Should be in p>=3 dimensions.} 
  \item{q}{Maximum order of the q vectors. Should be either 1 or 2. Note that q=2 generates the design matrix for both q=1 and q=2.}
  \item{normalize.by.volume}{Logical argument. Whether to normalize by the volume of the hyper-sphere. If TRUE, then the value returned with be normalized by the volume element.}
  \item{intercept}{Logical argument. Whether the LASSO should include an intercept or not. If TRUE, then the model will include an intercept.}
  \item{extra.info}{Logical argument. Whether additional information should be returned. If TRUE, then object returned will be a list consisting of the model, the estimated values of the density for each data point and the design matrix.}
}
\value{
If `extra.info = TRUE`
\item{model}{The LASSO model.}
\item{y}{The estimated density evaluated using the von-Mises Fisher kernel density estimator.}
\item{x.design}{The design matrix.}

If `extra.info = FALSE`, only the model is returned.
}
\references{[1]Dai, F. and Xu, Y. (2013), Approximation Theory and Harmonic Analysis on Spheres and Balls, Springer Science & Business Media.

[2] Beran, R.(1979), Exponential Models for Directional Data, Ann Statist 71162-1178.}
\author{Nishan Mudalige}

\examples{
## Requires simmd by Kent et. al.
## See Kent, J. T., Ganeiber A.M., Mardia, K.V. (2017), A New Unified Approach for the Simulation of a Wide Class of Directional Distributions, Journal of Computational and Graphical Statistics, 27:2, 291-301

# set.seed(1)

# p = 4
# n = 100
# int.vec = c(1:100)
# kappa = 5

# mu = mu.vec(p)
# nu.mat = rand.nu.mat(p, int.vec, kappa)
# nu.mat.star = nu.mat/kappa

# x.mfb = rFisherBingham(nsim=n, mu=mu, Aplus=nu.mat, q=dimset(mu,nu.mat))
# x.mfb = as.data.frame(x.mfb)
# model.vmf = gen.spherical.lasso(x.mfb, 2, intercept=F,
#                                 normalize.by.volume = F, extra.info=T)

}
