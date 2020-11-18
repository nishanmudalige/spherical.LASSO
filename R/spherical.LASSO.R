# Created by Nishan Mudalige and Dr. Peter Kim
# Maintained by Nishan Mudalige. Email: nishan.mudalige.1@ulaval.ca
# Copyright Nishan Mudalige and Dr. Peter Kim, 2020

# This research us partially based upon work supported by a research grant 
# from Google Cloud.

# We use the general spherical harmonics as defined by Dai and Xu
# in "Approximation Theory and Harmonic Analysis on Spheres and Balls".

# library(general.spherical) Not on CRAN Yet
library(orthopolynom)
library(pracma)
library(matrixcalc)
library(mefa)
library(glmnet)
library(Directional)
library(hypergeo)
library(stringr)
library(assertr)
library(Matrix)


# Function which replicates a vector multiple times and returns a matrix
rep.row<-function(x,n){
  matrix(rep(x,each=n),nrow=n)
}


# Function which replicates a column multiple times and returns a matrix
rep.col<-function(x,n){
  matrix(rep(x,each=n), ncol=n, byrow=TRUE)
}



## DELETE LATER 

# The b function as defined by Theorem1.5.1. of Dai and Xu
b.q = function(q){
  p = length(q)
  ifelse(q[p-1] + q[p] > 0, 2, 1)
}


# The g function as defined by Theorem1.5.1. of Dai and Xu
g.x = function(x, q){
  p = length(q)
  q.p = q[p]
  q.p_1 = q[p-1]
  
  if(q.p == 0) {
    result = Re(( complex(real=x[2], imaginary=x[1]) )^q.p_1)
    return(Re(result))
  } else if(q.p == 1) {
    result = Im(( complex(real=x[2], imaginary=x[1]) )^q.p_1)
    return(Re(result))
  } else {
    return(NULL) 
  }
  
}


# The |q| function as defined by Theorem1.5.1. of Dai and Xu
q.norm = function(q, j){
  p_1 = length(q)-1
  return(sum(q[j:p_1]))
}


# The lambda_j function as defined by Theorem1.5.1. of Dai and Xu
lambda = function(q, j){
  p = length(q)
  q.norm(q, j+1) + (p-j-1)/2
}


# The Gegenbauer polynomial C^{lambda}_{n}(x)
gegenbauer = function(n, lambda, x){
  
  res = ( (orthopolynom::pochhammer(2*lambda, n))/factorial(n) ) * 
    ( hypergeo::hypergeo(tol=0.1, A=-n, B=n+(2*lambda), C=lambda+0.5, z=(1-x)/2) )
  
  return(Re(res))
}


# The h_{\alpha}^{2} function as defined by Theorem1.5.1. of Dai and Xu
h.q.sqr = function(q){
  p = length(q)
  bq = b.q(q)
  result = NULL
  
  for(j in 1:(p-2)){
    lambda.j = lambda(q,j)
    num = factorial(q[j]) * pochhammer( (p-j+1)/2 , q.norm(q, j+1) ) * ( q[j] + lambda.j )
    denom = pochhammer( (2*lambda.j), q[j] ) * pochhammer( (p-j)/2 , q.norm(q, j+1) ) * lambda.j
    
    result[j] = num/denom
  }
  
  return(bq* prod(unlist(result)) )  
  
}


# The volume of the hyper-sphere
# By default, the unit sphere is considered 
volume.hyper.sphere = function(p, r=1){
  volume = 2*pi^(p/2) / gamma(p/2) * (r^p)
  return(volume)
}


# The spherical harmonic Y_{\alpha}(x) as defined by Theorem1.5.1. of Dai and Xu
# Note the minor error in Theorem1.5.1. of Dai and Xu where 
# (h_{\alpha}^{2})^{-1} should be replaced with h_{\alpha}
y.q.x = function(x, q, normalize.by.volume = T){
  
  p = as.numeric(length(x))
  
  gx = g.x(x, q)
  h.q = sqrt(h.q.sqr(q))
  
  result = NULL
  
  for(j in 1:(p-2)){
    #j = 2
    x.ss = sum( ( x[1:(p-j+1)] )^2 )
    lambda.j = lambda(q,j)
    
    g.poly = NULL
    
    if(q[j] == 0){
      g.poly = 1  
    } else {
      g.poly = gegenbauer( n=q[j], lambda = lambda.j, x =  as.numeric(x[p-j+1]/sqrt(x.ss)) )
    }
    
    result[j] =   x.ss^(q[j]/2) * g.poly
    
    
  }
  
  if(isTRUE(normalize.by.volume)){
    
    rad = as.numeric(sum(x^2))
    
    volume = volume.hyper.sphere(p, rad)
    
    return( (1/sqrt(volume)) * h.q * gx * prod(unlist(result)) )
  } else{
    return( h.q * gx * prod(unlist(result)) )
  }
  
}

##


# Create all vectors of length "size" with with elements 0 or 1 such that the
# first (p-1) terms add up to variable the value "choose"
combinations1 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:1), size))
  d[rowSums(d) == choose,]
  
}


# Create all vectors of length "size" with with elements 0,1,2 such that the
# first (p-1) terms add up to variable the value "choose"
combinations2 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:2), size))
  d[rowSums(d) == choose,]
  
}


# Create all valid first order vectors of dimension p
create.q.1 = function(p){
  
  q1 = combinations1(p, 1)
  
  remove.rows = which( rowSums(q1[,1:p-1]) < 1)
  q1 = q1[-remove.rows,]
  
  colnames(q1) = NA
  
  add.rows = q1[which(q1[, p-1] != 0), ]
  add.rows[, p] = 1
  colnames(add.rows) = NA
  
  q1 = as.matrix(rbind(q1, add.rows), rownames.force = FALSE)
  colnames(q1) = NULL
  
  return(q1)
  
}


# Create all valid second order vectors of dimension p
create.q.2 = function(p){
  
  q12 = combinations2(p, 2)
  
  remove.rows = which( rowSums(q12[,1:p-1]) < 2)
  q12 = q12[-remove.rows,]
  
  colnames(q12) = NA
  
  add.rows = q12[which(q12[, p-1] != 0), ]
  add.rows[, p] = 1
  colnames(add.rows) = NA
  
  # q12 = matrix(as.matrix(rbind(q12, add.rows)), ncol=p)
  q12 = as.matrix(rbind(q12, add.rows), rownames.force = FALSE)
  colnames(q12) = NULL
  
  return(q12)
  
}




# Create the design matrix for the LASSO.
# Can also be used with Beran's regression estimator
spherical.design = function(x.entered, normalize.by.volume = T){
  
  p = ncol(x)
  n = nrow(x)
  
  q1 = create.q.1(p)
  q2 = create.q.2(p)
  
  m1 = nrow(q1)
  temp1 = matrix(0, n, m1)
  
  for(i in 1:n){
    for(j in 1:m1){
      temp1[i,j] = y.q.x(x[i,], q1[j,], normalize.by.volume)
    }
  }
  
  
  m2 = nrow(q2)
  temp2 = matrix(0, n, m2)
  
  for(i in 1:n){
    for(j in 1:m2){
      temp2[i,j] = y.q.x(x[i,], q2[j,], normalize.by.volume)
    }
  }
  
  
  out1 = cbind(temp1, temp2)
  
  q1.names = apply(q1 , 1 , paste , collapse = "" )
  q1.names = paste("q=", q1.names, sep="")
  
  q2.names = apply(q2 , 1 , paste , collapse = "" )
  q2.names = paste("q=", q2.names, sep="")
  
  colnames(out1) = c(q1.names, q2.names)
  
  return(out1)  
  
}



# Spherical LASSO
spherical.lasso = function(x.entered, q, normalize.by.volume = T, intercept=FALSE, extra.info=FALSE){
  
  q = q
  n = nrow(x.entered)
  x.design = spherical.design(x.entered, normalize.by.volume)
  
  x.design = x.design - colMeans(x.design)
  
  h = vmfkde.tune(x.design)["Optimal h"]
  f.hat.n = vmf.kde(x=x.entered, h=h, thumb="rot")$f
  
  f.hat.n[is.nan(f.hat.n)] = 1e-10
  
  f.hat.n[f.hat.n == Inf] = unique(sort(f.hat.n, decreasing = T))[2]
  f.hat.n[f.hat.n == -Inf] = unique(sort(f.hat.n, decreasing = F))[2]
  
  y = log(f.hat.n) - mean(log(f.hat.n))
  
  model = glmnet(x=x.design, y=y, intercept=intercept, standardize.response =T)
  
  if(extra.info == TRUE){
    return(list(model, y, x.design))
  } else {
    return(model)
  }
  
}
