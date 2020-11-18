# Created by Nishan Mudalige and Dr. Peter Kim
# Maintained by Nishan Mudalige. Email: nishan.mudalige.1@ulaval.ca
# Copyright Nishan Mudalige and Dr. Peter Kim, 2020

# This research us partially based upon work supported by a research grant 
# from Google Cloud.

# We use the general spherical harmonics as defined by Dai and Xu
# in "Approximation Theory and Harmonic Analysis on Spheres and Balls".

library(general.spherical)
library(orthopolynom)
library(pracma)
library(matrixcalc)
library(mefa)
library(glmnet)
library(Directional)
library(hypergeo)
library(matrixcalc)
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
spherical.design = function(x, normalize.by.volume = T){
  
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
spherical.lasso = function(x.entered, q, normalize.by.volume = T,
                               intercept=FALSE, extra.info=FALSE){
  
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
