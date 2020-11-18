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


rep.row<-function(x,n){
  matrix(rep(x,each=n),nrow=n)
}

rep.col<-function(x,n){
  matrix(rep(x,each=n), ncol=n, byrow=TRUE)
}




b.q = function(q){
  p = length(q)
  ifelse(q[p-1] + q[p] > 0, 2, 1)
  
}



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



q.norm = function(q, j){
  p_1 = length(q)-1
  return(sum(q[j:p_1]))
}



lambda = function(q, j){
  p = length(q)
  q.norm(q, j+1) + (p-j-1)/2
}


gegenbauer = function(n, lambda, x){
  
  res = ( (orthopolynom::pochhammer(2*lambda, n))/factorial(n) ) * 
    ( hypergeo::hypergeo(A=-n, B=n+(2*lambda), C=lambda+0.5, z=(1-x)/2) )
  
  return(Re(res))
}


# # gegenbauer.old
# gegenbauer = function(n, lambda, x){
# 
#   if(n == 0){
#     result = 1
#     return(result)
#   } else if(n == 1){
#     result = 2*lambda*x
#     return(result)
#   } else if(n == 2){
#     result = -lambda + 2*lambda*(1 + lambda)*x^2
#     return(result)
#   } else {
#     warning("This function only supports up to second order terms")
#     return()
#   }
# 
# }


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


volume.hyper.sphere = function(p, r=1){
  # volume = ( pi^(p/2) / gamma(p/2 + 1) )*(r^p)
  volume = 2*pi^(p/2) / gamma(p/2) * (r^p)
  return(volume)
}




y.q.x = function(x, q, normalize.by.volume = T){
  
  p = as.numeric(length(x))
  
  gx = g.x(x, q)
  h.q = sqrt(h.q.sqr(q))
  
  result = NULL
  
  for(j in 1:(p-2)){
    
    x.ss = sum( ( x[1:(p-j+1)] )^2 )
    lambda.j = lambda(q,j)
    
    result[j] =   x.ss^(q[j]/2) * gegenbauer(n=q[j], lambda = lambda.j, x =  as.numeric(x[p-j+1]/sqrt(x.ss)) )
  }
  
  if(isTRUE(normalize.by.volume)){
    
    rad = as.numeric(sum(x^2))
    
    volume = volume.hyper.sphere(p, rad)
    
    return( (1/sqrt(volume)) * h.q * gx * prod(unlist(result)) )
  } else{
    return( h.q * gx * prod(unlist(result)) )
  }
  
}







combinations.1 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:1), size))
  d[rowSums(d) == choose,]
  
}



# Create q-vectors

########################################


combinations1 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:1), size))
  d[rowSums(d) == choose,]
  
}


combinations2 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:2), size))
  d[rowSums(d) == choose,]
  
}



combinations3 = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:3), size))
  d[rowSums(d) == choose,]
  
}


########################################


# Check first order
create.q.1 = function(p){
  
  q1 = combinations1(p, 1)
  
  remove.rows = which( rowSums(q1[,1:p-1]) < 1)
  q1 = q1[-remove.rows,]
  
  colnames(q1) = NA
  
  add.rows = q1[which(q1[, p-1] != 0), ]
  add.rows[, p] = 1
  colnames(add.rows) = NA
  
  # q1 = matrix(as.matrix(rbind(q1, add.rows)), ncol=p)
  q1 = as.matrix(rbind(q1, add.rows), rownames.force = FALSE)
  colnames(q1) = NULL
  
  return(q1)
  
}



# Create Second Order
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




# Create Third Order
create.q.3 = function(p){
  
  q12 = combinations3(p, 3)
  
  remove.rows = which( rowSums(q12[,1:p-1]) < 3)
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


####################################


spherical.design1 = function(x, normalize.by.volume = T){
  
  x = as.matrix(x)
  
  p = ncol(x)
  n = nrow(x)
  
  q1 = create.q.1(p)
  
  m1 = nrow(q1)
  temp1 = matrix(0, n, m1)
  
  for(i in 1:n){
    for(j in 1:m1){
      temp1[i,j] = y.q.x(x[i,], q1[j,], normalize.by.volume)
    }
  }
  
  
  out1 = cbind(temp1)
  
  q1.names = apply(q1 , 1 , paste , collapse = "" )
  q1.names = paste("q=", q1.names, sep="")
  
  colnames(out1) = c(q1.names)
  
  return(out1)  
  
}



spherical.design2 = function(x, normalize.by.volume = T){
  
  p = ncol(x)
  n = nrow(x)
  
  # x = as.matrix(x, nrow=x, ncol=p)
  
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





# General
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
  
  # Generate ys for glmnet
  y = log(f.hat.n) - mean(log(f.hat.n))
  
  model = glmnet(x=x.design, y=y, intercept=intercept, standardize.response =T)
  
  if(extra.info == TRUE){
    return(list(model, y, x.design))
  } else {
    return(model)
  }
  
}









num.param = function(p){
  out = NULL
  for(i in 1:p){
    out = c(out, -i:i)
  }
  return(length(out))
}





largest.digit = function(n){
  largest = 0
  while (n > 0) {
    r = n %% 10
    if (largest < r) {
      largest = r
    }
    n = n %/% 10
  }
  return(largest)
}




determine.order = function(x){
  names.x = names(x)
  names.x = gsub("q=","",names.x)
  
  num.x = as.numeric(names.x)
  order = max(sapply(as.list(num.x), largest.digit))
  
  return(order)
}




b.vector = function(betas, normalize.by.volume = T){
  
  p = determine.order(betas)
  
  names.x = names(betas)
  names.x = gsub("q=","",names.x)
  
  dim = max(nchar(names.x))
  
  num.x = as.numeric(names.x)
  names(betas) = num.x
  
  q.all = as.matrix(combinations.order(dim ,p))
  
  q.1 = q.all[which(rowSums(q.all[,1:(ncol(q.all)-1)]) == 1), ]
  
  q.1 = as.numeric(col_concat(q.1))
  
  b = NULL
  current.index = NULL
  
  name.vec = NULL
  
  for(i in 1:dim){
    
    if(i == 1){
      current.index = which(as.numeric(names(betas)) == "11")
    } else {
      current.index = which(as.numeric(names(betas)) == q.1[dim-i+1] )
    }
    
    b[i] = sqrt(dim)*betas[current.index]
    
    name.vec[i] = names.x[current.index]
  }
  names(b) = name.vec
  
  if(isTRUE(normalize.by.volume)){
    
    volume = volume.hyper.sphere(dim)
    
    # return( sqrt(dim*(dim+2)/2*volume) * b )
    return( sqrt(dim/volume) * b )
    
  } else {
    return(b)
  }
  
  
}






combinations.n = function(size, choose) {
  
  d = do.call("expand.grid", rep(list(0:choose), size))
  
  # Remove which last are (...0,1)
  d = d[which(!( d[,(size-1)] == 0 & d[,size] == 1)), ]
  
  
  # Remove which last element not 0 or 1
  d = d[d[, size] %in%  c(0,1), ]
  
  d[rowSums(d[1:(size-1)]) == choose,]
  
}



# combinations.n(3, 1) 


combinations.order = function(size, q){
  vec = 1:q
  
  out = NULL
  for(i in 1:length(vec)){
    out = rbind(out, combinations.n(size, vec[i])  )
  }
  
  out  
}










B.matrix = function(betas, normalize.by.volume = T){
  
  p = determine.order(betas)
  
  names.x = names(betas)
  names.x = gsub("q=","",names.x)
  
  dim = max(nchar(names.x))
  
  names.df = strsplit(names.x, "")
  names.df = do.call("rbind", names.df)
  
  B = matrix(0, nrow = dim, ncol = dim)
  
  # diag
  # diag
  # diag
  for(i in 1:dim){
    
    # B[1,1] and B[1,2]
    if(i==1 | i ==2){
      first.index = which(names.df[,dim-1] == "2" & names.df[,dim] == "0")
      
      sum.vec = NULL
      for(k in 2:(dim-1)){
        
        current.index = which(names.df[,dim-k] == "2" & names.df[,dim] == "0")
        coeff = 1/(sqrt(k)*sqrt(k+1))
        
        sum.vec[k-1] = coeff*betas[current.index]
      }
      
      if(i==1){
        B[1,1] = -1/sqrt(2)*betas[first.index] - sum(sum.vec)
      }
      else{
        B[2,2] = 1/sqrt(2)*betas[first.index] - sum(sum.vec)
      }
    }
    
    # B[3,3] ... B[p-1,p-1]
    if(i>=3 & i<=(dim-1)){
      first.index = which(names.df[,dim-i] == "2" & names.df[,dim] == "0")
      
      sum.vec = NULL
      for(k in i:(dim-1)){
        
        current.index = which(names.df[,dim-k] == "2" & names.df[,dim] == "0")
        coeff = 1/(sqrt(k)*sqrt(k+1))
        
        sum.vec[k-(i-1)] = coeff*betas[current.index]
      }
      B[i,i] = (i-1)/(sqrt(i)*sqrt(i-1)) * betas[first.index] - sum(sum.vec)
    }
    
    # B[p,p]
    if(i == dim){
      index = which(names.df[,1] == "2" & names.df[,dim] == "0")
      
      B[dim,dim] = sqrt((dim-1)) * betas[index]
    }
    
  }
  
  
  # off-diag
  # off-diag
  # off-diag
  for(i in 1:dim){
    for(j in 1:dim){
      
      if(i == j){
        next()
      }
      
      if(i==1 & j==2){
        index = which(names.df[,dim-1] == "2" & names.df[,dim] == "1")
        
        B[i,j] = 1/sqrt(2) * betas[index]
      }
      
      if(i == 1 & j >= 3 & j <= dim){
        index = which(names.df[,dim-j+1] == "1" & names.df[,dim-1] == "1" & names.df[,dim] == "1")
        
        B[i,j] = 1/sqrt(2) * betas[index]
      }
      
      if(i == 2 & j >= 3 & j <= dim){
        index = which(names.df[,dim-j+1] == "1" & names.df[,dim-1] == "1" & names.df[,dim] == "0")
        
        B[i,j] = 1/sqrt(2) * betas[index]
      }
      
      if(i >= 3 & i < j & j <= dim){
        index = which(names.df[,dim-i+1] == "1" & names.df[,dim-j+1] == "1" & names.df[,dim] == "0")
        
        B[i,j] = 1/sqrt(2) * betas[index]
      }
      
    }
  }
  
  
  common.coeff = (sqrt(dim) * sqrt(dim+2))/sqrt(2)
  B = common.coeff*B
  
  B = forceSymmetric(B)
  
  if(isTRUE(normalize.by.volume)){
    
    rad = 1
    volume = volume.hyper.sphere(p, rad)
    
    B = (1/volume^2) * B
    
  } 
  
  return(B)
  
}



l.decomp = function(x, normalize.by.volume){
  
  b = b.vector(x, normalize.by.volume)
  B = B.matrix(x, normalize.by.volume)
  
  return(list(b,B))
}









b.gamma = function(x, kappa){
  
  dim = ncol(x)
  e1 = c(1, rep(0, dim-1))
  gamma.mat = diag(dim)
  mu = kappa*e1
  
  kappa = Norm(mu, p=2)
  
  return(kappa * e1 %*% gamma.mat)
  
}


gamma.mat = diag(6)
mu = c(1,0,0,0,0,0)
nu.mat = diag(c(1,2,3,4,5,6)) %*% gamma.mat

kappa = 12

b.gamma(nu.mat, kappa)


# x = gamma.mat

B.gamma = function(A){
  
  dim = nrow(A)
  
  out.B = matrix(0, dim, dim)
  
  for(i in 2:(dim-1)){
    
    ek = rep(0, dim)
    ek[i] = 1
    
    out.B[i, i] = ek %*% A[, i]
    
  }
  
  out.B[dim, dim] = -sum(diag((out.B)))
  
  
  out.B[1,1] = 0
  
  return(out.B)
  
}

B.gamma(nu.mat)

diag(B.gamma(nu.mat))
sum(diag(B.gamma(nu.mat)))


# c(1,0,0,0) %*% t(c(1,0,0,0)) +
# c(0,1,0,0) %*% t(c(0,1,0,0)) +
# c(0,0,1,0) %*% t(c(0,0,1,0)) +
# c(0,0,0,1) %*% t(c(0,0,0,1))





kent.decomp = function(nu.mat, kappa){
  
  b = b.gamma(nu.mat, kappa)
  B = B.gamma(nu.mat)
  
  return(list(b,B))
}

# nu.mat = diag(c(1,2,3,4,5,6)) %*% gamma.mat
# kappa = 12
# 
# 
# kent.decomp(nu.mat, kappa)

# l.decomp(betas)

# Norm(l.decomp(betas)[[1]] - kent.decomp(nu.mat, kappa)[[1]], p = 2)

# norm(l.decomp(betas)[[2]] - kent.decomp(nu.mat, kappa)[[2]], type = "F")

# frobenius.norm(l.decomp(betas)[[2]] - kent.decomp(nu.mat, kappa)[[2]])




mse = function(nu.mat, betas, normalize.by.volume){
  
  k = nu.mat[1,1]
  
  Norm(l.decomp(betas, normalize.by.volume)[[1]] - kent.decomp(nu.mat, k)[[1]] , p = 2) +
    norm(l.decomp(betas, normalize.by.volume)[[2]] - kent.decomp(nu.mat, k)[[2]], type = "F")
  
}


# mse(nu.mat, betas)
