-*
given a matrix A of integers
return the list of minimal generating sets of the toric ideal of A


*-


needsPackage "FourTiTwo"

A = matrix {{1,1,1,1}, {0,1,2,5}}

toricMarkov A -- this is a minimal generating setx
toricGraver A -- this is the Graver basis of A

-- As a concrete ideal of a polynomial ring
R = QQ[x_1 .. x_4]
IA = toricMarkov(A, R)

viewHelp FourTiTwo

end 

-*
Todo:
1) check if there is a function in 4ti2 that we can use
   e.g. does 4ti2 have a function for Universal Markov Basis?

2) If not, then check the paper in this folder of the repo
   Section 2 of that paper constructs a graph that encodes
   all the different minimal generating sets of I_A

*-
