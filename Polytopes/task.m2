-*
Compute the Ehrhart series and Ehrhart delta-vector of a rational polytope
Compute the equivariant Ehrhart H* series of an orbit polytope
*-

needsPackage "Polyhedra"

P = convexHull transpose matrix "1,1,0,0;1,0,1,0;0,1,1,0;1,0,0,1;0,1,0,1;0,0,1,1"

vertices P

dim P
volume P

ehrhart P -- Ehrhart polynomial of P

Q = convexHull transpose matrix "0; 1/2"

vertices Q
dim Q

volume Q
ehrhart Q -- this doesn't make sense 


-- Is it possible to use Normaliz to compute the Ehrhart series of Q?
needsPackage "Normaliz"

R = QQ[t, x, Degrees => {1,0}]
L = {t, t^2*x} -- these correspond to 0 and 1/2 resp. of Q
(E1, E2) = ehrhartRing L
E1
peek E1.cache

end

-*
Todo:
0) Observe (in the source code of 'ehrhart') that it does not produce the 
   right (quasi)-polynomial for rational (non-lattice) polytopes

0.1) See the paper in this folder of the repo for definition of Ehrhart
     quasi-polynomial

0.2) What should the Ehrhart quasi-polynomia and Ehrhart series of Q be?


1) Check if any part of the Normaliz package can work with rational polytopes

1.1) Check if Normaliz itself can comute the Ehrhart series 


2) Make a function called ehrhartSeries:

2.1) If P is a lattice polytope, then use Normaliz to compute its Ehrhart series
     (see HNF-task for a special case that can be done fast)

2.2) If P is a rational polytope, then use the answer to part 1 to inform what
     you do next: either use Normaliz or find another way to compute the Ehrhart series


HNF-task:

> For Hermite-Normal-Form (HNF) simplices (see paper in repo), there is a very fast algorithm
  for computing the Ehrhart series / Ehrhart delta-vector 
  
  1) Make a function that checks whether a polytope is a HNF simplex  
  2) Implement the fast formula for the delta-vector
  3) Combine 1 & 2 in an implementation of Ehrhart series

*-
