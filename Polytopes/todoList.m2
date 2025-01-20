----------------------------------
-- Plans for future development --
----------------------------------

-----------
-- LattE --
-----------
--
-- On a computer that can compile M2 from scratch:
-- 0) Check license for LattE
-- 1) Clone M2 repo,
-- 2) Try adding LattE to the libraries: For instruction on how to add new libraries see:
--	  https://github.com/Macaulay2/M2/tree/master/M2/libraries
-- 3) Compile Macaulay2 following:
--		https://github.com/Macaulay2/M2/wiki/Building-M2-from-source-using-CMake

--
--    if LattE is incorporated then we can use it instead of #latticePoints
--    LattE has some additional functionality, such as Ehrhart polynomials,
--    so we can interface with those too
--    This can be implemented as another 'Strategy' - i.e. the user can decide
--    which algorithm / implementation they wish to use. E.g., a use may want to
--    use a purely M2 strategy if they want to follow the steps of the computation

--------------
-- Normaliz --
--------------
--
-- Investigate whether Normaliz package can be used for computing lattice points
-- There is way to use Normaliz to write down the list of lattice points of a lattice polytope:
-- https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Normaliz/html/___The_splattice_sppoints_cm_sp__Ehrhart_spseries_spand_spthe_spsupport_sphyperplanes_spof_span_spintegral_sppolytope..html
-- see also:
-- https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Normaliz/html/_normaliz_lp__Matrix_cm__String_rp.html
--
-- This function nomaliz(M, "polytope") seems to fail if the entries of the matrix are not integers
-- >> Is it possible to modify the Normaliz code to make it work for rational matrices?
-- (i.e., check the source code of normaliz)
--
-- The Normaliz manual explains that it can be used to compute the Ehrhart Series
-- for rational polytopes:
-- 0) check that the version of Normaliz in M2 has this functionality
-- 1) write a function that interfaces with Normaliz that can pass in the vertices of rational polytopes
-- 2) return the output from Normaliz to the user
-- (potentially 1 and 2 can be accessed using the Normaliz M2 package)
--


-- check the code for interalQuasiPolynomial -> how does it evaluate the polynomials?
-- There might be a problem with the indexing. It seems to give an error with the quasi polynomial:

P = convexHull matrix "0, 1"
QP = EhrhartQP P
QP 0
displayQP QP -- looks nice :)

--
-- check exported functions work with easy examples
-- that can be computed by hand. Add these as separate tests
-- can also add these to the documentation


-- hStar output formatting could be done in a similar to
-- see: help (hilbertSeries, Ideal)
-- Then it might make sense to call the function "ehrhartSeries"
-- documentation for ehrhartSeries
-- is it possible to display a factorised expression for the denominator?
--

-- internalQuasiPolynomial is a function that evaluates the quasiPolynomial at a certain integer value
-- -- current the mmethod uses a lot of matrix multiplication to evaluate
-- instead we can construct a list of polynomials (one for each value up to the period) that we can evaluate instead
-- once we have these polynomials we can cache them inside the quasiPolynomial object for future use.
--
-- implement a method for internalQuasiPolynomial that uses the following procedure:
-- 1) check the cache for a stored list of polynomials
-- 2) if there is no list, use the coefficients matrix to produce a list of polynomials and cache them
-- 3) take the input i modulo the period to obtain j, and return polynomial number j evaluated at i
-- the idea is to take advantage of M2's polynomial evaluation



-- decide what should be done if we try to create a quasi polynomial of period 1.
-- it's just a polynomial! So should we return a genuine polynomial or not?
--


-- review the behaviour of the following code that was added:
--
-- 1) if a quasi polynomial is made from a polytope, then store a reference to that polytope in the cache of
--    the quasi polynomial (done)
-- 2) cache the quasi-polynomial in the polyhedron and avoid recomputing the quasi-polynomial if it is already cached
--    note that the Polyhedron type is just a hashtable with a single entry: cache (done)



-- check the definition of hStart polynomial in literature and check whether the denominator of the Ehrhart series is:
-- (1 - t^(denominator P))^(dim P)  or  (1 - t^(period P))^(dim P)


-- simplify the names of functions: E.g. EhrhartQP -> ehrhart (overriding the one in Polyhedra)
-- or, if we don't want to override, then choose a name without abbreviations: e.g. ehrhartQuasiPolynomial
-- function names and variables should start with lower case
-- periodQP -> period (may need to change the key in the QuasiPolynomial type)



-- think about how a user might interact with the package and what would make life easier for them.
-- E.g. A user comes along with a polytope in mind: either they know the vertices or a half-space description
--      the user want to compute the Ehrhart quasi-polynomial, Ehrhart series, hStar poly, delta-vector (coefficients of hStar poly)


-- decide if we want to include the code from the equivariant Ehrhart file
--
