----------------------------------
-- Plans for future development --
----------------------------------

-- check with the core developers of M2 about incorporating LattE
-- 1 of 2 things could happen:
-- >> if LattE is incorporated then we can use it instead of #latticePoints
--    LattE has some additional functionality, such as Ehrhart polynomials,
--    so we can interface with those too
--    This can be implemented as another 'Strategy' - i.e. the user can decide
--    which algorithm / implementation they wish to use. E.g., a use may want to
--    use a purely M2 strategy if they want to follow the steps of the computation
--
-- >> if LattE cannot be incorporated then we can search for it in the user's system
--    and implement the above suggestions except the default method is via M2
--


-- A rough to-do list --

-- check exported functions work with easy examples
-- that can be computed by hand. Add these as separate tests


-- implement a method for internalQuasiPolynomial that uses the following procedure:
-- 1) check the cache for a stored list of polynomials
-- 2) if there is no list, use the coefficients matrix to produce a list of polynomials and cache them
-- 3) take the input i modulo the period to obtain j, and return polynomial number j evaluated at i
-- the idea is to take advantage of M2's polynomial evaluation

-- decide what should be done if we try to create a quasi polynomial of period 1.
-- it's just a polynomial! So should we return a genuine polynomial or not?


-- if a quasi polynomial is made from a polytope, then store a reference to that polytope in the cache of
-- the quasi polynomial


-- cache the quasi-polynomial in the polyhedron and avoid recomputing the quasi-polynomial if it is already cached
-- note that the Polyhedron type is just a hashtable with a single entry: cache 


-- check the definition of hStart polynomial in literature and check whether the denominator of the Ehrhart series is:
-- (1 - t^(denominator P))^(dim P)  or  (1 - t^(period P))^(dim P)


-- simplify the names of functions: E.g. EhrhartQP -> ehrhart (overriding the one in Polyhedra)
-- or, if we don't want to override, then choose a name without abbreviations: e.g. ehrhartQuasiPolynomial
-- function names and variables should start with lower case
-- periodQP -> period (may need to change the key in the QuasiPolynomial type)


-- think about how a user might interact with the package and what would make life easier for them.
-- E.g. A user comes along with a polytope in mind: either they know the vertices or a half-space description
--      the user want to compute the Ehrhart quasi-polynomial, Ehrhart series, hStar poly, delta-vector (coefficients of hStar poly)


-- Whenever we perform a computation, e.g. computing the EhrhartQP, store the result in the cache
-- and before performing computations, check if we have already computed it by checking the cache
-- a useful piece of code is:
C = new CacheTable from {1 => "hi"}
C#?1 -- 1 is a key of the hash table
C#?2 -- but 2 is not


