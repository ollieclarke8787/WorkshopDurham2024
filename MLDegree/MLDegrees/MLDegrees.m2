needsPackage "FourTiTwo"
needsPackage "NumericalAlgebraicGeometry"
needsPackage "Polyhedra"

-- MLIdeal is the ideal of solutions for critical points of the log likelihood function
-- on the "parameter side"
-- i.e. (t_i) coordinates of the torus, (p_i) coordinates of the toric variety
MLParamIdeal = method(
    Options => {
	minRandomValue => 10,
	maxRandomValue => 99
	}
    )

MLParamIdeal(Matrix, List, List) := opts -> (A, w, u) -> (
    n := numColumns A;
    d := numRows A;
    assert(n == #w);
    assert(n == #u);
    t := symbol t;
    R := QQ[for i from 1 to d list t_i];
    g := -1 + sum for i from 0 to n-1 list w_i * product for j from 0 to d-1 list R_j^(A_(j,i));
    M := A * transpose matrix {u} | transpose matrix {for j from 0 to d-1 list R_j * diff(R_j, g)};
    minors(2, M) + ideal g
    )

-- random u
MLParamIdeal(Matrix, List) := opts -> (A, w) -> (
    n := numColumns A;
    u := for i from 1 to n list random(opts.minRandomValue, opts.maxRandomValue);
    MLParamIdeal(A, w, u)
    )

complexSolutions = method()
complexSolutions(Ideal) := I -> (
    R := ring I;
    S := CC[gens R];
    RtoS := map(S, R, gens S);
    polys := first entries RtoS mingens I;
    solveSystem polys
    )



--------
-- Twitsted toric variety
twistedToricIdeal = method()

twistedToricIdeal (Matrix, List, Ring) := (A, w, R) -> (
    n := numColumns A;
    T := toricMarkov(A, R);
    ideal for g in first entries mingens T list (
	-- these generators should all be PURE BINOMIALS
	exps := exponents g;
	if #exps != 2 then error "non-binomial generator of toric ideal";
	c0 := product for i from 0 to n-1 list (w_i)^((exps_1)_i);
	c1 := product for i from 0 to n-1 list (w_i)^((exps_0)_i);
	c0 * R_(exps_0) - c1 * R_(exps_1)
	)	
    )

-- if no ring is supplied then make one
twistedToricIdeal (Matrix, List) := (A, w) -> (
    n := numColumns A;
    if #w != n then error("-- w does not have " | toString n | " entries");
    p := symbol p;
    R := QQ[for i from 1 to n list p_i];
    T := toricMarkov(A, R);
    ideal matrix(R, {
	    for g in first entries mingens T list (
		-- these generators should all be PURE BINOMIALS
		exps := exponents g;
		if #exps != 2 then error "non-binomial generator of toric ideal";
		c0 := product for i from 0 to n-1 list (w_i)^((exps_1)_i);
		c1 := product for i from 0 to n-1 list (w_i)^((exps_0)_i);
		c0 * R_(exps_0) - c1 * R_(exps_1)
		)
	    }
	)	
    )


-------
-- Implicit version ideal

MLImpIdeal = method(
    Options => {}
    )

MLImpIdeal(Matrix, List, List) := opts -> (A, w, u) -> (
    n := numColumns A;
    d := numRows A;
    assert(n == #w);
    assert(n == #u);
    p := symbol p;
    R := QQ[for i from 1 to n list p_i];
    T := toricMarkov(A, R);
    TTwist := ideal for g in first entries mingens T list (
	-- these generators should all be PURE BINOMIALS
	exps := exponents g;
	if #exps != 2 then error "non-binomial generator of toric ideal";
	c0 := product for i from 0 to n-1 list (w_i)^((exps_1)_i);
	c1 := product for i from 0 to n-1 list (w_i)^((exps_0)_i);
	c0 * R_(exps_0) - c1 * R_(exps_1)
	);
    jac := jacobian TTwist;
    codimT := codim TTwist;
    M := transpose matrix {
	for i from 0 to n-1 list u_i * product for j from 0 to n-1 list if i != j then R_j else continue,
	for i from 0 to n-1 list 1
	} | jac;
    -- dimension of projective variety is (dim T) - 1
    -- note that dim T is the affine dimension  
    -- so co-dimension is (n-1) - (dim T - 1) = codim T
    J := minors(codimT + 2, M) + TTwist + ideal(-1 + sum for i from 0 to n-1 list R_i);
    saturate(J, product for i from 0 to n-1 list R_i)
    )

-- random u
MLImpIdeal(Matrix, List) := opts -> (A, w) -> (
    n := numColumns A;
    u := for i from 1 to n list random(opts.minRandomValue, opts.maxRandomValue);
    MLImpIdeal(A, w, u)
    )

-- the monomial map given by a matrix
-- the resulting object is a function that can be applied to lists of CC


-- Map of Tori
-- intended to be evaluated on a list of CC-points
torusMap = method()
torusMap (Matrix, List) := (A, w) -> (
    n := numColumns A;
    d := numRows A;
    if #w != n then error ("expected twist to have same number of entries as columns of matrix");
    f := L -> ( -- expect a list of CC of length d and return the image under the map
	if #L != d then error("expected a list or sequence of length " | toString d);
	for i from 0 to n-1 list (
	    w_i * product for j from 0 to d-1 list L_j^(A_(j,i))
	    )
	);
    monomialMap := method();
    monomialMap List := L -> (
	if #L == 0 then error("empty argument");
	if class L_0 === Point then (
	    for P in L list point {f coordinates P}
	    )
	else (
	    f L
	    )
	);
    monomialMap Point := P -> (
	point f coordinates P
	);
    monomialMap Matrix := M -> ( -- apply to the rows of M
	matrix for row in entries M list f row
        );
    monomialMap
    )

-- if no twisting list is supplied then use {1 .. 1}
torusMap Matrix := A -> (
    w := matrix {toList(numColumns A) : 1};
    torusMap(A, w)
    )


-- A-discriminant
-- compute the defining equations of the variety of scalars
-- then eliminate the \theta (t) variables to obtain
-- the constraints on the weight variables w_i

-- The Strategy determines the following:
-- If Strategy => "Variables" then we introduce s_i variables such that t_i^-1 = s_i and we eliminate all s_i's and t_i's
-- If Stratgey => "Saturation" then we only have t_i variables to eliminate but we saturate the ideal with the product of t_i's 

ADiscriminant = method(
    Options => {
	AmbientRing => null,
	Indices => null,
	Strategy => "Saturation" -- "Variables" or "Saturation"
	}
    )

ADiscriminant Matrix := opts -> A -> (
    n := numColumns A;
    d := numRows A;
    t := symbol t;
    s := symbol s;
    w := symbol w;
    local R;
    local g;
    local I;
    local W;
    local R';
    local m;
    -- ## Commented out code is for adding in variables v_i that are inverse to w_i ... this seems like overkill ##
    -- v := symbol v;
    -- R := QQ[t_1 .. t_d, s_1 .. s_d, v_1 .. v_n, w_1 .. w_n, MonomialOrder => Eliminate(2*d)];
    -- g := sum for i from 0 to n-1 list R_(2*d + n+ i) * product for j from 0 to d-1 list R_j^(A_(j,i));
    -- I := ideal({g} | (for i from 0 to d-1 list diff(R_i, g)) | (for i from 0 to d-1 list R_i * R_(d+i) - 1) | (for i from 0 to n-1 list R_(2*d + i) * R_(2*d+n+i) - 1));
    if opts.Strategy == "Variables" then (
	R = QQ[t_1 .. t_d, s_1 .. s_d, w_1 .. w_n, MonomialOrder => Eliminate(2*d)];
	g = sum for i from 0 to n-1 list R_(2*d + i) * product for j from 0 to d-1 list R_j^(A_(j,i));
    	I = ideal({g} | (for i from 0 to d-1 list diff(R_i, g)) | (for i from 0 to d-1 list R_i * R_(d+i) - 1));
    	-*
    	-- Instead of introducing all these new variables, try saturating
    	--  
    	R := QQ[t_1 .. t_d, w_1 .. w_n, MonomialOrder => Eliminate(d)];
    	g := sum for i from 0 to n-1 list R_(d + i) * product for j from 0 to d-1 list R_j^(A_(j,i));
    	I := ideal({g} | (for i from 0 to d-1 list diff(R_i, g)));
    	I := saturate(I, product for i from 0 to d-1 list R_i)
    	*-
    	-- eliminate t_1 .. t_d, s_1 .. s_d
    	W = ideal selectInSubring(1, gens gb I); -- generator is the principal A-determinant
    	-- R':= QQ[v_1 .. v_n, w_1 .. w_n, MonomialOrder => Eliminate(n)];
    	-- m := map(R', R, toList(2*d : 0_(R')) | gens R');
    	-- J := m saturate(W, product for i from 0 to n-1 list R_(2*d+i));
    	-- W' := ideal selectInSubring(1, gens gb J);
    	-- R'' := if opts.AmbientRing === null then QQ[w_1 .. w_n] else opts.AmbientRing;
    	-- m' := map(R'', R', toList(n : 0_(R'')) | if opts.AmbientRing === null then gens R'' else (gens R'')_(opts.Indices)); 
    	-- m' W'
    	R' = if opts.AmbientRing === null then QQ[w_1 .. w_n] else opts.AmbientRing;
    	m = map(R', R, toList(2*d : 0_(R')) | if opts.AmbientRing === null then gens R' else (gens R')_(opts.Indices)); 
    	m saturate(W, product for i from 0 to n-1 list R_(2*d+i))
    	)
    else if opts.Strategy == "Saturation" then (
	R = QQ[t_1 .. t_d, w_1 .. w_n, MonomialOrder => Eliminate(d)];
	g = sum for i from 0 to n-1 list R_(d + i) * product for j from 0 to d-1 list R_j^(A_(j,i));
    	I = ideal({g} | (for i from 0 to d-1 list diff(R_i, g)));
	I = saturate(I, product for i from 0 to d list R_i);
	W = ideal selectInSubring(1, gens gb I); -- generator is the principal A-determinant
    	R' = if opts.AmbientRing === null then QQ[w_1 .. w_n] else opts.AmbientRing;
    	m = map(R', R, toList(d : 0_(R')) | if opts.AmbientRing === null then gens R' else (gens R')_(opts.Indices)); 
    	m saturate(W, product for i from 0 to n-1 list R_(d+i))
	-- m W -- without saturation at the final step (potentially a different answer)
	)
    )


-- compute ML degree using linear equations
toricMLDegree = method(
    Options => {
	minRandomValue => 10,
	maxRandomValue => 99
	}
    )

toricMLDegree(Matrix, List, List) := opts -> (A, w, u) -> (
    assert(#w == numColumns A);
    assert(#u == numColumns A);
    T := twistedToricIdeal(A, w);
    R := ring T;
    varMat := matrix {gens R};
    linearEquations :=  A * transpose varMat - A * transpose matrix {u};
    degree(T + ideal linearEquations)
    )

toricMLDegree(Matrix, List) := opts -> (A, w) -> (
    assert(#w == numColumns A);
    u := for i from 1 to numColumns A list random(opts.minRandomValue, opts.maxRandomValue);
    T := twistedToricIdeal(A, w);
    R := ring T;
    varMat := matrix {gens R};
    linearEquations :=  A * transpose varMat - A * transpose matrix {u};
    degree(T + ideal linearEquations)
    )



-- A-determinant from polytope
-- returns a list of factors coming from the faces of the convex hull of A
-- assume that A is the set of lattice points of a polytope
-- returns the list of A-discriminants i.e. we check that the ADiscriminant ideal has codim 1 

-- > Strategy : "Variables" or "Saturation"
--   -- Variables  - introduces variables for \theta_i^-1 
--   -- Saturation - avoids introducing new variables by saturating wrt product of \theta_i's 
--
-- > FillLatticePoints : true or false
--   -- true  - replaces the matrix A with the lattice points of the convex hull of the columns of supplied matrix
--   -- false - assumes that columns of A are the lattice points 

-- Notes:
-- polyhedral computations may be slow for large polytopes but the real bottle-neck is in the computation of the ADiscriminant
ADeterminant = method(
    Options => {
	Strategy => "Saturation", -- "Variables" or "Saturation"
	FillLatticePoints => false, -- Boolean
	Verbose => false -- print out the A-discriminants for each face
	}
    )

ADeterminant Matrix := opts -> A -> (
    P := convexHull A;
    -- we use the following matrix:
    L := if opts.FillLatticePoints then fold(latticePoints P, (a,b) -> a | b) else A;
    V := sub(vertices P, ZZ);
    d := dim P;
    w := symbol w;
    R := QQ[w_1 .. w_(numColumns L)];
    if opts.Verbose then (
	print "-- Points matrix:";
	print L;
	);
    flatten for i from 0 to d-1 list for f in faces(i, P) list (
	verts := fold(apply(f_0, x -> V_{x}), (a,b) -> a | b);
	face := convexHull verts;
	facePointsIndices := for i from 0 to numColumns L -1 list (if contains(face, L_{i}) then i else continue);
	I := ADiscriminant(L_facePointsIndices, AmbientRing => R, Indices => facePointsIndices, Strategy => opts.Strategy);
	if opts.Verbose then (
	    print "";
	    print ("-- face: " | toString facePointsIndices);
	    print L_facePointsIndices;
	    print "-- ADiscriminant:";
	    print I;
	    );
	if codim I == 1 then first first entries gens I else continue
	)
    )





end --
restart
load "MLDegrees.m2"

A = matrix {{1, 1, 1, 1, 1, 1}, {0, 1, 2, 0, 1, 0}, {0, 0, 0, 1, 1, 2}}
ADiscriminant(A, Strategy => "Variables")
ADiscriminant(A, Strategy => "Saturation")
ADeterminant A

-- different w's giving degrees 4,3,2,1 respectively
degree MLParamIdeal(A, {1,1,1,1,1,1})
degree MLParamIdeal(A, {1,2,1,1,2,2})
degree MLParamIdeal(A, {1,2,1,1,2,1})
degree MLParamIdeal(A, {1,2,1,2,2,1})

-- get complex solutions:
-- Observation - some of these solutions are duplicated!

I = MLParamIdeal(A, {1,1,1,1,1,1})
netList complexSolutions I

I = MLParamIdeal(A, {1,2,1,2,2,1})
netList complexSolutions I

I = MLParamIdeal(A, {1,2,1,1,2,2})
netList complexSolutions I

I = MLParamIdeal(A, {1,2,1,1,2,1})
netList complexSolutions I

-----------

A = matrix {{1, 1, 1, 1, 1, 1}, {0, 1, 2, 0, 1, 0}, {0, 0, 0, 1, 1, 2}}
w = {1,1,1,1,1,1}
u = {1,2,3,4,5,6}
I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I
J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J
phi = torusMap(A, w)
netList phi complexSolutions I


nw = {1,2,1,2,2,1}
u = {1,2,3,4,5,6}
I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I
J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J
phi = torusMap(A, w)
netList phi complexSolutions I

-------------------

A = matrix {
    {1, 1, 1, 1},
    {0, 1, 0, 1},
    {0, 0, 1, 1}
    }
T = toricMarkov(A, QQ[(p := symbol p; for i from 1 to numColumns A list p_i)])
(ideal singularLocus T) : product for i from 0 to numgens ring T - 1 list (ring T)_i
degree T

w = {2,5,11,19}
u = {2,5,3,6}
I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I
J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J
phi = torusMap(A, w)
netList phi complexSolutions I

w = {1,1,1,1}
u = {2,5,3,6}
I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I
J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J
phi = torusMap(A, w)
netList phi complexSolutions I


-- unpacking the implicit ideal computation 
n = numColumns A
d = numRows A
p = symbol p
R = QQ[for i from 1 to n list p_i]
T = toricMarkov(A, R)
jac = jacobian T
codimI = codim T
M = transpose matrix {
    for i from 0 to n-1 list u_i * product for j from 0 to n-1 list if i != j then R_j else continue,
    for i from 0 to n-1 list 1
    } | jac
M = transpose matrix {for i from 0 to n-1 list u_i} | (diagonalMatrix for i from 0 to n-1 list R_i) * (transpose matrix {for i from 0 to n-1 list 1} | jac)
tempJ = minors(codimI + 2, M) + T + ideal(-1 + sum for i from 0 to n-1 list R_i)
J = saturate(tempJ, product for i from 0 to n-1 list R_i)

-- unpacking the parametrised ideal computation
n = numColumns A
d = numRows A
t = symbol t
R = QQ[for i from 1 to d list t_i]
g = -1 + sum for i from 0 to n-1 list w_i * product for j from 0 to d-1 list R_j^(A_(j,i))
M = A * transpose matrix {u} | transpose matrix {for j from 0 to d-1 list R_j * diff(R_j, g)}
I = minors(2, M) + ideal g

mingens ideal singularLocus T



------------------------
restart
load "MLDegrees.m2"

-- Singular toric variety example
A = matrix {
    {1,1,1,1,1},
    {0,1,0,1,2},
    {0,0,1,1,2}
    }

ADeterminant A

R = QQ[for i from 1 to numColumns A list p_i]
T = toricMarkov(A, R)
T' = T : product for i from 0 to numgens R -1 list R_i
netList primaryDecomposition ideal singularLocus T

w = {1,1,1,1,2}
TTwist := ideal for g in first entries mingens T list (
    -- these generators should all be PURE BINOMIALS
    exps := exponents g;
    c0 := product for i from 0 to numColumns A -1 list (w_i)^((exps_1)_i);
    c1 := product for i from 0 to numColumns A -1 list (w_i)^((exps_0)_i);
    c0 * R_(exps_0) - c1 * R_(exps_1)
    )
netList primaryDecomposition ideal singularLocus TTwist

u = for i from 1 to numColumns A list random(10,99)

I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I

J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J

phi = torusMap(A, w)
netList phi complexSolutions I


----------------
A = matrix {
    {1,1,1},
    {0,1,2}
    }

-*
A = matrix {
    {1,1,1},
    {2,1,0},
    {0,1,2}
    }
*-

w = {1,1,1}
u = {1,2,3}
R = QQ[for i from 1 to numColumns A list p_i]
T = toricMarkov(A, R)
I = MLParamIdeal(A, w, u)
degree I
netList complexSolutions I
J = MLImpIdeal(A, w, u)
degree J
netList complexSolutions J
phi = torusMap(A, w)
netList phi complexSolutions I


-- finding the A-discriminat
t = symbol t
w = symbol w
R = QQ[t_1, t_2, s_1, s_2, w_1, w_2, w_3, MonomialOrder => Eliminate(4)]

n = numColumns A
d = numRows A
f = sum for i from 1 to n list w_i * product for j from 1 to d list t_j^(A_(j-1,i-1))
I = ideal {
    f,
    diff(t_1, f),
    diff(t_2, f),
    t_1*s_1 - 1,
    t_2*s_2 - 1
    }
J = ideal(t_1*t_2, w_1*w_2*w_3)
I == saturate(I, J)
I == radical I
-- eliminate t_1 and t_2

selectInSubring(1, gens gb I)    

-----------

A = matrix {{1, 1, 1, 1, 1, 1}, {0, 1, 2, 0, 1, 0}, {0, 0, 0, 1, 1, 2}}

n = numColumns A
d = numRows A
t = symbol t
w = symbol w
R = QQ[t_1 .. t_d, s_1 .. s_d, w_1 .. w_n, MonomialOrder => Eliminate(2*d)]
describe R
f = sum for i from 1 to n list w_i * product for j from 1 to d list t_j^(A_(j-1,i-1))
I = ideal({f} | (for i from 1 to d list diff(t_i, f)) | (for i from 1 to d list t_i * s_i - 1))
-- eliminate t_1 .. t_d
gens gb I
W = ideal selectInSubring(1, gens gb I) -- generator is the principal A-determinant
saturate(W, product for i from 1 to n list w_i)

-------
A = matrix {
    {1,1,1,1},
    {0,1,2,3}
    }

ADiscriminant A

-- line segment => usual discriminants

----------
A = matrix {
    {1,1,1,1,1},
    {0,1,0,1,2},
    {0,0,1,1,2}
    }

ADiscriminant(A, Strategy => "Variables")
ADiscriminant(A, Strategy => "Saturation")
ADeterminant A

------------------------
A = matrix {
    {1,1,1,1,1,1},
    {0,1,0,2,1,2},
    {0,0,1,1,2,2}
    }
I = twistedToricIdeal(A, {1,1,1,1,1,1})
J = ideal singularLocus I 
saturate(J, product gens ring I)

ADeterminant(A, Verbose => true)

--------------------------
A = matrix {
    {1,1,1,1},
    {0,1,0,1},
    {0,0,1,1}
    }
I = twistedToricIdeal(A, {1,1,1,1})
J = ideal singularLocus I 
saturate(J, product gens ring I)
ADeterminant(A, Verbose => true)

A = matrix {
    {1,1,1,1,1,1,1,1},
    {0,1,2,0,1,2,0,1},
    {0,0,0,1,1,1,2,2}
    }
I = twistedToricIdeal(A, {1,1,1, 1,1,1, 1,1})
J = ideal singularLocus I;
saturate(J, product gens ring I)

ADeterminant(A, Verbose => true)

A = matrix {
    {1,1,1,1,1,1,1,1,1},
    {0,1,2,0,1,2,0,1,2},
    {0,0,0,1,1,1,2,2,2}
    }
ADeterminant(A, Verbose => true)

A = matrix {
    {1,1,1,1,1,1,1},
    {0,1,2,0,1,2,0},
    {0,0,0,1,1,1,2}
    }
ADeterminant(A, Verbose => true)
