needsPackage "FourTiTwo"
needsPackage "NumericalAlgebraicGeometry"


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
    p := symbol p;
    R := QQ[for i from 1 to n list p_i];
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


-------
-- Implicit version


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
ADiscriminant = method()
ADiscriminant Matrix := A -> (
    n := numColumns A;
    d := numRows A;
    t := symbol t;
    w := symbol w;
    R := QQ[t_1 .. t_d, s_1 .. s_d, w_1 .. w_n, MonomialOrder => Eliminate(2*d)];
    g := sum for i from 0 to n-1 list R_(2*d + i) * product for j from 0 to d-1 list R_j^(A_(j,i));
    I := ideal({g} | (for i from 0 to d-1 list diff(R_i, g)) | (for i from 0 to d-1 list R_i * R_(d+i) - 1));
    -- eliminate t_1 .. t_d
    W := ideal selectInSubring(1, gens gb I); -- generator is the principal A-determinant
    R' := QQ[w_1 .. w_n];
    m := map(R', R, toList(2*d : 0_(R')) | gens R');
    m saturate(W, product for i from 0 to n-1 list R_(2*d+i))
    )


-- compute ML degree using linear equations
MLDegree = method()



end --
restart
load "MLDegrees.m2"

A = matrix {{1, 1, 1, 1, 1, 1}, {0, 1, 2, 0, 1, 0}, {0, 0, 0, 1, 1, 2}}
ADiscriminant A

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


w = {1,2,1,2,2,1}
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

ADiscriminant A


