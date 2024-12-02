newPackage(
    "RationalPolytopes",
    Version => "0.1",
    Date => "",
    Headline => "A package for Ehrhart theory of rational polytopes",
    Authors => {
	{Name => "Oliver Clarke", Email => "oliver.clarke@ed.ac.uk", HomePage => "https://www.oliverclarkemath.com/"},
	{Name => "Alex Milner", Email => "A.J.C.Milner@sms.ed.ac.uk", HomePage => ""},
	{Name => "Victoria Schleis", Email => "victoria.m.schleis@durham.ac.uk", HomePage => "https://victoriaschleis.github.io/"},
	{Name => "Vincenzo Reda", Email => "redav@tcd.ie", HomePage => ""},
	{Name => "Benoît Guerville-Ballé", Email => "benoit.guerville-balle@math.cnrs.fr", HomePage => "https://www.benoit-guervilleballe.com"}
	},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Polyhedra"}
    )

export {
    "hStar",
    "Ehrhart",
    "EhrhartQP",
    "isPeriod",
    -- "cleanCoefficients",
    "quasiPolynomial",
    "period",
    "displayQP",
    "periodQP",
    "coefficientMonomial",
    "ehrhartSeries",
    "ReturnDenominator"
    }

-* QuasiPolynomial Type *-

-- Cleaning function

isPeriod=method()
isPeriod(Matrix,ZZ) := (M,q) -> (
    result:=true;
    if numRows M%q!=0 then result=false;
    if numRows M%q==0 then (
	for j from 0 to numRows M//q-1 do(
	    if M^(toList(0 .. q-1))!=M^(toList((j*q .. (j+1)*q-1))) then result=false;
	    );
	);
    result
    )

cleaning = method()
cleaning(Matrix) := M-> (
    q:=0;
    for p from 1 to numRows M-1 do(
	if isPeriod(M,p) then q=p;
    );
    if q!=0 then (
	M=submatrix'(M,toList(q .. numRows M-1),);
	);
    M
    )


-- Definition of the Type QuasiPolynomial

QuasiPolynomial = new Type of HashTable

quasiPolynomial = method()
quasiPolynomial(Matrix) := M -> (
    Mclean:=cleaning(M);
    new QuasiPolynomial from {
	period => numRows(Mclean),
	coefficients => Mclean,
	cache => new CacheTable,
	}
    )

net QuasiPolynomial := QP -> (
    "QuasiPolynomial of degree " | net(numColumns(QP#coefficients)-1) | " and of period " | net(QP#period)
)

quasiPolynomial(List) := L -> (
    if not isMember(false, for l in L list instance(l,List)) then (
	D:=max for p in L list length p;
	L1:=for p in L list ((for i in 0..D-length p -1 list 0)|p);
	quasiPolynomial(matrix(L1))
	)
    else if not isMember(false, for l in L list instance(class l,PolynomialRing)) then(
	if not isMember(false, for l in L list numgens class l==1) then (
	    D1:=max for p in L list (degree p)#0;
	    lM:=for p in L list sub( (coefficients(p, Monomials=>for d in 0..D1 list ((generators class p)#0)^(D1-d)))#1, QQ);
	    M:=transpose fold((a,b) -> a|b, lM);
	    quasiPolynomial(M)
	    )
	)
    )


-- QuasiPolynomial as a function.

QuasiPolynomial ZZ := (QP, v) -> (
    internalQuasiPolynomial(QP,v)
)

internalQuasiPolynomial = method()
internalQuasiPolynomial(QuasiPolynomial, ZZ) := (QP,t) -> (
    r :=  (QP#coefficients)^{t%QP#period};
    T := matrix for i in 0..(numRows QP#coefficients - 1) list {t^(numrows QP#coefficients - i)};
    (r*T)_(0,0)
    )


-- Various methods associated to a QuasiPolynomial

displayQP = method()
displayQP(QuasiPolynomial) := QP -> (
    R:=QQ[getSymbol "t"];
    t1:=(gens R)#0;
    Mono := flatten  for d in 0..(numColumns QP#coefficients)-1 list {" + ", (QP#coefficients)_(d),t1^(numColumns (QP#coefficients)-d-1)};
    fold((a,b) -> net a | net b , take(Mono,{1,length(Mono)-2}))
    )

degree(QuasiPolynomial) := QP -> (
    numColumns(QP#coefficients)-1
    )

periodQP =method()
periodQP(QuasiPolynomial) := QP -> (
    numRows(QP#coefficients)
    )

coefficientMonomial = method()
coefficientMonomial(QuasiPolynomial,ZZ) := (QP,i) -> (
    if i < degree(QP)+1 then M:=QP#coefficients_{degree(QP)-i};
    if i > degree(QP) then M=0;
    M
    )



-* Ehrhart Polynomial part *-


Ehrhart=method(TypicalValue=>RingElement)
Ehrhart (Polyhedron,ZZ):=(P, i) -> (
    n:=dim P;
    k:=lcm for j in flatten entries vertices P list denominator promote(j,QQ);
    R:=QQ[getSymbol "x"];
    x:=R_"x";
    S:=for j from 0 to n list i+j*k;
    if n==0 and (not isEmpty P) then return 1+0*x;
    if isEmpty P then return 0+0*x;
    v:=matrix apply(S,h->(
	    if h == 0 then {0}
	    else {-1+#latticePoints(h*P)}
	    )
	);
    v=promote(v,QQ);
    M:=promote(matrix apply(S,a->reverse apply(n+1,j->( a^j ))),QQ);
    M=flatten entries((inverse M)*v);


    1+sum apply(n+1,a->M_(a)*x^(n-a))
    )


EhrhartQP=method()
EhrhartQP Polyhedron:=P->(
    k:=lcm for i in flatten entries vertices P list denominator promote(i,QQ);
    quasiPolynomial(for i from 0 to k-1 list Ehrhart(P,i))
    )


hStar = method(
    Options => {
	ReturnDenominator => false --returns a pair of polys (h, d) s.t. Ehrhart series is h/d
	})

hStar(Polyhedron , Ring) := opts -> (P, R) -> (
    n:=dim P;
    dnom := lcm for i in flatten entries vertices P list denominator promote(i,QQ);
    p:=1;
    t:=R_0;
    for i from 1 to (n+1)*dnom do (p=p + #latticePoints(i*P) * t^i);
    r:=(1-t^dnom)^(n+1);
    f := (p*r) % t^((n+1)*dnom);
    if opts.ReturnDenominator then (f, r) else f
  )

hStar(Polyhedron) := opts -> P -> (
  R:=QQ[getSymbol "t"];
  hStar(P, R, opts)
  )


ehrhartSeries = method()
ehrhartSeries(Polyhedron, Ring) := (P, R) -> (
    (h, d) := hStar(P, R, ReturnDenominator => true);
    F := frac R;
    h = h_F;
    d = d_F;
    h/d
    )

ehrhartSeries Polyhedron := P -> (
    ehrhartSeries(P, QQ[getSymbol "t"]) 
    )



-* Documentation section *-
beginDocumentation()

doc ///
  Key
    RationalPolytopes
  Headline
    A package for Ehrhart theory of rational polytopes
///

doc ///
  Key
    Ehrhart
  Headline
    a function
  Usage
    p = Ehrhart(P,i)
  Inputs
    P : Polyhedron
    i : ZZ
      (P,i) is a polyhedron and integer to calculate the ith polynomial piece contributing to the Ehrhart quasipolynomial for P
  Outputs
    p : QQ[x]
      the ith polynomial contributing to the Ehrhart quasipolynomial of P
  Description
    Text
      it calculates the ith polynomial piece contributing to the Ehrhart quasipolynomial of a polyhedron P
    Example
      Ehrhart(convexHull transpose matrix "0,0;1/2,0;0,1/2",0)
      Ehrhart(convexHull transpose matrix "0,0;1/2,0;0,1/2",1)

  SeeAlso
    RationalPolytopes
///


doc ///
  Key
    EhrhartQP
  Headline
    a function
  Usage
    L = EhrhartQP(P)
  Inputs
    P : Polyhedron
      the polyhedron for which we calculate the Ehrhart quasipolynomial
  Outputs
    L : List
      a list of polynomial pieces contributing to the Ehrhart quasipolynomial of P
  Description
    Text
      it calculates the Ehrhart quasipolynomial of polyhedron P
    Example
      EhrhartQP(convexHull transpose matrix "0,0;1/2,0;0,1/2")
///



doc ///
  Key
    hStar
  Headline
    a method
  Usage
    hStar P
    hStar(P,R)
  Inputs
    P : Polyhedron
      A convex polyhedron which must be compact
    R : Ring
      A ring in one variable
  Outputs
    f : RingElement
      the hStar polynomial (in the ring R) of the input Polytope
  Description
    Text
      Computes the hStar polynomial of a polytope
    Example
      hStar convexHull transpose matrix "0; 1/2"
      hStar convexHull transpose matrix "0,0,0;1,0,0;0,1,0;0,0,1"
      hStar convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"
  SeeAlso
    RationalPolytopes
///

doc ///
  Key
    isPeriod
  Headline
    a function
  Usage
    result = isPeriod(M,q)
  Inputs
    M : Matrix
    q : ZZ
  Outputs
    result : Boolean
      result is true if q is the period and false otherwise
  Description
    Text
      It returns true if q is the period and false otherwise
    Example
      isPeriod(matrix "1,1;2,2;1,1;2,2",2)
      isPeriod(matrix "1,1;2,2;1,1;3,2",2)
      isPeriod(matrix "1,2,5;2,4,3;1,2,5;3,4,5;1,2,5;2,4,3;1,2,5;3,4,5",3)
  SeeAlso
    RationalPolytopes
///

doc ///
  Key
    periodQP
  Headline
    a function
  Usage
    p = periodQP(QP)
  Inputs
    QP : QuasiPolynomial
      A quasipolynomial of which we want to compute the period
  Outputs
    p : ZZ
      The period of QP
  Description
    Text
      Computes the period of a quasipolynomial
    Example
      periodQP(quasiPolynomial(matrix{{1,2,3},{1,4,5}}))
      periodQP(quasiPolynomial(matrix{{1,1},{1,2},{1,1},{1,2}}))
      periodQP(quasiPolynomial(matrix{{3,6,7,2},{3,4,4,2},{3,2,5,6}}))
  SeeAlso
    RationalPolytopes
///

doc ///
  Key
    coefficientMonomial
  Headline
    a function
  Usage
    L = coefficientMonomial(QP,i)
  Inputs
    QP : QuasiPolynomial
      A quasipolynomial of which we want to know the coefficients
    i : ZZ
      The degree of the monomials of QP of which we want to know the coefficients 
  Outputs
    L : List
      The coefficients of the monomials of degree i appearing in QP
  Description
    Text
      Computes the coefficients of the monomials of degree i appearing in QP
    Example
      coefficientMonomial(quasiPolynomial(matrix{{1,2,3},{1,4,5}}),2)
      coefficientMonomial(quasiPolynomial(matrix{{1,1},{1,2},{1,1},{1,2}}),0)
      coefficientMonomial(quasiPolynomial(matrix{{3,6,7,2},{3,4,4,2},{3,2,5,6}}),2)
  SeeAlso
    RationalPolytopes
///
  


-* Test section *-
TEST /// -- (1)
R=QQ[t]
assert(1_R == hStar(convexHull transpose matrix "0,0,0;1,0,0;0,1,0;0,0,1",R))
assert(t^5+3*t^4+4*t^3+4*t^2+3*t+1 == hStar(convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2",R))
assert(t+1 == hStar(convexHull transpose matrix "0; 1/2",R))
assert(t^5+t^3+t^2+1 == hStar(convexHull transpose matrix "1/4; 1/2",R))
///



end--

----------------------------------
-- Plans for future development --
----------------------------------

-- To-do list --

-- check exported functions work with easy examples
-- that can be computed by hand


-- implement a method for internalQuasiPolynomial that implements the following procedure:
-- 1) check the cache for a stored list of polynomials
-- 2) if there is no list, use the coefficients matrix to produce a list of polynomials and cache them
-- 3) take the input i modulo the period to obtain j, and return polynomial number j evaluated at i


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


--------------------------------------------------

-* Development section *-
restart

uninstallPackage "RationalPolytopes"

restart
installPackage "RationalPolytopes"

viewHelp "RationalPolytopes"
debug needsPackage "RationalPolytopes"

check "RationalPolytopes"


P=convexHull transpose matrix "0;1/2"
EQP=EhrhartQP(P)

P=convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"
diasplayQP EhrhartQP(P)

P=convexHull transpose matrix "-1/2; 1/2"
EhrhartQP(P)



-- Test of the constructor of the Type QuasiPolynomial


S=matrix({{1,2,3},{1,4,5}})
M=matrix({{1,2,3},{0,1,0},{1,2,3},{0,1,0}})
>>>>>>> d04361317282fa5dc9611b857a026e43e63b2a0d
QP=quasiPolynomial(M)
QP#period
print QP
displayQP QP
degree QP
periodQP QP
coefficientMonomial(QP,0)

R=QQ[x]
R1=QQ[t]
L={x^2+3,2*t}
quasiPolynomial(L)

L={{1,0,3},{2,0}}
quasiPolynomial(L)


--- Benchmarking examples -- functions with timings :)



IsLatticePolytope=method()
IsLatticePolytope(Polyhedron) := P -> (
    M := vertices P;
    test := true;
    for a in flatten entries M do (
	if denominator(a) != 1 then (
	    test = false;
	    );
	);
    test
    );

DenominatorOfPolytope=method()
DenominatorOfPolytope(Polyhedron) := P -> (
    lcm for x in flatten entries vertices P list denominator(x)
    )

EhrhartPolynomial=method()
EhrhartPolynomial(Polyhedron) := P -> (
    if IsLatticePolytope P then (
	ehrhart P
	)
    else (
	print DenominatorOfPolytope(P);
	print "Work in progress...";
	);
    )

TabularOfValues=method()
TabularOfValues(Polyhedron) := P -> (
    denom := DenominatorOfPolytope(P);
    T := { {0,1} };
    for d in 1 .. denom*(dim P + 1) do (
	T = append(T, {d, length latticePoints (d*P)} );
	);
    SortedT := {};
    for i in 0..denom-1 do(
	SortedT = append(SortedT, for j in 0..dim P list T#(j*denom + i) );
	);
    print T;
    print SortedT;
)

PolynomialInterpolation=method()
PolynomialInterpolation(List,List,PolynomialRing) := (X,Y,R) -> (
    Xpower := mutableMatrix(coefficientRing R, length X, length X);
    for i in 0..length X-1 do (
	for j in 0..length X-1 do (
	    Xpower_(i,j) = (X#i)^j;
	    );
	);
    S:=solve(matrix(Xpower),transpose matrix(coefficientRing R, {Y}));
    sum for i in 0..length X - 1 list S_(i,0)*((generators R)#0)^i
    )


Ehrhart=method(TypicalValue=>RingElement)
Ehrhart (Polyhedron,ZZ):=(P, i) -> (
    n:=dim P;
    k:=lcm for j in flatten entries vertices P list denominator promote(j,QQ);
    R:=QQ[getSymbol "x"];
    x:=R_"x";
    S:=for j from 0 to n list i+j*k;
    if n==0 and (not isEmpty P) then return 1+0*x;
    if isEmpty P then return 0+0*x;
    v:=matrix apply(S,h->(
	    if h == 0 then {elapsedTime 0}
	    else {
					elapsedTime print h;
					elapsedTime -1+#latticePoints(h*P)
					}
	    )
	);
    v=promote(v,QQ);
    M:=promote(matrix apply(S,a->reverse apply(n+1,j->( a^j ))),QQ);
    M=flatten entries((inverse M)*v);


    1+sum apply(n+1,a->M_(a)*x^(n-a))
    )


EhrhartQP=method()
EhrhartQP Polyhedron:=P->(
    k:=lcm for i in flatten entries vertices P list denominator promote(i,QQ);
    for i from 0 to k-1 list Ehrhart(P,i))


hStar = method()
hStar(Polyhedron , Ring) := (P, R) -> (
  n:=dim P;
  dnom := lcm for i in flatten entries vertices P list denominator promote(i,QQ);
  p:=1;
  t:=R_0;
  for i from 1 to n*dnom+1 do (,
			elapsedTime p =p + #latticePoints(i*P) * t^i),
  f:=0;
  r:=(1-t^dnom)^(n+1);
  for i from 0 to n*dnom+1 do f=f+part(i,p * r);
  f
  )

hStar(Polyhedron) := P -> (
  R:=QQ[Variables => 1];
  hStar(P,R)
  )




P = convexHull transpose matrix "1,0;-1,0;0,1/20;-1,11/20"
EhrhartQP(P)

hStar P
ehrhartSeries P


-----------------------------------
--old doc--

doc ///
  Key
    cleanCoefficients
  Headline
    a function
  Usage
    T = cleanCoefficients(M)
  Inputs
    M : Matrix
  Outputs
    T : Matrix
      T is obtained from M eliminating periodicity in M
  Description
    Text
      it produces a matrix from M which is not periodic
    Example
      cleanCoefficients(matrix "1,1;2,2;1,1;2,2")
      cleanCoefficients(matrix "1,1;2,2;1,1;2,2")
      cleanCoefficients(matrix "1,2,5;2,4,3;1,2,5;3,4,5;1,2,5;2,4,3;1,2,5;3,4,5")
  SeeAlso
    RationalPolytopes
///

doc ///
  Key
   "degree(QuasiPolynomial)"
  Headline
    a function
  Usage
    n = degree(QP)
  Inputs
    QP : QuasiPolynomial
      A quasipolynomial of which we want to know the degree
  Outputs
    n : ZZ
      The degree of QP
  Description
    Text
      Computes the degree of a quasipolynomial
    Example
      degree(quasiPolynomial(matrix{{1,2,3},{1,4,5}}))
      degree(quasiPolynomial(matrix{{1,1},{1,2},{1,1},{1,2}}))
      degree(quasiPolynomial(matrix{{3,6,7,2},{3,4,4,2},{3,2,5,6}}))
  SeeAlso
    RationalPolytopes
///

