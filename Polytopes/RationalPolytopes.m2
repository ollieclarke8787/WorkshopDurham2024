newPackage(
    "RationalPolytopes",
    Version => "0.1",
    Date => "",
    Headline => "A package for Ehrhart theory of rational polytopes",
    Authors => {
	{Name => "Oliver Clarke", Email => "oliver.clarke@ed.ac.uk", HomePage => "https://www.oliverclarkemath.com/"},
	{Name => "Alex Milner", Email => "A.J.C.Milner@sms.ed.ac.uk", HomePage => ""},
	{Name => "Victoria Schleis", Email => "victoria.m.schleis@durham.ac.uk", HomePage => "https://victoriaschleis.github.io/"}},
   AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Polyhedra"}
    )

export {
    "hStar",
    "PolynomialInterpolation",
    "Ehrhart",
    "EhrhartQP",
    "quasiPolynomial",
    "period"
    }

-* QuasiPolynomial Type *-

-- List of polynomial
-- Period
-- Ring of Polynomial
-- degree
-- coefficient list
-- leading coefficient

cleaning = method()
cleaning(Matrix) := M->M; -- Waiting for the full cleaning function.

QuasiPolynomial = new Type of HashTable
quasiPolynomial = method()
quasiPolynomial(Matrix) := M -> (
    Mclean:=cleaning(M);
    new QuasiPolynomial from {
	period => numRows(Mclean), -- computation of the period from the matrix
	coefficients => Mclean,
	cache => new CacheTable,
	}
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





-* Code section *-

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
    for i from 0 to k-1 list Ehrhart(P,i))


hStar = method()
hStar(Polyhedron , Ring) := (P, R) -> (
  n:=dim P;
  dnom := lcm for i in flatten entries vertices P list denominator promote(i,QQ);
  p:=1;
  t:=R_0;
  for i from 1 to n*dnom+1 do (p=p + #latticePoints(i*P) * t^i);
  f:=0;
  r:=(1-t^dnom)^(n+1);
  for i from 0 to n*dnom+1 do f=f+part(i,p * r);
  f
  )

hStar(Polyhedron) := P -> (
  R:=QQ[Variables => 1];
  hStar(P,R)
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
    PolynomialInterpolation
  Headline
    A method that compute the interpolation polynomial of a set of points.
  Usage
    P = PolynomialInterpolation(X,Y,R)
  Inputs
    X : List
      a list of the x-coordinates of the points.
    Y : List
      a list of the y-coordinates of the points in the same order as in X.
    R : PolynomialRing
      an univariate polynomial ring over a ring containing all the coefficients of X and Y.
  Outputs
    P : RingElement
      The interpolation polynomial.
  Description
    Text
      A method that computes the interpolation polynomial of a set of points defined by (X_i,Y_i).
    Example
      PolynomialInterpolation({1,2,3},{1,4,9},QQ[x])
  SeeAlso
    RationalPolytopes
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



-* Test section *-
TEST /// -- (1)
R=QQ[t]
assert(1_R == hStar(convexHull transpose matrix "0,0,0;1,0,0;0,1,0;0,0,1",R))
assert(t^5+3*t^4+4*t^3+4*t^2+3*t+1 == hStar(convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2",R))
assert(t+1 == hStar(convexHull transpose matrix "0; 1/2",R))
assert(t^5+t^3+t^2+1 == hStar(convexHull transpose matrix "1/4; 1/2",R))
///

end--

-* Development section *-
restart

uninstallPackage "RationalPolytopes"
restart
installPackage "RationalPolytopes"

viewHelp "RationalPolytopes"
debug needsPackage "RationalPolytopes"

check "RationalPolytopes"


P=convexHull transpose matrix "0;1/2"
EhrhartQP(P)

P=convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"
EhrhartQP(P)

P=convexHull transpose matrix "-1/2; 1/2"
EhrhartQP(P)

M=matrix{{1,2},{3,4}}

QP=quasiPolynomial(M)
QP#"period"


M=matrix({{1,2,3,4},{0,2,0,4}})
quasiPolynomial(M)

-- Test of the constructor of the Type QuasiPolynomial

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
