newPackage(
    "RationalPolytopes",
    Version => "0.1",
    Date => "",
    Headline => "A package for Ehrhart theory of rational polytopes",
    Authors => {{ Name => "Victoria Schleis", Email => "victoria.m.schleis@durham.ac.uk", HomePage => "https://victoriaschleis.github.io/"},
		{ Name => "Alex Milner", Email => "A.J.C.Milner@sms.ed.ac.uk", HomePage => ""}},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Polyhedra"}
    )

export {"fx","hStar"}

-* Code section *-
fx = x -> x^2;

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
PolynomialInterpolation(List,List,Ring) := (X,Y,R) -> (
    Xpower := mutableMatrix(R, length X, length X);
    for i in 0..length X-1 do (
	for j in 0..length X-1 do (
	    print(i,j);
	    Xpower_(i,j) = (X#j)^i;
	    );
	);
    S:=solve(matrix(Xpower),transpose matrix(R, {Y}));
    Rpoly:=R[t];
    sum for i in 0..length X - 1 list S_(i,0)*t^i
    )


Ehrhart=method(TypicalValue=>RingElement)
Ehrhart (Polyhedron,ZZ):=(P, i) -> (
    n:=dim P;
    k:=lcm for i in flatten entries vertices P list denominator promote(i,QQ);
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
    1+sum apply(n,a->M#a*x^(n-a))
    )


EhrhartQP=method()
EhrhartQP Polyhedron:=P->(
    k:=lcm for i in flatten entries vertices P list denominator promote(i,QQ);
    for i from 0 to k-1 list Ehrhart(P,i))

P=convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"
EhrhartQP(P)



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
  R:=QQ[t];
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
    fx
  Headline
    a function
  Usage
    n = fx a
  Inputs
    a : ZZ
      a number to be squared
  Outputs
    n : ZZ
      the square of a
  Description
    Text
      it squares things
    Example
      fx 4
      fx 2
  SeeAlso
    RationalPolytopes
///


-* Test section *-
TEST /// -- (0)
assert(1 == fx 1)
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
assert(1_R == hStar(convexHull transpose matrix "0,0,0;1,0,0;0,1,0;0,0,1"),R)
assert(t^5+3*t^4+4*t^3+4*t^2+3*t+1 == hStar(convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"),R)
assert(t+1 == hStar(convexHull transpose matrix "0; 1/2"),R)
assert(t^5+t^3+t^2+1 == hStar(convexHull transpose matrix "1/4; 1/2"),R)
///

end--

-* Development section *-
restart
debug needsPackage "RationalPolytopes"
check "RationalPolytopes"

uninstallPackage "RationalPolytopes"
restart
installPackage "RationalPolytopes"
viewHelp "RationalPolytopes"
