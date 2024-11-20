newPackage(
    "RationalPolytopes",
    Version => "0.1",
    Date => "",
    Headline => "A package for Ehrhart theory of rational polytopes",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Polyhedra"}
    )

export {"fx"}

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
hStar(Polyhedron) := P -> (
  n:=dim P;
  dnom := lcm for i in flatten entries vertices P list denominator promote(i,QQ);  
  R:=QQ[t];
  p:=1;
  for i from 1 to n*dnom+1 do (p=p + #latticePoints(i*P) * t^i);
  f:=0;
  for i from 0 to n*dnom+1 do f=f+part(i,p * (1-t^dnom)^(n+1));
  f
  )

exs={transpose matrix "1,0;-1,0;0,1/2;0,-1/2", 
    transpose matrix "0; 1/2",
    transpose matrix "0,0,0;1,0,0;0,1,0;0,0,1"};

hStar \convexHull\exs



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

end--

-* Development section *-
restart
debug needsPackage "RationalPolytopes"
check "RationalPolytopes"

uninstallPackage "RationalPolytopes"
restart
installPackage "RationalPolytopes"
viewHelp "RationalPolytopes"
