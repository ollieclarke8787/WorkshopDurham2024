needsPackage "Polyhedra"

IsLatticePolytope=method()
IsLatticePolytope(Polyhedron) := P -> (
	M = vertices P;
	test = true;
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
	denom = DenominatorOfPolytope(P);
	T = { {0,1} };
	for d in 1 .. denom*(dim P + 1) do (
		T = append(T, {d, length latticePoints (d*P)} );
	);
	SortedT = {};
	for i in 0..denom-1 do(
		SortedT = append(SortedT, for j in 0..dim P list T#(j*denom + i) );
	);
	print T;
	print SortedT;
)

PolynomialInterpolation=method()
PolynomialInterpolation(List,List,Ring) := (X,Y,R) -> (
	Xpower = mutableMatrix(R, length X, length X);
	for i in 0..length X-1 do (
		for j in 0..length X-1 do (
			print(i,j);
			Xpower_(i,j) = (X#j)^i;
		);
	);
	S=solve(matrix(Xpower),transpose matrix(R, {Y}));
	Rpoly=R[t];
	sum for i in 0..length X - 1 list S_(i,0)*t^i
)


end

load "Polytopes - Danny and Ben.m2"

P = convexHull matrix {{1,2,3},{1/3,1/2,5/3}}

TabularOfValues(P)
