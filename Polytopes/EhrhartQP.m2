needsPackage "Polyhedra"

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
M:=promote(matrix apply(S,a->reverse apply(n+1,j->( a^j
                )
            )),QQ);
M=flatten entries((inverse M)*v);
1+sum apply(n,a->M#a*x^(n-a))
)



EhrhartQP=method()

EhrhartQP Polyhedron:=P->(k:=lcm for i in flatten entries vertices P list denominator promote(i,QQ);
for i from 0 to k-1 list Ehrhart(P,i))

P=convexHull transpose matrix "1,0;-1,0;0,1/2;0,-1/2"
EhrhartQP(P)
