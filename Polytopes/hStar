

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
