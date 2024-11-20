1+1
-- new file: ctrl x ctrl f

-- f12: start M2

-- list buffers ctrl-x ctrl-b

-- switch buffers (i.e. windows) click on them

-- hide buffers ctrl-x 0

-- open buffer on left ctrl-x 3

-- open buffer below ctrl-x 2

-- maximise current buffer ctrl-x 1

-- kill buffer ctrl-x k

-- f11 run current line of code in M2

-- save ctrl-x ctrl-s

--

needsPackage "Tropical"
needsPackage "Polyhedra"

P = convexHull matrix{{1,2,3},{1,0,0}}
vertices P
R = QQ[x,y,z]
S = QQ[a,b,c,d,e,f]
f = a*f-b*e+d*d
I = Ideal(f)
I = ideal(f)
tropicalVariety(I)
