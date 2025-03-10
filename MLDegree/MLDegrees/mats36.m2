L = "********************
0*******************
0******************0
0******0************
0******0******0*****
0******0******0***0*
00**0*****0*********
00**0****00*********
000*00*0**00*0**0***
0000****************
0000************0***
0000************0000
00000*****0*********
00000*****0*******0*
00000*****0*****00**
00000****00****0****
00000****00****000**
00000****00****00000
000000*0**00*0**0***
000000*0**00*0**00**
0000000***000*******
0000000***000******0
00000000**0000**0***
00000000**0000**0**0
000000000*00000*00**
0000000000**********
00000000000*********
00000000000****0****
000000000000*0**0***
0000000000000*******
0000000000000******0
00000000000000**0***
00000000000000**0**0
000000000000000*00**
0000000000000000****
00000000000000000***
000000000000000000**
0000000000000000000*"

-- for each matroid M
-- check that it is realisable i.e. it contrinbutes to the Matroid stratifiaction of the Grassmannian
-- get the values of a,b c ... i for that matroid:

-- M is the column matroid of:
--1 0 0 a b c
--0 1 0 d e f
--0 0 1 g h i

-- set w = (a, b,c, ... i)
-- find ML degree of (P^2 x P^2)_w

needs "matroids.m2"

Llist = toList L

Llists = for i from 0 to 37 list (
    Llist_{21*i .. 21*i + 19}
    )

matroidList = for m in Llists list (
    S := subsets(6, 3);
    matroid(toList(0 .. 5), for i from 0 to 19 list if m_i == "*" then S_i else continue)
    )

S = subsets(6, 3)
p = symbol p
R = QQ[for s in subsets(6, 3) list p_(toSequence s)]
G = Grassmannian(2, 5, R)
lookupSubsets = new HashTable from for i from 0 to 19 list S_i => i 

-*    
realisableMatroids = for M in matroidList list (
    p := product(for b in bases M list (vars R)_(0,lookupSubsets#(sort toList b)));
    G' := sub(G, for b in nonbases M list (vars R)_(0,lookupSubsets#(sort toList b)) => 0);
    if dim saturate(G', p) != -1 then (
	print("-- true for:" | net bases M);
	M ) 
    else (
	print("-- false for:" | net bases M);
	continue
	)
    )
*-

getRealisation = M -> (
    B = (bases M) / toList;
    B0 = B_0;
    i := B0_0;
    j := B0_1;
    k := B0_2;
    remainingIndices := for l from 0 to 5 list if member(l, B0) then continue else l;  
    transpose matrix for l from 0 to 5 list (
	if l == i then {1,0,0} 
	else if l == j then {0,1,0}
	else if l == k then {0,0,1}
	else (
	    {
		(si := sort {j, k, l};
	    	if member(si, B) then 1 else 0),
		(sj := sort {i, k, l};
	    	if member(sj, B) then 1 else 0),
		(sk := sort {i, j, l};
	    	if member(sk, B) then 1 else 0)
		}
	    ) 
	)
    )

end 

load "mats36.m2"

Llist = toList L

Llists = for i from 0 to 37 list (
    Llist_{21*i .. 21*i + 19}
    )

M = matroidList_0
S = subsets(6, 3)
p = symbol p
R = QQ[for s in subsets(6, 3) list p_(toSequence s)]
G = Grassmannian(2, 5, R)
lookupSubsets = new HashTable from for i from 0 to 19 list S_i => i 
p = product(for b in bases M list (vars R)_(0,lookupSubsets#(sort toList b)))
G' = sub(G, for b in nonbases M list (vars R)_(0,lookupSubsets#(sort toList b)) => 0)
saturate(G', p)
dim oo


M = matroidList_5
bases M
-- 2 <--> 3

1 0 0 1 
0 1 0 1 
0 0 1 0 

-- bases: 134, 234, so 124 is a non-basis

getRealisation M



      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
o10 = |set {0, 1, 2}|set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}| 
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 3}|set {0, 2, 3}|set {1, 2, 3}|set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {3, 4, 5}|             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 3}|set {1, 2, 3}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 3}|set {1, 2, 3}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 2, 3}|set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {1, 2, 5}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 4}|set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 4}|set {1, 2, 4}|set {0, 3, 4}|set {1, 3, 4}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {1, 2, 5}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 2, 4}|set {1, 3, 4}|set {2, 3, 4}|set {1, 2, 5}|set {1, 3, 5}|set {2, 3, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 3, 4}|set {1, 3, 4}|set {2, 3, 4}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 3, 4}|set {2, 3, 4}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 3, 4}|set {2, 3, 4}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {2, 3, 4}|set {2, 3, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 1, 5}|set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 2, 5}|set {1, 2, 5}|set {0, 3, 5}|set {1, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 2, 5}|set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 3, 5}|set {1, 3, 5}|set {2, 3, 5}|set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 3, 5}|set {2, 3, 5}|set {1, 4, 5}|set {2, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {2, 3, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {0, 4, 5}|set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {1, 4, 5}|set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {2, 4, 5}|set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+
      |set {3, 4, 5}|             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |             |
      +-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+-------------+


{{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}}
{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {3, 4, 5}}
{{0, 2, 3}, {1, 2, 3}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 3}, {1, 2, 3}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 4}, {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {3, 4, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}}
{{1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}}
{{1, 3, 4}, {2, 3, 4}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 3, 4}, {2, 3, 4}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}}
{{2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 2, 5}, {1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 3, 5}, {1, 3, 5}, {2, 3, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}}
{{1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 3, 5}, {2, 3, 5}, {1, 4, 5}, {2, 4, 5}}
{{2, 3, 5}, {2, 4, 5}, {3, 4, 5}}
{{0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{1, 4, 5}, {2, 4, 5}, {3, 4, 5}}
{{2, 4, 5}, {3, 4, 5}}
{{3, 4, 5}}


-- 1.
load "segreEmbeddings.m2"
A = getSegreMatrix {3,3}

-- 1. Uniform
w = {1,1,1, 1,2,3, 1,3,6}
toricMLDegree(A, w)

-- 2. \456
w = {1,1,1, 1,2,3, 1,3,5}
toricMLDegree(A, w)

w = {1,1,1, 1,2,3, 1,2,4}
toricMLDegree(A, w)

-- 4.
w = {1,1,1, 1,1,2, 1,2,4}
toricMLDegree(A, w)

-- 5.

w = {1,1,1, 1,2,2, 1,2,1}
toricMLDegree(A, w)

-- 7.

w = {1,1,1, 1,1,2, 1,1,3}
toricMLDegree(A, w)

-- 10

w = {1,1,1, 1,2,3, 1,2,3}
toricMLDegree(A, w)

-- 13.

w = {1,1,1, 1,1,2, 1,1,2}
toricMLDegree(A, w)

-- 21.

w = {1,1,1, 1,1,1, 1,1,1}
toricMLDegree(A, w)
