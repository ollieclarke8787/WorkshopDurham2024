--
-- w = {{1,1,1},{1,a,b},{1,c,d}}
-- p_ij
-- u_ij

-- R = QQ[p_(1,1) .. p_(3,3), MonomialOrder => Eliminate(7)]

C = ZZ/101[u_(1,1) .. u_(3,3), a,b,c,d]
F = frac C
R = F[p_(1,1) .. p_(3,3), MonomialOrder => Eliminate(7)]

selectInSubring(1, vars R)
P = matrix for i from 1 to 3 list for j from 1 to 3 list p_(i,j)
U = matrix for i from 1 to 3 list for j from 1 to 3 list u_(i,j)
W = matrix {{1,1,1}, {1,a,b}, {1,c,d}}
I = ideal(
    (
	flatten for s in subsets({1,2,3},2) list for t in subsets({1,2,3},2) list (
	    p_(s_0, t_0) * p_(s_1, t_1) * W_(s_0 - 1, t_1 -1) * W_(s_1 - 1, t_0 -1) - 
	    p_(s_0, t_1) * p_(s_1, t_0) * W_(s_0 - 1, t_0 -1) * W_(s_1 - 1, t_1 -1)
	    )
	) | (
	for i from 0 to 2 list sum first entries P^{i} - sum first entries U^{i}
	) | (
	for i from 0 to 2 list sum first entries transpose P_{i} - sum first entries transpose U_{i}
	)
    )


for i from 1 to 3 do (
    G = gb(I, DegreeLimit => i);
    print("-- DegreeLimit " | net i | ": Number Generators " | net numColumns gens G);
    )

S = selectInSubring(1, gens G)
SIdeal = ideal S;
dim SIdeal

saturate(ideal S, a*b*c*d*product flatten entries U)


------------------------


C = QQ[a,b,c,d, u2p, u3p, up2, up3]
F = frac C
R = F[p_(2,1), p_(3,1)]

d1 = 1 - up2 - up3 + p_(2,1)*(a-1) + p_(3,1)*(c-1)
d2 = 1 - up2 - up3 + p_(2,1)*(b-1) + p_(3,1)*(d-1)

I = ideal(
    (u2p - p_(2,1))*d1*d2 - a*up2*d2 - b*up3*d1,
    (u3p - p_(3,1))*d1*d2 - c*up2*d2 - d*up3*d1
    )

G = gb(I, DegreeLimit => 5)

-----------
-- What if we make d_i the variables:
restart
n = 8
m = 3
C = QQ[w_(2,1) .. w_(3,n), u_1 .. u_n, v_2 .. v_m]
F = frac C
R = F[d_1 .. d_n]

I = ideal(
    for k from 2 to m list (
	(-v_k*product for i from 1 to n list d_i) + sum for i from 1 to n list w_(2,i)*u_i* product for j from 1 to n list if i != j then d_j else continue
	)
    )
dim I
degree I

load "segreEmbeddings.m2"
A = getSegreMatrix {m,n}
w = for i from 1 to numColumns A list random(10, 99)
toricMLDegree(A, w)
