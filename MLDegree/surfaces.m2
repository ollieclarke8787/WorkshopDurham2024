needsPackage "FourTiTwo"

end --


-- Toric ideal using 4ti2
R = QQ[x_1 .. x_6]
I = toricMarkov(matrix {
	{1, 1, 1, 1, 1, 1},
    	{0, 1, 2, 0, 1, 0},
    	{0, 0, 0, 1, 1, 2}
    	}, 
    R)

H = ideal(varList := first entries vars R; (product varList)*(sum varList))
degree(I:H)
degree(I+H)
    

-- scaled Veronese:

S = QQ[a,b,c]
scaledVeronese = method()
scaledVeronese(List) := c -> (
    m := map(S, R, {
	    c_0 * S_0, 
	    c_1 * S_0 * S_1, 
	    c_2 * S_0 * S_1^2, 
	    c_3 * S_0 * S_2,
	    c_4 * S_0 * S_1 * S_2,
	    c_5 * S_0 * S_2^2
	    }
	);
    ker m
    )

I111111 = scaledVeronese({1,1,1,1,1,1}) 
I121221 = scaledVeronese({1,2,1,2,2,1}) 

transpose mingens (I111111 : H)
transpose mingens (I121221 : H)

-*
l_u = \prod x_i^u_i / (\sum x_i)^\sum u_i

-- want to maximize l_u on V\H

use logarithmic derivative
and Lagrange multiplier theorem to get the ML degree
*-


J = transpose jacobian mingens I111111
use R
u = for i from 1 to 6 list random(10, 100)
firstTwoRows = matrix {toList(numColumns J : 1), for i from 0 to numColumns J - 1 list u_i * product for j from 0 to numColumns J - 1 list if i == j then continue else x_(j+1) }

M = firstTwoRows || J
I = I111111 + minors(6, M)
mingens I
degree I

J = transpose jacobian mingens I121221
use R
u = for i from 1 to 6 list random(10, 100)
firstTwoRows = matrix {toList(numColumns J : 1), for i from 0 to numColumns J - 1 list u_i * product for j from 0 to numColumns J - 1 list if i == j then continue else x_(j+1) }

M = firstTwoRows || J
I = (I121221 + minors(6, M))
transpose mingens I
I == I121221
degree I

(I121221 + minors(6, jacobian I121221)) == I121221 -- smooth


J = matrix {{1,1,1,1,1,1}} ||  transpose jacobian mingens I121221
D = diagonalMatrix for i from 1 to 6 list x_i
M = matrix {for i from 1 to 6 list random(10, 100)} || J*D
I = I121221 + minors(6, M)
I == I121221

------------
-- liklihood equations 

A = matrix {
    {1, 1, 1, 1, 1, 1},
    {0, 1, 2, 0, 1, 0},
    {0, 0, 0, 1, 1, 2}
    }

use S
S' = QQ[a,b,c,s]
m = map(S', S, {S'_0, S'_1, S'_2})
f = a + 2*a*b + a*b^2 + 2*a*c + 2*a*b*c + a*c^2 
jacobian f

u = transpose matrix {for i from 1 to 6 list random(10, 99)} 
uPlus = sum first entries transpose u
eqns = flatten {1 - s*m(f), for i from 0 to 2 list (
	(A*u)_(i, 0) - (uPlus * s * S'_i * diff(S'_i, m(f)))
	) 
    }

use R 

Lf = x_1 + 2*x_2 + x_3 + 2*x_4 + 2*x_5 + x_6
df1 = S'_0 * diff(S'_0, m(f))
L1 = x_1 + 2*x_2 + x_3 + 2*x_4 + 2*x_5 + x_6 -- == Lf
df2 = S'_1 * diff(S'_1, m(f))
L2 = 2*x_2 + 2*x_3 + 2*x_5
df3 = S'_2 * diff(S'_2, m(f))
L3 = 2*x_4 + 2*x_5 + 2*x_6 

eqnR = {
    (A*u)_(0,0) * Lf - uPlus * L1,
    (A*u)_(1,0) * Lf - uPlus * L2,
    (A*u)_(2,0) * Lf - uPlus * L3
    }
E = ideal eqnR
mingens (I121221 + E)
I = I121221 + E
degree I
HP = ideal x_1*x_2*x_3*x_4*x_5*x_6*Lf
degree(I : H)

----------------

restart

R = QQ[u_1 .. u_6, w_1 .. w_6,t_1, t_2, t_3]
M = matrix {
    {(u_1)_R + (u_2)_R + (u_3)_R + (u_4)_R + (u_5)_R + (u_6)_R, (u_2)_R + 2*(u_3)_R + (u_5)_R, (u_4)_R + (u_5)_R + 2*(u_6)_R},
    {
	t_1*((w_1)_R + (w_2)_R*t_2 + (w_3)_R*t_2^2 + (w_4)_R*t_3 + (w_5)_R*t_2*t_3 + (w_6)_R*t_3^2),
    	t_2*((w_2)_R*t_1 + 2*(w_3)_R*t_1*t_2 + (w_5)_R*t_1*t_3),
	t_3*((w_4)_R*t_1 + (w_5)_R*t_1*t_2 * 2*(w_6)_R*t_1*t_3)
	}
    }	 
g = (w_1)_R*t_1 + (w_2)_R*t_1*t_2 + (w_3)_R*t_1*t_2^2 + (w_4)_R*t_1*t_3 + (w_5)_R*t_1*t_2*t_3 + (w_6)_R*t_1*t_3^2 - 1
I = ideal(g) + minors(2, M)
degree I

S = QQ[s_1 .. s_3]

m = map(S, R, {    
	(u_1)_R => random(10, 99), (u_2)_R => random(10, 99), (u_3)_R => random(10, 99), 
	(u_4)_R => random(10, 99), (u_5)_R => random(10, 99), (u_6)_R => random(10, 99),
	(w_1)_R => 1, (w_2)_R => 1, (w_3)_R => 1, 
	(w_4)_R => 1, (w_5)_R => 1, (w_6)_R => 1, 
	t_1 => s_1, t_2 => s_2, t_3 => s_3
	}
    )

J = m I

degree(J : s_1*s_2*s_3)
dim J

-------------------------------------

-- w = (1,2,1,2,2,1)

R = QQ[t_1, t_2, t_3]
w = {1,2,1,2,2,1}
u = for i from 1 to 6 list random(1, 100)

g = (w_0)_R*t_1 + (w_1)_R*t_1*t_2 + (w_2)_R*t_1*t_2^2 + (w_3)_R*t_1*t_3 + (w_4)_R*t_1*t_2*t_3 + (w_5)_R*t_1*t_3^2 - 1

M = matrix {
    {
	u_0 + u_1 + u_2 + u_3 + u_4 + u_5, 
	u_1 + 2*u_2 + u_4,
	u_3 + u_4 + 2*u_5
	},
    {
	t_1*((w_0)_R + (w_1)_R*t_2 + (w_2)_R*t_2^2 + (w_3)_R*t_3 + (w_4)_R*t_2*t_3 + (w_5)_R*t_3^2),
	t_2*((w_1)_R*t_1 + 2*(w_2)_R*t_1*t_2 + (w_4)_R*t_1*t_3),
	t_3*((w_3)_R*t_1 + (w_4)_R*t_1*t_2 * 2*(w_5)_R*t_1*t_3)
	}
    }	 

I = minors(2, M) + ideal g
dim I
degree (I : t_1*t_2*t_3)

getIdeal = (w, u) -> (
    g := (w_0)_R*t_1 + (w_1)_R*t_1*t_2 + (w_2)_R*t_1*t_2^2 + (w_3)_R*t_1*t_3 + (w_4)_R*t_1*t_2*t_3 + (w_5)_R*t_1*t_3^2 - 1;
    M := matrix {
    	{
	    u_0 + u_1 + u_2 + u_3 + u_4 + u_5, 
	    u_1 + 2*u_2 + u_4,
	    u_3 + u_4 + 2*u_5
	    },
    	{
	    t_1*((w_0)_R + (w_1)_R*t_2 + (w_2)_R*t_2^2 + (w_3)_R*t_3 + (w_4)_R*t_2*t_3 + (w_5)_R*t_3^2),
	    t_2*((w_1)_R*t_1 + 2*(w_2)_R*t_1*t_2 + (w_4)_R*t_1*t_3),
	    t_3*((w_3)_R*t_1 + (w_4)_R*t_1*t_2 * 2*(w_5)_R*t_1*t_3)
	    }
    	};
    I := minors(2, M) + ideal g
    )

computeDegree = (w, u) -> (
    -- R := QQ[t_1, t_2, t_3];
    g := (w_0)_R*t_1 + (w_1)_R*t_1*t_2 + (w_2)_R*t_1*t_2^2 + (w_3)_R*t_1*t_3 + (w_4)_R*t_1*t_2*t_3 + (w_5)_R*t_1*t_3^2 - 1;
    M := matrix {
    	{
	    u_0 + u_1 + u_2 + u_3 + u_4 + u_5, 
	    u_1 + 2*u_2 + u_4,
	    u_3 + u_4 + 2*u_5
	    },
    	{
	    t_1*((w_0)_R + (w_1)_R*t_2 + (w_2)_R*t_2^2 + (w_3)_R*t_3 + (w_4)_R*t_2*t_3 + (w_5)_R*t_3^2),
	    t_2*((w_1)_R*t_1 + 2*(w_2)_R*t_1*t_2 + (w_4)_R*t_1*t_3),
	    t_3*((w_3)_R*t_1 + (w_4)_R*t_1*t_2 * 2*(w_5)_R*t_1*t_3)
	    }
    	};
    I := minors(2, M) + ideal g;
    degree (I : t_1*t_2*t_3)
    )

while true do (
    u := for i from 1 to 6 list random(1, 100);
    w := for i from 1 to 6 list random(1, 100);
    d := computeDegree(u, w);
    if d < 6 then print(d, w, u);
    )


-*
(4, {32, 3, 88, 63, 28, 56}, {9, 24, 16, 16, 49, 82})
(5, {40, 53, 87, 84, 34, 72}, {92, 14, 4, 18, 28, 49})
(4, {56, 43, 60, 3, 42, 10}, {44, 44, 11, 5, 32, 11})
*-

needsPackage "NumericalAlgebraicGeometry"

Q = CC[q_1, q_2, q_3]
RtoQ = map(Q, R, vars Q)

w = {9, 24, 16, 16, 49, 82}

w = {1, 2, 1, 2, 2, 1}
I = getIdeal(w, for i from 1 to 6 list random(1, 100))
degree I
polys = first entries RtoQ gens I 
netList solveSystem polys
L = solveSystem polys

P = CC[p_1 .. p_6]
map(Q, P, {w_0*q_1, w_1*q_1*q_2, w_2*q_1*q_2^2, w_3*q_1*q_3, w_4*q_1*q_2*q_3, w_5*q_1*q_3^2})
L0 = coordinates L_0
subPoint = L -> (
    {w_0*L_0, w_1*L_0*L_1, w_2*L_0*L_1^2, w_3*L_0*L_2, w_4*L_0*L_1*L_2, w_5*L_0*L_2^2}
    )

netList subPoint coordinates L_0
netList subPoint coordinates L_1
netList subPoint coordinates L_2


-----------------------------------
-- The start of more general code:

w = {1, 2, 1, 2, 2, 1}
u = for i from 1 to 6 list random(1, 100)
A = matrix {
    {1, 1, 1, 1, 1, 1}, 
    {0, 1, 2, 0, 1, 0},
    {0, 0, 0, 1, 1, 2}
    }

R = QQ[for i from 1 to numRows A list t_i]
g = -1 + sum for i from 0 to numColumns A - 1 list w_i * product for j from 1 to numRows A list t_j^(A_(j-1, i))

M = A * transpose matrix {u} | transpose matrix {for i from 1 to numRows A list t_i * diff(t_i, g)}
I = minors(2, M) + ideal g
degree I



MLIdeal = method(
    Options => {
	minRandomValue => 10,
	maxRandomValue => 99
	}
    )
MLIdeal(Matrix, List, List) := opts -> (A, w, u) -> (
    n := numColumns A;
    d := numRows A;
    assert(n == #w);
    assert(n == #u);
    R := QQ[for i from 1 to d list t_i];
    g := -1 + sum for i from 0 to n-1 list w_i * product for j from 0 to n-1 list R_j^(A_(j,i));
    M := A * transpose matrix {u} | transpose matrix {for j from 0 to n-1 list R_j * diff(R_j, g)};
    minors(2, M) + ideal g
    )

-- random u
MLIdeal(Matrix, List) := opts -> (A, w) -> (
    n := numColumns A;
    u := for i from 1 to n list random(opts.minRandomValue, opts.maxRandomValue);
    MLIdeal(A, w, u)
    )

degree MLIdeal(A, {1,1,1,1,1,1}) 
