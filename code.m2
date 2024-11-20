-- Macaulay2 tutorial

---------------------
-- Using the Shell --
---------------------

-- arithmetic

1+1

3/5 + 7/12

n = 2^607 - 1

isPrime n

isPrime o1


-- rings and polynomials

R = QQ[x,y,z]

x > y -- all rings come with term orders

x^2 > y^3

describe R -- show more details about R

R = QQ[x,y,z, MonomialOrder => Lex]

x^2 > y^3

f = (x-1)^3 - (y-1)^3

factor f

R = QQ[x,y,z, MonomialOrder => {Weights => {1,2,0}}]

f = (x-1)^3 - (y-1)^3

sub(f, {x => 2, y => 2})
sub(f, {x => 1})

ZZ -- integers

ZZ[x,y,z]

S = ZZ/3[x,y,z]

f -- still belongs to R
sub(f, S)

factor sub(f, S)

RR -- Real Field (inexact)

pi

pi_RR

RR_100

pi_(RR_200)


-- ideals and quotients

R = QQ[x,y,z]
f = (x-1)^3 - (y-1)^3

I = ideal(f, z^3 - x*y^2, x*z - y^2)

gens I

dim I

isPrime I

primaryDecomposition I

netList oo

netList associatedPrimes I

netList for P in associatedPrimes I list {dim P, degree P, P}


Q = R/I

-- elements in Q are displayed in their normal form w.r.t. I
f_Q

z^3

x^3


-- Groebner bases

use R

f

f % (x^3 + 3*x^2) -- division algorithm see: "Matrix % Matrix"

G = gb I -- produces a gb object

help "gb"

gens gb I

gens gb(I, Algorithm => "Homogeneous")

transpose gens gb I

leadTerm I


-- Resolutions

res I -- behaviour is different on web

(res I).dd

betti res I

-- https://macaulay2.com/GettingStarted/

P = ZZ/32003[x_1 .. x_20]

J = Grassmannian(2, 5, P) --Gr(3,6)
betti res J

res J -- don't do this on web


-- output to file

f = "output.txt"

f << toString gens I << endl

f << toString gens gb J << endl

f << close

help "creating and writing files"


---------------------------------------
-- Objects and keywords in Macaulay2 --
---------------------------------------

-- code

-- value = (Expression; Expression; .. ; Expression; Return value)

n = (
  i = 10;
  j = 100;
  (i+j)^2
  )


-- lists and sequences (immutable)

L = {1,2,3}
L_1
L#0
#L

L = {{1,2}, {3}, {4,5,6}, {7,8,9}, {{10, 11}, {12}}}
flatten L
first L

associatedPrimes I
netList oo

apply(associatedPrimes I, dim)
dim \ associatedPrimes I

1  .. 10
(3 : 4)
x_1 .. x_10

toList(1 .. 10)
toList(3 : 4)


-- if and loops

a = 1
b = 2

if 2*a == b then print "yes" else print "no"

if 2*a != b then (
    -- do stuff
    1
    ) else (
    -- do other stuff
    2
    )


for i from 0 to 10 do print("done " | toString i)

S = for i from 0 to 10 list i^2

for i in S do print i

for P in associatedPrimes I list (dim P, degree P, leadTerm P)


i = 0

while i < 10 do (print i; i = i+1)

while i > 0 list (i = i-1; i)

help "for"
help "while"


-- hash tables

H = hashTable {a => 1, b => 2}

H#a

data = for i from 1 to 1000 list random(1, 6) + random(1, 6);
T = tally data -- Tally is a type of hashtable
T#2

ancestors Tally


H' = new MutableHashTable

H'#a = 1

H'#b = 2

H'

peek H'


-- mutable lists

L = new MutableList from {1,2,3}

L#3 = L

peek L


-- matrices

A = matrix {{1,1},{1,0}}

for i from 1 to 9 do print(toString i | ": " | net A^i | "\n\n")

mat = matrix(ZZ/2, {{1,1,0},{1,0,1}})

source mat

mat_{1,2} -- columns 1 and 2 (note: first column is 0)

mat^{1} -- row 1

ker mat

reducedRowEchelonForm mat


R = QQ[x,y,z]

A = matrix {{x, y}, {z, 1}}

A^2

ring A -- every matrix is over a ring

entries A

A | A^2 -- matrices joined side-by-side

A || A^2 -- stacked matrices


-- maps between rings

restart

R = QQ[for s in subsets(6, 3) list p_(toSequence s)]

S = QQ[x_(1,1) .. x_(3,6)]

gens R
gens S

X = transpose genericMatrix(S, 6, 3)

m = map(S, R, for s in subsets(6, 3) list det X_s)

I = ker m; -- pluecker ideal

transpose mingens I

dim I


-- functions

f = n -> n^2

collatz = n -> (
  if n == 1 then {1}
  else if n % 2 == 0 then {n} | collatz(n//2)
  else {n} | collatz(3*n+1)
  )

collatz 3

collatz(837799);

L = {1,2,3,4}

f \ L


-- method functions

unitCube = method()
unitCube(ZZ) := d -> (
  if d <= 0 then error("expected dimension at least 1");
  if d == 1 then matrix {{0, 1}}
  else (
    C := unitCube(d-1);
    (matrix {toList(2^(d-1) : 0)} || C) | (matrix {toList(2^(d-1) : 1)} || C)
  )
)

unitCube 3

unitCube "a"

methods unitCube

unitCube(QQ) := q -> (
    error("I don't know how to do that ...");
    )

unitCube (1/2)

methods unitCube


-------------------
-- Help yourself --
-------------------

---- no :( I want you to help me



help "help"

methods unitCube

code 0

methods primaryDecomposition

code 1


---------------
-- Exercises --
---------------

-- Language Exercises --

-*

0. Find the help page that explains 'continue'. Copy and modify the first example so that it prints the numbers 1 to 10 and returns a the odd numbers between 1 and 10

1. List the first 100 prime numbers
[hint: define a variable: numberOfPrimes = 0, and use a while loop: while numberOfPrimesFound < 100 list (...) ]

2. Compute the 2024th Fibonacci number
[hint: use the matrix: matrix {{1,1},{1,0}} ]

3. write a function startsWithX that takes a string s and outputs true if the first character of s is the letter "x" otherwise it returns false
[hint: strings can be indexed using underscores]
[corner case: does your function work with the empty string?]

4. Use the packages "Graphs" and "Matroids" to count the number of maximal chains of flats of the graphic matroid of the complete graph on 5 vertices
[hint: use 'needsPackage' to load each package. Use the help to find out how to produce the complete graph and how to make a matroid from a graph.
Then use the functions 'latticeOfFlats' and 'chains' to count the number of chains. Note that maximal length chains have length one more than the rank of matroid]

5. Make a function randomMatrix that takes an integer n and produces an n by n matrix whose entries are random elements of ZZ/2

*-

-- Working with polynomials --

-*

6. Make a ring with 5 variables x_1 .. x_5 and a term order such that x_1 > x_2 > .. > x_5 and x_1^2 > x_2^3
[hint: x_1 .. x_5 makes 5 variables and remember the optional parameter 'MonomialOrder => ...' - also try a Lexicographic order]

7. Show that the ideal generated by y-x^2 and z-x^3 contains the polynomial z-xy


8. Define the polynomials f_1 = x+y+z, f_2 = xy+xz+yz, f_3 = xyz. Determine how to write g = x^3 + y^3 + z^3 as a polynomial combination of f1, f2, f3.
[hint: define a ring QQ[x,y,z, u_1, u_2, u_3] and an ideal I generated by {u_i - f_i : i = 1,2,3}. Write g in 'normal form' with respect to I using g % I]
[follow up: if you used the hint, why does this work?]


9. Let X = (x_ij) be a 3x3 matrix of variables and I be the ideal generated by the 2x2 minors of X. Show that I is a prime ideal. Find an initial ideal of I. Bonus: how many different initial ideals of I are there?
[hint: lookup the function 'genericMatrix', 'minors', 'isPrime', and 'leadTerm']
[hint for bonus: the package 'gfanInterface' can compute the 'gfan' of an ideal]

*-


--------------
-- Projects --
--------------

-- Maximum Likelihood Degrees --
-- Check some of my old code - how can it be generalised
-- Can we compute the Likelihood correspondence for some small example, e.g., for independence models

-- Polyhedra package:
-- Ehrhart series
-- Ehrhart delta-vector
-- equivariant Ehrhart series for Symmetric group actions (Character table is available in BettiCharacter package)
-- Questions: Can we use Normaliz for these computations?


-- [Markov bases]
-- ennumeration of all Markov bases of a toric ideal
<<<<<<< HEAD
=======




-- hi from ollie:
-- kill: crtl-x crtl-c
-- save: crtl-x crtl-s
>>>>>>> 2eef146fc7ba8859e961b54145ecb243270392a2
