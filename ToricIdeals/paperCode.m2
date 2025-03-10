
---------------------
-- 1. Introduction --
---------------------

needsPackage "AllMarkovBases";

A = matrix "7,8,9,10";
countMarkov A
markovBases A

A' = matrix "51,52,53,54,55,56";
countMarkov A'
randomMarkov A'

R = QQ[x_1 .. x_6];
randomMarkov(A', R)

toricIndispensableSet A'
toricUniversalMarkov A'

A'' = matrix {{1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1},
    {1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0},
    {1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0},
    {0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,0,0,0},
    {1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0},
    {0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0}};

elapsedTime countMarkov A''
elapsedTime toricIndispensableSet A'';
elapsedTime toricUniversalMarkov A'';

---------------------
-- 2. How it works --
---------------------

needsPackage "FourTiTwo";

A = matrix "1,2,3";
M = toricMarkov A

needsPackage "AllMarkovBases";
fiberGraph A

markovBases A

pruferSequence {0,0,2,4}

randomMarkov(A, NumberOfBases => 1)

toricUniversalMarkov A
toricIndispensableSet A

R = QQ[x, y, z];
markovBases(A, R)
randomMarkov(A, R)
toricIndispensableSet(A, R)

gens toricUniversalMarkov(A, R)
