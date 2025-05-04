newPackage(
    "AllMarkovBases",
    Version => "1.0",
    Date => "December 16, 2024",
    Headline => "package for computing all minimal Markov bases
    of a configuration matrix",
    Authors => {
        {Name => "Alexander Milner",
            Email => "A.J.C.Milner@sms.ed.ac.uk",
            HomePage => "https://alexandermilner.github.io/"},
        {Name => "Oliver Clarke",
            Email => "oliver.clarke@durham.ac.uk",
            HomePage => "https://www.oliverclarkemath.com/"}
        },
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"FourTiTwo","Graphs","TensorComplexes","Polyhedra","Posets","SubalgebraBases","LLLBases","Normaliz"}
    )

-------------
-- Exports --
-------------

export {
    "pruferSequence",
    "markovBases",
    "randomMarkov",
    "NumberOfBases",
    "AlwaysReturnList",
    "fiberGraph",
    "ReturnConnectedComponents",
    "fiber",
    "toricIndispensableSet",
    "ReturnFiberValues",
    "toricUniversalMarkov",
    "computeFiber"
    }

----------
-- Code --
----------



--normaliz2 = profile normaliz



-- computes one fiber
computeFiber = method(
    Options => {
        ReturnConnectedComponents => false,
	Algorithm => "groebner" -- "groebner" (better for simpler matrices), "markov" (better for more complicated matrices) or "lattice" using the Normaliz algorithm
        }
    );
computeFiber (Matrix,Matrix) := opts -> (A, b) -> (
    if not A.cache#?"MarkovBasis" then setupFibers A;
    val := flatten entries b;
    if opts.ReturnConnectedComponents and opts.Algorithm =="lattice" then error("Lattice algorithm won't compute connected components");
    if opts.Algorithm == "lattice" and not (A.cache#"fibers")#?val then(
	u:={};
	for row in entries toricMarkov (b | A) do(
	    r := drop(row,1);
	    if row#0 == 1 and all(r,z->z<=0) then (u = {-r}; break;);
	    );
	(A.cache#"fibers")#val = if #u==0 then set{} else set latticePointsFromMoves(transpose A.cache#"MarkovBasis",transpose matrix u);
	)else if not (A.cache#"fibers")#?val or (opts.ReturnConnectedComponents and not (A.cache#"fibers")#?val) then(
	if opts.Algorithm == "groebner" then(
	    A.cache#"Ring" = ZZ(monoid[Variables => numRows A + numColumns A]);
	    A.cache#"RingGenerators" = gens A.cache#"Ring";
	    A.cache#"toricIdeal"=toricGroebner(id_(ZZ^(numRows A)) | A, A.cache#"Ring");
	    );
	if (A.cache#"fiberStarters")#?val and opts.ReturnConnectedComponents then (
	    if opts.Algorithm == "markov" then ccFibersM(A,val) else ccFibersG(A,val);
	    )else (
	    if opts.Algorithm == "markov" then fibRecursionM(A,val) else fibRecursionG(A,val);
	    );
	);
    if opts.ReturnConnectedComponents then (
	if (A.cache#"fiberStarters")#?val then (A.cache#"fiberComponents")#val else {toList (A.cache#"fibers")#val}
	)else(
	toList (A.cache#"fibers")#val
	)
    );

-- recursive method using groebner bases (unexported)
fibRecursionG = method();
fibRecursionG (Matrix,List) := (A, val) -> (
    out := union for val2 in keys A.cache#"fiberStarters" list(
	if not (val2 << val) then continue;
	if val2==val and (A.cache#"fiberStarters")#?val then continue (A.cache#"fiberStarters")#val;
	resid := val-val2;
	if not (A.cache#"fibers")#?resid then fibRecursionG(A,resid);
	if #((A.cache#"fibers")#resid) == 0 then continue;
	if not (A.cache#"fibers")#?val2 then fibRecursionG(A,val2);
	fibAdd((A.cache#"fibers")#val2,(A.cache#"fibers")#resid)
	);
    if #out==0 then(
        e:=first exponents (product(for i from 0 to #val-1 list ((A.cache#"RingGenerators")#i)^(val#i)) % A.cache#"toricIdeal");
	if take(e,numRows A) == toList((numRows A):0) then out = set{take(e,-numColumns A)};
	);
    (A.cache#"fibers")#val = out;
    );


-- recursive method using Markov bases method (unexported)
fibRecursionM = method();
fibRecursionM (Matrix,List) := (A, val) -> (
    out := union for val2 in keys A.cache#"fiberStarters" list(
	if not (val2 << val) then continue;
	if val2==val and (A.cache#"fiberStarters")#?val then continue (A.cache#"fiberStarters")#val;
	resid := val-val2;
	if not (A.cache#"fibers")#?resid then fibRecursionM(A,resid);
	if #((A.cache#"fibers")#resid) == 0 then continue;
	if not (A.cache#"fibers")#?val2 then fibRecursionM(A,val2);
	fibAdd((A.cache#"fibers")#val2,(A.cache#"fibers")#resid)
	);
    if #out==0 then(
	for row in entries toricMarkov matrix{{transpose matrix {val},A}} do(
	    r := drop(row,1);
	    if row#0 == 1 and all(r,z->z<=0) then (out = set{-r}; break;);
	    );
	);
    (A.cache#"fibers")#val = out;
    );




ccFibersG = method();
ccFibersG (Matrix,List) := (A,val) -> (
    out := for val2 in keys A.cache#"fiberStarters" list(
	if not (val2 << val) then continue;
	if val2==val and (A.cache#"fiberStarters")#?val then continue (A.cache#"fiberStarters")#val;
	resid := val-val2;
	if (A.cache#"fiberStarters")#?resid then(
	    )else(
	    );
	if not (A.cache#"fibers")#?resid then fibRecursionG(A,resid);
	if #((A.cache#"fibers")#resid) == 0 then continue;
	if not (A.cache#"fibers")#?val2 then fibRecursionG(A,val2);
	fibAdd((A.cache#"fibers")#val2,(A.cache#"fibers")#resid)
	);
    local output;
    (A.cache#"fiberComponents")#val = output;
    (A.cache#"fibers")#val = flatten output;
    );



ccFibersM = method();
ccFibersM (Matrix,List) := (A,val) -> (
    out := union for val2 in keys A.cache#"fiberStarters" list(
	if not (val2 << val) then continue;
	if val2==val and (A.cache#"fiberStarters")#?val then continue (A.cache#"fiberStarters")#val;
	resid := val-val2;
	if (A.cache#"fiberStarters")#?resid then(
	    )else(
	    );
	if not (A.cache#"fibers")#?resid then fibRecursionM(A,resid);
	if #((A.cache#"fibers")#resid) == 0 then continue;
	if not (A.cache#"fibers")#?val2 then fibRecursionM(A,val2);
	fibAdd((A.cache#"fibers")#val2,(A.cache#"fibers")#resid)
	);
    local output;
    (A.cache#"fiberComponents")#val = output;
    (A.cache#"fibers")#val = flatten output;
    );




fibAdd = method();
fibAdd (Set,Set) := (L1,L2) -> (
    set flatten for l1 in keys L1 list for l2 in keys L2 list l1+l2
    );

fiberAdditionConnected = method();
fiberAdditionConnected (List,List) := (L1,L2) -> (
    unique flatten for l1 in L1 list for l2 in L2 list l1+l2
    );




computeFiberLattice = method();
computeFiberLattice (Matrix,Matrix) := (A, b) -> (
    M := if A.cache#?"MarkovBasis" then A.cache#"MarkovBasis" else toricMarkov A;
    u:={};
    for row in entries toricMarkov (b | A) do(
	r := drop(row,1);
	if row#0 == 1 and all(r,z->z<=0) then (u = {-r}; break;);
	);
    if #u==0 then {} else latticePointsFromMoves(transpose M,transpose matrix u)
    );



fiberGraph = method(
    Options => {
        ReturnConnectedComponents => false,
        Algorithm => "graph", -- "decompose","lattice","fast"(RECOMMENDED),"graph"
        }
    );
fiberGraph Matrix := opts -> A -> (
    if not A.cache#?"MarkovBasis" then setupFibers A;
    if opts.ReturnConnectedComponents then(
	if not A.cache#"componentsComputed" then (
	    if opts.Algorithm == "fast" then fastFiberGraphInternal A
	    else if opts.Algorithm == "lattice" then latticeFiberGraph A
	    else if opts.Algorithm == "decompose" then decomposeFiberGraph A
	    else if opts.Algorithm == "graph" then graphicFiberGraph A
	    else error("unknown option for Algorithm");
	    A.cache#"componentsComputed" = true;
	    );
	) else (if #(values A.cache#"fiberGraphs")==0 then (
	    graphicFiberGraph A;
	    ) else A.cache#"fiberGraphs"
	);
    if opts.ReturnConnectedComponents then values A.cache#"fiberComponents" else values A.cache#"fiberGraphs"
    );



-- computes Markov Basis and hence fiber starters for A (unexported)
setupFibers = method();
setupFibers Matrix := A -> (
    A.cache#"MarkovBasis" = toricMarkov A;
    if A.cache#"MarkovBasis" == 0 then error("No Markov bases for the input matrix");
    fiberStarters := new MutableHashTable;
    fiberValues := new MutableHashTable;
    for basisElement in entries A.cache#"MarkovBasis" do(
	if (all(basisElement, z -> z >= 0) or all(basisElement, z -> z <= 0)) then error("Semigroup associated to input matrix is not pointed");
        elPos := for coord in basisElement list(if coord >= 0 then coord else 0);
        elNeg := elPos - basisElement;
        fiberVal := flatten entries (A * transpose matrix{elPos});
        if fiberStarters#?fiberVal then (
	    fiberStarters#fiberVal = union(fiberStarters#fiberVal, set{elPos,elNeg});
	    )else fiberStarters#fiberVal = set{elPos,elNeg};
	fiberValues#basisElement = fiberVal;
	);
    A.cache#"fiberStarters" = new HashTable from fiberStarters;
    A.cache#"fiberValues" = new HashTable from fiberValues;
    A.cache#"fibers" = new MutableHashTable from {{toList((numRows A):0),set {toList((numColumns A):0)}}};
    A.cache#"fiberComponents" = new MutableHashTable;
    A.cache#"componentsComputed" = false;
    A.cache#"fiberGraphs" = new MutableHashTable;
    );

--computes poset of generating fiber values (unexported)
setupPoset = method();
setupPoset Matrix := A -> (
    if not A.cache#?"MarkovBasis" then setupFibers A;
    A.cache#"fiberPoset" = poset(keys A.cache#"fiberStarters",(x,y) -> x<<y);
    );







--Algorithm 3: decompose fiber into smaller fibers
decomposeFiberGraph = method();
decomposeFiberGraph Matrix := A -> (
    fiber:={};
    starterMB := entries A.cache#"MarkovBasis";
    fiberStarters := new MutableHashTable;
    for basis in starterMB do(
        elPos := for coord in basis list(if coord >= 0 then coord else 0);
        elNeg := elPos - basis;
        fiberVal := flatten entries (A * transpose matrix{elPos});
        if fiberStarters#?fiberVal then (fiberStarters#fiberVal)##(fiberStarters#fiberVal) = {elPos,elNeg} else fiberStarters#fiberVal = new MutableList from {{elPos,elNeg}};
        );
    finalR := new MutableHashTable;
    for val in keys fiberStarters do(
        buildFiber := flatten toList fiberStarters#val;
        finalR#val = (v -> {v}) \ (unique buildFiber);
        fiberStarters#val = {set buildFiber};
        );
    if not A.cache#?"fiberStartersDep" then A.cache#"fiberStartersDep" = fiberStarters;
    local fiberValuesPoset;
    if fiber == {} then (fiberValuesPoset = poset(keys fiberStarters,(x,y) -> x<<y);)
    else (
        snippedStarters := for starter in keys fiberStarters list(if starter << fiber then starter else continue);
        fiberValuesPoset = poset(toList(set snippedStarters + set {fiber}),(x,y) -> x<<y);
        );
    fibersLeft := new MutableList from fiberValuesPoset#GroundSet;
    tempPoset := fiberValuesPoset;
    local R;
    local rvs;
    while #fibersLeft>0 do(
        for minimalElement in minimalElements tempPoset do(
            remove(fibersLeft,position(toList fibersLeft,z -> z==minimalElement));
            A.cache#"current" = minimalElement;
            rvs = drop(sort principalOrderIdeal(fiberValuesPoset,minimalElement),-1);
            if minimalElement != fiber and #rvs == 0 then continue;
            if finalR#?minimalElement then (
                R = integrateLists(recursiveFiber(minimalElement,rvs,A),(v -> set toList v) \ finalR#minimalElement);
                )
            else R = recursiveFiber(minimalElement,rvs,A);
            finalR#minimalElement = (v -> toList v) \ R;
            (A.cache#"fiberStartersDep")#minimalElement = {union R};
            );
        tempPoset = subposet(fiberValuesPoset,toList fibersLeft);
        );
    for val in keys finalR do (A.cache#"fiberComponents")#val = finalR#val;
    );



-- addition of fibers (unexported)
fiberAdd = method();
fiberAdd (Set,Set) := (C,D) -> (
    {set flatten for p in keys C list for q in keys D list p+q}
    );

-- recursive method 2 (unexported)
recursiveFiber = method();
recursiveFiber (List, List, Matrix) := (val, rvs, A) -> (
    local output;
    residVals := for i from 0 to #rvs - 1 list(
	resid := val-rvs#i;
	if not all(resid,z -> z>=0) then continue;
	output := fiberAdd(union recursiveFiber(resid, rvs_{0..i}, A), ((A.cache#"fiberStartersDep")#(rvs#i))#0);
	if output == {set{}} then continue else output
	);
    if #residVals > 0 then fold(residVals,integrateLists)
    else if (A.cache#"fiberStartersDep")#?val and (A.cache#"current" != val) then (A.cache#"fiberStartersDep")#val
    else endFiber(val,A)
    );

-- method to handle end of recursion (unexported)
endFiber = method();
endFiber (List, Matrix) := (val, A) -> (
    output := {set{}};
    for row in entries toricMarkov matrix{{transpose matrix {val},A}} do(
	r := drop(row,1);
	if row#0 == 1 and all(r,z->z<=0) then (output = {set{-r}}; break;);
	);
    (A.cache#"fiberStartersDep")#val=output;
    output
    );


-- method to glue fibers together (unexported)
integrateLists = method();
integrateLists (List,List) := (L1, L2) -> (
    L1 = new MutableList from L1;
    L2 = new MutableList from L2;
    for i from 0 to #L1 - 1 do(
	for j from 0 to #L2 - 1 do(
	    if #(L1#i * L2#j)>0 then (
		u := L1#i + L2#j;
		L1#i = u;
		L2#j = u;
		);
	    );
	);
    unique ((toList L1) | (toList L2))
    );







--Algorithm 2: lattice points (note: A must have full rank
latticeFiberGraph = method();
latticeFiberGraph Matrix := A -> (
    starterMB := transpose A.cache#"MarkovBasis";
    n := numColumns A;
    d := numRows A;
    k := numColumns starterMB;
    fiberStarters := new MutableHashTable;
    fiberValues := new MutableHashTable;
    for i from 0 to k - 1 do(
	basisElement := starterMB_{i};
        elPos := transpose matrix{for j from 0 to n-1 list(if basisElement_(j,0) >= 0 then basisElement_(j,0) else 0)};
	elNeg := elPos - basisElement;
        fiberVal := flatten entries (A * elPos);
	if fiberStarters#?fiberVal then (fiberStarters#fiberVal)##(fiberStarters#fiberVal) = {elPos,elNeg} else fiberStarters#fiberVal = new MutableList from {{elPos,elNeg}};
        fiberValues#basisElement = fiberVal;
        );
    for val in keys fiberStarters do(
	buildFiber := (v -> flatten entries v) \ unique flatten toList fiberStarters#val;
	starter := fiberStarters#val#0#0;
	validIndexes := for i from 0 to k-1 list if fiberValues#(starterMB_{i}) << val then i else continue;
	snippedMB := submatrix(starterMB,validIndexes);
	finalR := (v -> new MutableList from {v}) \ buildFiber;	
        lPs := latticePointsFromMoves(snippedMB,starter);
	print("-- got the lattice points");
	lPs = new MutableList from lPs - set buildFiber;
 	local reset;
 	while #lPs>0 do(
 	    for point in lPs do(
 		reset=false;
 		for i from 0 to #buildFiber-1 do(
 		    if reset then break;
 		    for el in finalR#i do(
 		        if reset then break;
 			if (not all(point,el,(y,z) -> y==0 or z==0)) and point != el then (
 			    (finalR#i)##(finalR#i) = point;
 			    remove(lPs,position(toList(lPs),z -> z == point));
 			    reset=true;
 			    );
 			);
 		    );
 		);
 	    );
	(A.cache#"fiberComponents")#val = (v -> toList v) \ finalR
	);
    
    );


-- uses Normaliz to compute lattice points (unexported)
latticePointsFromMoves = method();
latticePointsFromMoves(Matrix, Matrix) := (I, v) -> (
    M := I | v;
    normalizOutput := normaliz2(M, "inhom_inequalities");
    normalizOut := transpose normalizOutput#"gen"_{0..(numColumns normalizOutput#"gen")-2};
    for i from 0 to numColumns normalizOut - 1 list flatten entries (I*(normalizOut_{i})+v)
    );


-- use Normaliz to comptue the points in a fiber
-- A is the matrix of the toric ideal
-- v if the fiber:
-- return all point in \NN^n \cap \{x : Ax = Av\}
pointsInFiber = method();
pointsInFiber(Matrix, Matrix) := (A, v) -> (
    n := numColumns A;
    I := id_(ZZ^n);
    O := transpose matrix {toList(n : 0)};
    M := (I | O) || (A | -v);
    normaliz2(M, "inhom_inequalities")
    );






--Algorithm 1: faster fiberGraph
--returns connected components and stores them in A.cache

fastFiberGraphInternal = method();
fastFiberGraphInternal Matrix := A -> (
    n := numColumns A;
    for val in keys A.cache#"fiberStarters" do(
	buildFiber := toList (A.cache#"fiberStarters")#val;
        validMoves := for move in entries A.cache#"MarkovBasis" list if ((A.cache#"fiberValues")#move << val) and ((A.cache#"fiberValues")#move != val) then move else continue;
        validMoves = new MutableHashTable from ((v -> {v,true}) \ validMoves);
        (A.cache#"fiberComponents")#val = for i from 0 to #buildFiber - 1 list(
            cc := set {buildFiber#i};
            lenCC := 0;
            movesUnused := for kvs in pairs validMoves list if kvs#1 then kvs#0 else continue;
            while lenCC != #cc do(
                lenCC = #cc;
                for move in movesUnused do(
                    cc = set flatten for el in keys cc list(
                        flatten for checkIndex in {1,0,-1} list(
                            if checkIndex == 0 then continue {el};
                            n := checkIndex;
                            while all(el+n*move, z -> z >= 0) list (el+n*move) do (validMoves#move = false; n = n + checkIndex)
                            )
                        );
                    );
                );
            toList cc
            )
        );
    );



-- Algorithm 0: uses Graphs package to compute the connected components of fiber graphs
-- returns a list of graphs

graphicFiberGraph = method();
graphicFiberGraph Matrix := A -> (
    starterMarkovBasis := A.cache#"MarkovBasis";
    n := numColumns A;
    fiberStarters := new MutableHashTable;
    possibleMoves := new MutableList;
    for i from 0 to numRows starterMarkovBasis - 1 do(
        starterFiberElement := for j from 0 to n-1 list(if starterMarkovBasis_(i,j)>=0 then starterMarkovBasis_(i,j) else 0);
        fiberValue := A * transpose matrix{starterFiberElement};
        if not fiberStarters#?fiberValue then fiberStarters#(flatten entries fiberValue) = starterFiberElement;
        validMove := flatten entries starterMarkovBasis^{i};
        possibleMoves##possibleMoves = validMove;
        possibleMoves##possibleMoves = - validMove;
        );
    for starterFiberElement in pairs fiberStarters do(
        queueOfFiberElements := new MutableList from {starterFiberElement#1};
        adjacencyMatrixIndex := new MutableHashTable from {starterFiberElement#1 => 0};
        adjacencyMatrix := matrix("0");
        fiberSize := 1;
        while #queueOfFiberElements != 0 do(
            currentFiberElement := queueOfFiberElements#0;
            for move in possibleMoves do(
                testFiberElement := move + currentFiberElement;
                if (all(testFiberElement, z -> z>=0) and not adjacencyMatrixIndex#?testFiberElement) then (
                    queueOfFiberElements##queueOfFiberElements=testFiberElement;
                    intersectionIndex := mutableMatrix(ZZ,1,fiberSize);
                    for keyVals in pairs adjacencyMatrixIndex do(
                        if (not all(testFiberElement, keyVals_0,(y,z) -> y<=0 or z<=0)) then (
                            intersectionIndex_(0,keyVals_1) = 1
                            );
                        );
                    intersectionIndex = matrix intersectionIndex;
                    adjacencyMatrix = matrix{{adjacencyMatrix, transpose intersectionIndex}, {intersectionIndex, matrix{{0}}}};
                    adjacencyMatrixIndex#testFiberElement = fiberSize;
                    fiberSize = fiberSize + 1
                    );
                );
            remove(queueOfFiberElements,0);
            );
        orderedAdjacencyMatrixIndex := new MutableList from toList(numColumns adjacencyMatrix:0);
        for l in keys adjacencyMatrixIndex do orderedAdjacencyMatrixIndex#(adjacencyMatrixIndex#l)=l;
	outG := graph(toList orderedAdjacencyMatrixIndex, adjacencyMatrix);
	(A.cache#"fiberGraphs")#(starterFiberElement#0) = outG;
	(A.cache#"fiberComponents")#(starterFiberElement#0) = connectedComponents outG;
        );
    );






pruferSequence = method();
pruferSequence List := L -> (
    numberOfNodes := #L + 2;
    edgeList := new MutableList;
    nodeDegrees := new MutableList from toList(numberOfNodes : 1);
    for j in L do(
        nodeDegrees#j = nodeDegrees#j + 1;
        );
    for j in L do(
        for node from 0 to numberOfNodes - 1 do(
            if nodeDegrees#node == 1 then(
                edgeList##edgeList = set {node, j};
                nodeDegrees#j = nodeDegrees#j - 1;
                nodeDegrees#node = nodeDegrees#node - 1;
                break;
                );
            );
        );
    edgeList##edgeList = set positions(nodeDegrees, x -> x==1);
    toList edgeList
    );


-- direct product of lists (unexported)
listProd = method();
listProd List := L -> (
    fold(
        (combinedLists, listToBeAdded) -> (
            flatten for combinedElement in combinedLists list (
                for newElement in listToBeAdded list (
                    append(combinedElement, newElement)
                    )
                )
            ),
        {{}},
        L)
    );


-- sortMarkov takes a list L of elements of a minimal Markov basis of a matrix A
-- and returns a minimal Markov basis of elements whose first non-zero entry is positive
-- the elements are then sorted by fiber, which are sorted lexicographically (E.g. sort subsets(4, 2))
sortMarkov = method()
sortMarkov(List, Matrix) := (L, A) -> (
		L = (rsort(L | -L))_{0 .. #L -1};
		sort(L, x -> first entries transpose sum for i from 0 to #x -1 list if x_i > 0 then x_i * A_{i} else continue)
		)

markovBases = method();
markovBases Matrix := A -> (
		allFibersConnectedComponents := fiberGraph(A,
				ReturnConnectedComponents => true,
				Algorithm => "fast");
		allFibersSpanningTrees := for fiberConnectedComponents in allFibersConnectedComponents list(
        for pruferList in listProd splice {
            #fiberConnectedComponents - 2 : toList(0..#fiberConnectedComponents-1)
            } list pruferSequence pruferList
        );
    markovBasesAsLists := listProd for k from 0 to #allFibersSpanningTrees-1 list(
        flatten for spanningTree in allFibersSpanningTrees#k list(
						listProd for edge in spanningTree list(
                pairsOfFiberElements := listProd for l in keys edge list allFibersConnectedComponents#k#l;
                for pair in pairsOfFiberElements list pair#0-pair#1
                )
            )
        );
		markovBasesAsLists = sort(apply(markovBasesAsLists, x -> sortMarkov(flatten x, A)));
		for markovBasisAsList in markovBasesAsLists list matrix markovBasisAsList
    );

markovBases(Matrix, Ring) := opts -> (A, R) -> (
    listOfBases := markovBases(A, opts);
    apply(listOfBases, B -> toBinomial(B, R))
    )


randomMarkov = method(
    Options => {
        NumberOfBases => 1,
        AlwaysReturnList => false
        }
    );


randomMarkov Matrix := opts -> A -> (
    allFibersConnectedComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        Algorithm => "fast");
    randomMarkovBases := for i from 0 to opts.NumberOfBases - 1 list(
        allFibersRandomSpanningTree := for fiberConnectedComponents in allFibersConnectedComponents list(
            pruferSequence for j from 1 to #fiberConnectedComponents-2 list random(#fiberConnectedComponents)
            );
        matrix sortMarkov(
						flatten for k from 0 to #allFibersRandomSpanningTree-1 list(
								for edge in allFibersRandomSpanningTree#k list(
										randomPairOfFiberElements := for l in keys edge list allFibersConnectedComponents#k#l#(random(#allFibersConnectedComponents#k#l));
										randomPairOfFiberElements#0-randomPairOfFiberElements#1
										)
								),
						A)
        );
    if (not opts.AlwaysReturnList and opts.NumberOfBases == 1) then randomMarkovBases_0 else randomMarkovBases
    );


randomMarkov(Matrix, Ring) := opts -> (A, R) -> (
    listOfBases := randomMarkov(A, NumberOfBases => opts.NumberOfBases, AlwaysReturnList => true);
    listOfIdeals := apply(listOfBases, B -> toBinomial(B, R));
    if (not opts.AlwaysReturnList and opts.NumberOfBases == 1) then listOfIdeals_0 else listOfIdeals
    );


countMarkov = method(
    Options => {
	Algorithm => "fast"
	}
    )
countMarkov Matrix := opts -> A -> (
    allFibersConnectedComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        Algorithm => opts.Algorithm);
    product for fiberConnectedComponents in allFibersConnectedComponents list(
        k := #fiberConnectedComponents;
        if k==2 then continue #fiberConnectedComponents#0 * #fiberConnectedComponents#1;
        ccSizes := (v -> #v) \ fiberConnectedComponents;
        (product ccSizes) * (sum ccSizes)^(k-2)
        )
    )


toricIndispensableSet = method(
    Options => {
	ReturnFiberValues => false
	}
    );

toricIndispensableSet Matrix := opts -> A -> (
    starterMarkovBasis := toricMarkov A;
    toricIndispensableSet(A,starterMarkovBasis)
    )

toricIndispensableSet (Matrix,Matrix) := opts -> (A,starterMarkovBasis) -> (
    starterMB := entries starterMarkovBasis;
    B := for el in starterMB list(
	elPos := for coord in el list(if coord >= 0 then coord else 0);
	{elPos,elPos - el}
	);
    F := for pair in B list(
	newB := flatten delete(pair,B);
	check0 := all(newB,z -> not all(pair#0-z,y -> y>=0));
	check1 := all(newB,z -> not all(pair#1-z,y -> y>=0));
        check2 := not isMember(pair#0,newB);
	check3 := not isMember(pair#1,newB);
	if check0 and check1 and check2 and check3 then pair#0 - pair#1 else continue
	);
    if not opts.ReturnFiberValues then matrix F
    else for el in F list flatten entries (A * transpose matrix{for coord in el list(if coord >= 0 then coord else 0)})
    );


toricIndispensableSet(Matrix, Ring) := opts -> (A, R) -> (
    indispensableMatrix := toricIndispensableSet A;
    toBinomial(indispensableMatrix, R)
    )


toricUniversalMarkov = method()
toricUniversalMarkov Matrix := A -> (
    fiberComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        Algorithm => "fast");
    matrix flatten for vertexList in fiberComponents list (
        flatten for pairsOfVertices in subsets(vertexList, 2) list (
            for movePairs in listProd pairsOfVertices list (
                movePairs_0 - movePairs_1
                )
            )
        )
    )

toricUniversalMarkov(Matrix, Ring) := (A, R) -> (
    indispensableMatrix := toricUniversalMarkov A;
    toBinomial(indispensableMatrix, R)
    )

-------------------
-- Documentation --
-------------------


beginDocumentation()

doc ///
  Key
    AllMarkovBases
  Headline
    compute all minimal Markov Bases of a toric ideal
  Description
    Text
      Fix a matrix $A = (a_{i,j}) \in \ZZ^{d \times n}$ satisfying
      $\ker(A) \cap (\ZZ_{\ge 0})^n = \{0\}$. The toric ideal $I_A$
      is the kernel of the associated monomial map
      $\phi_A : k[x_1, \dots, x_n] \rightarrow k[t_1, \dots, t_d]$
      given by $\phi(x_i) = t_1^{a_{1,i}} t_2^{a_{2,i}} \dots t_d^{a_{d,i}}$
      for each $i \in [n]$. A Markov basis is a minimal generating
      set for a toric ideal.
      Markov bases are used in Algebraic Statistics in hypothesis testing
      for contingency tables; for further details we refer to:
      M. Drton, B. Sturmfels, and S. Sullivant
      {\bf Lectures on Algebraic Statistics}

      This package computes the set of all minimal Markov bases of a
      given toric ideal $I_A$. We do this by using @TO FourTiTwo@ to
      efficiently compute one Markov basis $M$. We then compute all
      spanning forests of the {\it fiber graph} of $A$ in the
      {\it generating fibers} using the well-known bijection
      of Prüfer. Each spanning forest corresponds to
      a Markov basis, which gives us an efficient way to compute the
      number of Markov bases of $A$ as well as produce the Markov bases.
      For further theoretical details, see
      H. Charalambous, K. Anargyros, A. Thoma
      {\bf Minimal systems of binomial generators and the indispensable
          complex of a toric ideal}.

      Below is an example showing how to compute all Markov bases for
      the matrix $A = (7 \ 8 \ 9 \ 10) \in \ZZ^{1 \times 4}$.

    Example
      A = matrix "7,8,9,10";
      countMarkov A
      netList markovBases A

    Text
      The format of the output follows that of @TO toricMarkov@, so each
      minimal Markov basis is given by a matrix whose rows correspond to
      elements of the Markov basis.

      If the configuration matrix has too many minimal
      Markov bases, then it may be
      convenient to use a random Markov basis.
      This package provides a method to produce a random minimal Markov basis
      that is uniformly sampled from the set of all minimal Markov bases.

    Example
      A = matrix "2,3,5,7,30,31,32";
      countMarkov A
      randomMarkov A

    Text
      The package also provides methods to compute the indispensable set and
      universal Markov basis; see @TO toricIndispensableSet@ and
      @TO toricUniversalMarkov@. These methods exploit the fiber graph to
      compute these respective sets of binomials.

  References
    @UL{
        {"B. Sturmfels.    Groebner bases and Convex Polytopes.
            Volume 8 of ",
            EM "University Lecture Series",
            ". American Mathematical Society, Providence, RI, 1996."
            },
        {"M. Drton, B. Sturmfels, and S. Sullivant.    Lectures on
            Algebraic Statistics.",
            EM "Oberwolfach Seminar Series",
            "39 Basel, Switzerland, Birkhäuser Verlag, 2009."
            },
        {"H. Charalambous, K. Anargyros, and A. Thoma. Minimal
            systems of binomial generators and the indispensable
            complex of a toric ideal. Volume 135 of ",
            EM "Proceedings of the American Mathematical Society",
            "2007."},
        {"Prüfer, H. (1918). Neuer Beweis eines Satzes über Permutationen.",
            EM "Arch. Math. Phys. 27: 742–744."}
        }@

  Subnodes
    randomMarkov
    countMarkov
    fiberGraph
    markovBases
    pruferSequence
    toricIndispensableSet
    toricUniversalMarkov
///


doc ///
  Key
    fiberGraph
    (fiberGraph, Matrix)
    [fiberGraph, ReturnConnectedComponents]
    [fiberGraph, Algorithm]
    ReturnConnectedComponents
  Headline
    generating fibers of a configuration matrix
  Usage
    G = fiberGraph A
  Inputs
    A : Matrix
      configuration matrix
    ReturnConnectedComponents => Boolean
      if true then return the list of connected components
      of each fiber, otherwise return the whole graphs
    Algorithm => String
      either "fast" or "graph": "fast" traverses
      the connected components of the fibers directly; "graph" uses
      the function @TO connectedComponents@ of the package @TO Graphs@.
      Use "fast" only if @TO ReturnConnectedComponents@ is set to @TT "true"@
  Outputs
    G : List
      a list of graphs, one for each generating fiber of A
  Description
    Text
      This function constructs the generating fibers of
      the configuration matrix $A$. The fibers are returned
      as a list of graphs where two vectors in a fiber are
      adjacent if their supports have non-trivial intersection.

      If the option @TO ReturnConnectedComponents@ is @TT "true"@ then,
      instead of returning a list of graphs, the function returns
      a list of the connected components of each fiber. In this
      this case it is recommended to set the option @TO Algorithm@
      to @TT "true"@ as this will speed up the calculation.
    Example
      fiberGraph matrix "3,4,5"
      fiberGraph matrix "1,2,3"
      fiberGraph(matrix "1,2,3",
          ReturnConnectedComponents => true,
          Algorithm => "fast")

  SeeAlso
    markovBases
    AllMarkovBases
///


doc ///
  Key
    pruferSequence
    (pruferSequence, List)
  Headline
    the edge set of a spanning tree corresponding to a Prüfer sequence
  Usage
    E = pruferSequence L
  Inputs
    L : List
      Prüfer sequence, an element of $\{0, \dots, n-1\}^{n-2}
  Outputs
    E : List
      the edge set of the spanning tree corresponding $L$
  Description
    Text
      Cayley's formula in graph theory is the result that the number of
      trees with vertices labelled from $0$ to $n-1$ is $n^{n-2}$. The Prüfer
      sequence of a labelled tree is an element of $\{0, \dots, n-1\}^{n-2}$
      and gives an explicit bijection between the two sets.

      This function produces the edge set of the spanning tree corresponding
      to a given Prüfer sequence.
    Example
      pruferSequence {2}
      pruferSequence {1,3}
      pruferSequence {3,3,3,4}
///


doc ///
  Key
    markovBases
    (markovBases, Matrix)
    (markovBases, Matrix, Ring)
  Headline
    all minimal Markov bases of a configuration matrix
  Usage
    K = markovBases A
    L = markovBases(A, R)
  Inputs
    A : Matrix
      configuration matrix
    R : Ring
      ring with one generator for each column of $A$
  Outputs
    K : List
      the minimal Markov bases A
    L : List
      ideals in R generated by the minimal Markov bases of $A$
  Description
    Text
      This method produces all minimal Markov bases of a
      given configuration matrix $A \in \ZZ^{d \times n}$.
      By default, the output is formatted in the same way
      as @TO toricMarkov@: each Markov basis is a $k \times n$
      matrix whose rows correspond to the elements of the Markov basis.
    Example
      netList markovBases matrix "3,4,5" -- unique Markov basis
      netList markovBases matrix "1,2,3"
      netList markovBases matrix "1,2,3,4"
      netList markovBases matrix "1,2,3,4;4,5,6,7"
    Text
      Similarly to @TO toricMarkov@, we may also specify a ring $R$.
      In this case, the method produces a list of ideals in $R$
      with each ideal generated by a different minimal Markov basis of $A$.
    Example
      markovBases(matrix "1,2,3",QQ[x_1,x_2,x_3])
      gens \ (markovBases(matrix "1,2,3",QQ[x_1,x_2,x_3]))
  SeeAlso
    randomMarkov
///


doc ///
  Key
    countMarkov
    (countMarkov, Matrix)
  Headline
    the number of minimal Markov bases of a configuration matrix
  Usage
    N = countMarkov A
  Inputs
    A : Matrix
      configuration matrix
  Outputs
    N : ZZ
      the number of minimal Markov bases of $A$
  Description
    Text
      This method counts all minimal Markov bases of $A$.
    Example
      countMarkov matrix "3,4,5" -- unique Markov basis
      countMarkov matrix "1,2,3"
      countMarkov matrix "2,3,5,7,30,31,32"
    Text
      This method does not produce all minimal Markov bases, so it is much
      faster to use {\tt countMarkov A} than {\tt #markovBases A}.
  SeeAlso
    markovBases
///


doc ///
  Key
    randomMarkov
    (randomMarkov, Matrix)
    (randomMarkov, Matrix, Ring)
    [randomMarkov, NumberOfBases]
    [randomMarkov, AlwaysReturnList]
    NumberOfBases
    AlwaysReturnList
  Headline
    get a random minimal Markov basis
  Usage
    B = randomMarkov A
    I = randomMarkov(A, R)
  Inputs
    A : Matrix
      the configuration matrix
    R : Ring
      with one generator for each column of $A$
    NumberOfBases => ZZ
      the number of Markov bases to return
    AlwaysReturnList => Boolean
      if true (or NumberOfBases > 1) then returns the result as a list
  Outputs
    B : Matrix
      a random Markov basis of $A$
    I : Ideal
      an ideal in $R$ generated by a random Markov basis of $A$

  Description
    Text
      This method outputs one minimal Markov basis of $A$ chosen
      uniformly at random.
    Example
      randomMarkov matrix "1,2,3,4"
      A = matrix "2,3,5,7,30,31,32"
      randomMarkov A
    Text
      The option @TO NumberOfBases@ allows us specify how many Markov
      bases to return. If this number is greater than one, then the
      function returns a list of Markov bases. Since each Markov basis
      is produced independently, it is possible for the list to contain
      repeats. One may check how many minimal Markov bases exist with
      the function @TO countMarkov@, and the list of all Markov bases
      can be computed with @TO markovBases@. Just like @TO markovBases@,
      we may specify a ring, which produces an ideal whose generating set
      is given by a random minimal Markov basis.
    Example
      A = matrix "2,3,5,7,30,31,32"
      randomMarkov(A, NumberOfBases => 2)
      countMarkov A
      R = ZZ[x_1 .. x_7]
      netList randomMarkov(A, R, NumberOfBases => 2)
  SeeAlso
    markovBases
    countMarkov
///

doc ///
  Key
    toricIndispensableSet
    (toricIndispensableSet, Matrix)
    (toricIndispensableSet, Matrix, Ring)
  Headline
    the indispensable set of toric binomials
  Usage
    S = toricIndispensableSet A
    I = toricIndispensableSet(A, R)
  Inputs
    A : Matrix
      the configuration matrix
    R : Ring
      with one generator for each column of $A$
  Outputs
    S : Matrix
      indispensable set of toric binomials
    I : Ideal
      an ideal in $R$ generated by the indispensable binomials
  Description
    Text
      A binomial $x^u - x^v$ of a toric ideal $I_A$ is called indispensable if
      it belongs to every minimal Markov basis of A.
      The set of all indispensable elements is called the indispensable set,
      and is often denoted with $S(A)$.

      This method computes the indispensable set of a matrix $A$ and returns
      the indispensibles as the rows of a matrix. Similarly to @TO markovBases@,
      if a ring $R$ is supplied, then the result is an ideal generated by
      the indispensable set.
    Example
      A = matrix "7,8,9,10";
      toricIndispensableSet A
      toricIndispensableSet(A, QQ[x_1 .. x_4])
    Text
      The function computes the indispensable elements by checking the connected
      components of the fiber graph of $A$; see @TO fiberGraph@. A fiber
      gives rise to an indispensable element if and only if it has exactly two
      connected components and each component contains a single a single point
      in the fiber.
  SeeAlso
    markovBases
    fiberGraph
///


doc ///
  Key
    toricUniversalMarkov
    (toricUniversalMarkov, Matrix)
    (toricUniversalMarkov, Matrix, Ring)
  Headline
    the universal Markov basis
  Usage
    U = toricUniversalMarkov A
    I = toricUniversalMarkov(A, R)
  Inputs
    A : Matrix
      the configuration matrix
    R : Ring
      with one generator for each column of $A$
  Outputs
    U : Matrix
      the universal Markov basis of $A$
    I : Ideal
      an ideal in $R$ generated by the universal Markov basis of $A$
  Description
    Text
      The universal Markov basis, often denoted $U(A)$, of a configuration
      matrix $A$ is the union of all minimal Markov bases of $A$. This
      method computes the universal Markov basis of $A$ and returns
      the elements as the rows of a matrix. Similarly to @TO markovBases@,
      if a ring $R$ is supplied, then the result is an ideal generated by
      the universal Markov basis.
    Example
      A = matrix "7,8,9,10";
      toricUniversalMarkov A
      toricUniversalMarkov(A, QQ[x_1 .. x_4])
    Text
      The function computes the universal Markov basis elements using the
      the fiber graph of $A$; see @TO fiberGraph@. An irreducible binomial
      $x^u - x^v$ is an element of the universal Markov basis if and only if
      $u$ and $v$ belong to different connected components of the fiber graph.

  SeeAlso
    markovBases
    fiberGraph
///


-----------
-- Tests --
-----------

TEST /// -- unique minimal Markov basis for monomial curve in A^3
assert(
    set flatten ((v -> {v,-v}) \ entries (markovBases matrix "3,4,5")_0)
    ==
    set flatten ((v -> {v,-v}) \ entries toricMarkov matrix "3,4,5")
    )
///

TEST ///
assert(countMarkov matrix "3,4,5" == 1)
///

TEST /// -- two minimal Markov bases for (CI) monomial curve in A^3
result := {
    {{2,-1,0},{3,0,-1}},
    {{2,-1,0},{1,1,-1}}};
assert(
    set((A -> set flatten ((v -> {v,-v}) \ entries A)) \ markovBases matrix "1,2,3")
    ==
    set((A -> set flatten ((v -> {v,-v}) \ A)) \ result)
    )
///

TEST /// -- hypersurface in A^3
result := {{1,-2,1}};
assert(
    set flatten ((v -> {v,-v}) \ entries (markovBases matrix "1,2,3;4,5,6")_0)
    ==
    set flatten ((v -> {v,-v}) \ result)
    )
///

TEST /// -- monomial curve in A^5 with five minimal Markov bases
result := {
    {{-5, 2, 0},{20, 0, -1}},
    {{-5, 2, 0},{15, 2, -1}},
    {{-5, 2, 0},{10, 4, -1}},
    {{-5, 2, 0},{5, 6, -1}},
    {{-5, 2, 0},{0, 8, -1}}};
assert(
    set((A -> set flatten ((v -> {v,-v}) \ entries A)) \ markovBases matrix "2,5,40")
    ==
    set((A -> set flatten ((v -> {v,-v}) \ A)) \ result)
    )
///

TEST ///
result := {{2,0,-1}};
assert(
    set flatten ((v -> {v,-v}) \ entries toricIndispensableSet matrix "2,3,4")
    ==
    set flatten ((v -> {v,-v}) \ result)
    )
///

TEST ///
result := {
    {1, -2, 1, 0},
    {1, -1, -1, 1},
    {0, 1, -2, 1},
    {-3, -1, 1, 2}};
assert(
    set flatten ((v -> {v,-v}) \ entries toricIndispensableSet matrix "7,8,9,10")
    ==
    set flatten ((v -> {v,-v}) \ result)
    )
///

TEST ///
result := {
    {1, -2, 1},
    {2, 0, -1},
    {3, -2, 0}};
assert(
    set flatten ((v -> {v,-v}) \ entries toricUniversalMarkov matrix "2,3,4")
    ==
    set flatten ((v -> {v,-v}) \ result)
    )
///

TEST ///
result := {
    {-4, 0, 2, 1},
    {-4, 1, 0, 2},
    {-3, -1, 1, 2},
    {0, 1, -2, 1},
    {1, -1, -1, 1},
    {1, -2, 1, 0},
    {2, 2, 0, -3},
    {3, 0, 1, -3}};
assert(
    set flatten ((v -> {v,-v}) \ entries toricUniversalMarkov matrix "7,8,9,10")
    ==
    set flatten ((v -> {v,-v}) \ result)
    )
///


end--
restart
needsPackage "AllMarkovBases"
installPackage "AllMarkovBases"

check AllMarkovBases

#markovBases matrix "5,6,7,8,9"
markovBases matrix "5,6,7,8,9"
randomMarkov matrix "5,6,7,8,9"

E2=transpose matrix {{1,0,-3,-5,-7,0,0,0,0,0,0,0,0},
    {0,0,1,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,1,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,1,0,0,0,0,0,0,0,0},
    {0,4,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,5,0,0,0,0,4,3,0,0,0,0,0},
    {0,0,0,0,0,0,7,0,0,0,0,0,0},
    {0,10,0,0,0,0,0,7,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,-1,2024,0,0,0},
    {0,6,0,0,0,0,0,0,2023,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,2023,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,-3,2,2},
    {0,7,0,0,0,0,0,0,0,0,1,0,0},
    {0,7,0,0,0,0,0,0,0,0,0,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,1}};

E3=transpose matrix {
    {0,4,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,5,0,0,0,0,4,3,0,0,0,0,0},
    {0,0,0,0,0,0,7,0,0,0,0,0,0},
    {0,10,0,0,0,0,0,7,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,-1,2024,0,0,0},
    {0,6,0,0,0,0,0,0,2023,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,2023,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,-3,2,2},
    {0,7,0,0,0,0,0,0,0,0,1,0,0},
    {0,7,0,0,0,0,0,0,0,0,0,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,1}};

A=2;
E4=transpose matrix {
    {0,4,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,5,0,0,0,0,4,3,0,0,0,0,0},
    {0,0,0,0,0,0,7,0,0,0,0,0,0},
    {0,10,0,0,0,0,0,7,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,-1,A,0,0,0},
    {0,6,0,0,0,0,0,0,A-1,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,-3,2,2},
    {0,7,0,0,0,0,0,0,0,0,1,0,0},
    {0,7,0,0,0,0,0,0,0,0,0,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,1}};

A=40;
E9=transpose matrix {{0,0,0,0,0,0,0,0,0,0,1,0,0},
    {1,0,-3,-5,-7,0,0,0,0,0,0,0,0},
    {0,0,1,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,1,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,1,0,0,0,0,0,0,0,0},
    {0,4,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,5,0,0,0,0,4,3,0,0,0,0,0},
    {0,0,0,0,0,0,7,0,0,0,0,0,0},
    {0,10,0,0,0,0,0,7,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,-1,A,0,0,0},
    {0,6,0,0,0,0,0,0,A-1,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,-3,2,2},
    {0,7,0,0,0,0,0,0,0,0,1,0,0},
    {0,7,0,0,0,0,0,0,0,0,0,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,1}};


A=3;
E8=transpose matrix {{1,0,-3,-5,-7,0,0,0,0,0,0,0,0},
    {0,0,1,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,1,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,1,0,0,0,0,0,0,0,0},
    {0,4,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,5,0,0,0,0,4,3,0,0,0,0,0},
    {0,0,0,0,0,0,7,0,0,0,0,0,0},
    {0,10,0,0,0,0,0,7,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,-1,A,0,0,0},
    {0,6,0,0,0,0,0,0,A-1,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,A-1,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,-3,2,2},
    {0,7,0,0,0,0,0,0,0,0,1,0,0},
    {0,7,0,0,0,0,0,0,0,0,0,1,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,1}};




E4

cF = (m) -> binomial(m+4, 4);
elapsedTime U = countMarkov E4;
elapsedTime V = countMarkov E5;
elapsedTime W = 5^3 * (cF(0))^8 * (cF(A))^8 * (cF(2*A))^4 * (cF(3*A))^4 * (cF(4*A))^2 * (cF(5*A))^2 * (cF(7*A));
U
V
W





b=4;
cF = (m) -> binomial(m+b, b);

5^3 * (cF(0))^8 * (cF(2024))^8 * (cF(4048))^4 * (cF(6072))^4 * (cF(8096))^2 * (cF(10120))^2 * (cF(14168))
10 + 8 * cF(0) + 8 * cF(2024) + 4 * cF(4048) + 4 * cF(6072) + 2 * cF(8096) + 2 * cF(10120) + cF(14168)



(b+1)^3 * (cF(0))^8 * (cF(A))^8 * (cF(2*A))^4 * (cF(3*A))^4 * (cF(4*A))^2 * (cF(5*A))^2 * (cF(7*A))
10 + 8 * cF(0) + 8 * cF(2024) + 4 * cF(4048) + 4 * cF(6072) + 2 * cF(8096) + 2 * cF(10120) + cF(14168)


fiberGraph' = profile fiberGraph


debugLevel = 10
elapsedTime countMarkov(E8, Algorithm => "decompose") -- 5.86078 seconds
elapsedTime countMarkov(E8, Algorithm => "fast") -- 34.2109 seconds
elapsedTime countMarkov(E8, Algorithm => "lattice") -- 156.734 seconds
remove(E8.cache, "FiberGraphComponents")


for key in keys fiberValues do (
    v := transpose matrix {(fiberValues#key)};
    print(numRows ((pointsInFiber(A, v))#"gen"));
    );

debugLevel = 2
showNmzOptions()
setNmzOption("normal_l", true)
