newPackage(
    "AllMarkovBases",
    Version => "0.1",
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
    PackageExports => {"FourTiTwo","Graphs","TensorComplexes","Polyhedra","Posets","SubalgebraBases","LLLBases"}
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
    "CheckInput",
    "fiber",
    "countMarkov",
    "toricIndispensableSet",
    "toricUniversalMarkov"
    }

----------
-- Code --
----------






fiberGraph = method(
    Options => {
        ReturnConnectedComponents => false,
        CheckInput => true,
        Algorithm => "graph", -- "decompose","lattice","fast"(RECOMMENDED),"graph",
	fiber => {}
        }
    );
fiberGraph Matrix := opts -> A -> (
    local starterMarkovBasis;
    n := numColumns A;
    if opts.ReturnConnectedComponents then (
        -- return a list of (lists of) components
        if not A.cache#?"FiberGraphComponents" then (
            starterMarkovBasis = toricMarkov A;
            if opts.CheckInput then ( -- check whether \NN A is a pointed cone
                for basisElement in entries starterMarkovBasis do (
                    if (all(basisElement, z -> z >= 0) or all(basisElement, z -> z <= 0)) then error("semigroup not pointed");
                    );
                );
	    if opts.fiber != {} then return decomposeFiberGraph(A,starterMarkovBasis,opts.fiber);
            if opts.Algorithm == "fast" then (
                fastFiberGraphInternal(A, starterMarkovBasis);
                )
            else if opts.Algorithm == "graph" then (
                graphicFiberGraph(A, starterMarkovBasis);
                )
	    else if opts.Algorithm == "lattice" then (
                latticeFiberGraph(A, starterMarkovBasis);
                )
	     else if opts.Algorithm == "decompose" then (
                decomposeFiberGraph(A, starterMarkovBasis,opts.fiber);
                )
            else error("unknown option for Algorithm");
            );
        A.cache#"FiberGraphComponents"
        )
    else (
        -- return the graph objects
        if not A.cache#?"FiberGraph" then (
            starterMarkovBasis = toricMarkov A;
            if opts.CheckInput then ( -- check whether \NN A is a pointed cone
                for basisElement in entries starterMarkovBasis do (
                    if (all(basisElement, z -> z >= 0) or all(basisElement, z -> z <= 0)) then error("semigroup not pointed");
                    );
                );
	    if opts.fiber != {} then return flatten decomposeFiberGraph(A,starterMarkovBasis,opts.fiber);
            if opts.Algorithm == "graph" then (
                graphicFiberGraph(A, starterMarkovBasis);
                )
            else error("unknown option for Algorithm");
            );
        A.cache#"FiberGraph"
        )
    )


--Algorithm 3: decompose fiber into smaller fibers 
decomposeFiberGraph = method();
decomposeFiberGraph (Matrix, Matrix,List) := (A, starterMarkovBasis,fiber) -> (
    n := numColumns A;
    R := QQ(monoid[Variables => 2*n]);
    A.cache#"ring" = R;
    G := gens R;
    I := ideal(for i from 0 to n-1 list(G#i * G#(n+i) -1));
    S := subring (gens R)_{0..n-1};
    A.cache#"subring" = S;
    A.cache#"binomial" = toBinomial(starterMarkovBasis,R)+I;
    starterMarkovBasis = entries starterMarkovBasis;
    fiberStarters := new MutableHashTable;
    for basis in starterMarkovBasis do(
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
    if not A.cache#?"fiberStarters" then A.cache#"fiberStarters" = fiberStarters;
    local fiberValuesPoset;
    if fiber == {} then (fiberValuesPoset = poset(keys fiberStarters,(x,y) -> x<<y);)
    else (
	snippedStarters := for starter in keys fiberStarters list(if starter << fiber then starter else continue);
	fiberValuesPoset = poset(toList(set snippedStarters + set {fiber}),(x,y) -> x<<y);
	);
    fibersLeft := new MutableList from fiberValuesPoset#GroundSet;
    tempPoset := fiberValuesPoset;
    A.cache#"MBTiming" = 0; --TIMING
    A.cache#"foldingTiming" = 0; --TIMING
    A.cache#"additionTiming" = 0; --TIMING
    A.cache#"recursion" = 0; --TIMING
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
	    (A.cache#"fiberStarters")#minimalElement = {union R};
	    );
	tempPoset = subposet(fiberValuesPoset,toList fibersLeft);
	);
    --print peek (A.cache#"fiberStarters");
    print "Time spent computing Markov bases"; --TIMING
    print A.cache#"MBTiming"; --TIMING
    print "Time spent folding lists"; --TIMING
    print A.cache#"foldingTiming"; --TIMING
    print "Time spent adding lists"; --TIMING
    print A.cache#"foldingTiming"; --TIMING
    print "Time spent recursing"; --TIMING
    print A.cache#"recursion"; --TIMING
    remove(A.cache,"current");
    if fiber=={} then A.cache#"FiberGraphComponents" = values finalR else finalR#fiber
    );



-- addition of fibers (unexported)
fiberAdd = method();
fiberAdd (Set,Set,Matrix) := (C,D,A) -> (
    -- {set flatten for p in keys C list for q in keys D list p+q}
    aDD := timing {set flatten for p in keys C list for q in keys D list p+q}; --TIMING
    A.cache#"additionTiming" = A.cache#"additionTiming" + aDD#0; --TIMING
    aDD#1 --TIMING
    );

-- recursive method 2 (unexported)
recursiveFiber = method();
recursiveFiber (List, List, Matrix) := (val, rvs, A) -> (
    local output;
    residVals := for i from 0 to #rvs - 1 list(
	resid := val-rvs#i;
	if not all(resid,z -> z>=0) then continue;
	output := fiberAdd((union recursiveFiber(resid, rvs_{0..i}, A)), ((A.cache#"fiberStarters")#(rvs#i))#0,A);
	if output == {set{}} then continue else output
	);
    -- if #residVals > 0 then fold(residVals,integrateLists)
    if #residVals > 0 then (F := timing fold(residVals,integrateLists); A.cache#"foldingTiming" = A.cache#"foldingTiming" + F#0; F#1) --TIMING
    else if (A.cache#"fiberStarters")#?val and (A.cache#"current" != val) then (A.cache#"fiberStarters")#val
    else endFiber2(val, A)
    );

-- method to handle end of recursion (unexported)
endFiber = method();
endFiber (List, Matrix) := (val, A) -> (
    output := {set{}};
    T := timing toricMarkov matrix{{transpose matrix {val},A}}; --TIMING
    A.cache#"MBTiming" = A.cache#"MBTiming" + T#0; --TIMING
    for row in entries T#1 do( --TIMING
    -- for row in entries toricMarkov matrix{{transpose matrix {val},A}} do(
	r := drop(row,1);
	if row#0 == 1 and all(r,z->z<=0) then (output = {set{-r}}; break;);
	);
    (A.cache#"fiberStarters")#val=output;
    output
    );

-- different algorithm to handle end of recursion (unexported) (a lot slower)
endFiber2 = method();
endFiber2 (List, Matrix) := (val, A) -> (
    n := numColumns A;
    T := timing (entries transpose (LLL(A | transpose matrix{val},ChangeMatrix => true))#1)#(n-rank A);
    A.cache#"MBTiming" = A.cache#"MBTiming" + T#0; --TIMING
    T = T#1;
    -- T := last entries transpose kernelLLL (A | transpose matrix{val});
    if abs(last T) != 1 then return {set{}};
    T = -(last T) * drop(T,-1);
    G := gens A.cache#"ring";
    e := 1;
    for i from 0 to #T - 1 do(
	if T#i < 0 then e=e*(G#(n+i))^(-T#i)
	else e=e*(G#i)^(T#i)
	);
    e = e % A.cache#"binomial";
    if e % A.cache#"subring" == 0 then {set{take((exponents e)#0,{0,n-1})}} else {set{}}
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
latticeFiberGraph (Matrix, Matrix) := (A, starterMarkovBasis) -> (
    starterMarkovBasis = entries starterMarkovBasis;
    n := numColumns A;
    d := numRows A;
    fiberStarters := new MutableHashTable;
    fiberValues := new MutableHashTable;
    for basis in starterMarkovBasis do(
        elPos := for coord in basis list(if coord >= 0 then coord else 0);
        elNeg := elPos - basis;
        fiberVal := flatten entries (A * transpose matrix{elPos});
        if fiberStarters#?fiberVal then (fiberStarters#fiberVal)##(fiberStarters#fiberVal) = {elPos,elNeg} else fiberStarters#fiberVal = new MutableList from {{elPos,elNeg}};
        fiberValues#basis = fiberVal;
        );
    AQQ := matrix(QQ,entries A);
    A.cache#"FiberGraphComponents" = for val in keys fiberStarters list(
	V := transpose matrix(QQ,{val});
	lPs := (v -> (entries transpose v)#0) \ latticePoints convexHull transpose matrix for subset in subsets(toList(0..n-1),d) list(
	    S := submatrix(AQQ,subset);
	    if det S == 0 then continue;
	    Sinv := inverse(S) * V;
	    tempL := new MutableList from n:0;
	    for i from 0 to d-1 do tempL#(subset#i) = Sinv_(i,0);
	    tempL = toList tempL;
	    if all(tempL, z -> z >= 0) then tempL else continue
	    );
	buildFiber := unique flatten toList fiberStarters#val;
	finalR := (v -> new MutableList from {v}) \ buildFiber;	
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
	(v -> toList v) \ finalR
	);
    );






--Algorithm 1: faster fiberGraph
--returns connected components and stores them in A.cache

fastFiberGraphInternal = method();
fastFiberGraphInternal(Matrix, Matrix) := (A, starterMarkovBasis) -> (
    starterMarkovBasis = entries starterMarkovBasis;
    n := numColumns A;
    fiberStarters := new MutableHashTable;
    fiberValues := new MutableHashTable;
    for basis in starterMarkovBasis do(
        elPos := for coord in basis list(if coord >= 0 then coord else 0);
        elNeg := elPos - basis;
        fiberVal := flatten entries (A * transpose matrix{elPos});
        if fiberStarters#?fiberVal then (fiberStarters#fiberVal)##(fiberStarters#fiberVal) = {elPos,elNeg} else fiberStarters#fiberVal = new MutableList from {{elPos,elNeg}};
        fiberValues#basis = fiberVal;
        );

    A.cache#"FiberGraphComponents" = for val in keys fiberStarters list(
        validMoves := for move in starterMarkovBasis list if (fiberValues#move << val) and (fiberValues#move != val) then move else continue;
        validMoves = new MutableHashTable from ((v -> {v,true}) \ validMoves);
        buildFiber := unique flatten toList fiberStarters#val;
        for i from 0 to #buildFiber - 1 list(
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

graphicFiberGraph = method()
graphicFiberGraph(Matrix, Matrix) := (A, starterMarkovBasis) -> (
    n := numColumns A;
    fiberStarters := new MutableHashTable;
    possibleMoves := new MutableList;
    for i from 0 to numRows starterMarkovBasis - 1 do(
        starterFiberElement := for j from 0 to n-1 list(if starterMarkovBasis_(i,j)>=0 then starterMarkovBasis_(i,j) else 0);
        fiberValue := A * transpose matrix{starterFiberElement};
        if not fiberStarters#?fiberValue then fiberStarters#fiberValue = starterFiberElement;
        validMove := flatten entries starterMarkovBasis^{i};
        possibleMoves##possibleMoves = validMove;
        possibleMoves##possibleMoves = - validMove;
        );
    fibers := new MutableList;
    for starterFiberElement in values fiberStarters do(
        queueOfFiberElements := new MutableList from {starterFiberElement};
        adjacencyMatrixIndex := new MutableHashTable from {starterFiberElement => 0};
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
        fibers##fibers=graph(toList orderedAdjacencyMatrixIndex, adjacencyMatrix);
        );
    fibers = toList fibers;
    A.cache#"FiberGraph" = fibers;
    A.cache#"FiberGraphComponents" = apply(A.cache#"FiberGraph", connectedComponents);
    fibers
    )


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


markovBases = method(
    Options => {
        CheckInput => true
        }
    );
markovBases Matrix := opts -> A -> (
    allFibersConnectedComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        CheckInput => opts.CheckInput,
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
    for markovBasisAsList in markovBasesAsLists list matrix flatten markovBasisAsList
    );

markovBases(Matrix, Ring) := opts -> (A, R) -> (
    listOfBases := markovBases(A, opts);
    apply(listOfBases, B -> toBinomial(B, R))
    )


randomMarkov = method(
    Options => {
        NumberOfBases => 1,
        AlwaysReturnList => false,
        CheckInput => true
        }
    );


randomMarkov Matrix := opts -> A -> (
    allFibersConnectedComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        CheckInput => opts.CheckInput,
        Algorithm => "fast");
    randomMarkovBases := for i from 0 to opts.NumberOfBases - 1 list(
        allFibersRandomSpanningTree := for fiberConnectedComponents in allFibersConnectedComponents list(
            pruferSequence for j from 1 to #fiberConnectedComponents-2 list random(#fiberConnectedComponents)
            );
        matrix flatten for k from 0 to #allFibersRandomSpanningTree-1 list(
            for edge in allFibersRandomSpanningTree#k list(
                randomPairOfFiberElements := for l in keys edge list allFibersConnectedComponents#k#l#(random(#allFibersConnectedComponents#k#l));
                randomPairOfFiberElements#0-randomPairOfFiberElements#1
                )
            )
        );
    if (not opts.AlwaysReturnList and opts.NumberOfBases == 1) then randomMarkovBases_0 else randomMarkovBases
    );


randomMarkov(Matrix, Ring) := opts -> (A, R) -> (
    listOfBases := randomMarkov(A, NumberOfBases => opts.NumberOfBases, AlwaysReturnList => true, CheckInput => opts.CheckInput);
    listOfIdeals := apply(listOfBases, B -> toBinomial(B, R));
    if (not opts.AlwaysReturnList and opts.NumberOfBases == 1) then listOfIdeals_0 else listOfIdeals
    );


countMarkov = method()
countMarkov Matrix := A -> (
    allFibersConnectedComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        CheckInput => true,
        Algorithm => "decompose");
    product for fiberConnectedComponents in allFibersConnectedComponents list(
        k := #fiberConnectedComponents;
        if k==2 then continue #fiberConnectedComponents#0 * #fiberConnectedComponents#1;
        ccSizes := (v -> #v) \ fiberConnectedComponents;
        (product ccSizes) * (sum ccSizes)^(k-2)
        )
    )



toricIndispensableSet = method()
toricIndispensableSet Matrix := A -> (
    fiberComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        CheckInput => true,
        Algorithm => "fast");
    indispensables := flatten for vertexList in fiberComponents list (
        if (
            #vertexList == 2 and
            #vertexList#0 == 1 and
            #vertexList#1 == 1
            ) then vertexList#0 - vertexList#1 else continue
        );
    matrix indispensables
    )

toricIndispensableSet(Matrix, Ring) := (A, R) -> (
    indispensableMatrix := toricIndispensableSet A;
    toBinomial(indispensableMatrix, R)
    )


toricUniversalMarkov = method()
toricUniversalMarkov Matrix := A -> (
    fiberComponents := fiberGraph(A,
        ReturnConnectedComponents => true,
        CheckInput => true,
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
    [fiberGraph, CheckInput]
    [fiberGraph, Algorithm]
    ReturnConnectedComponents
    CheckInput
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
    CheckInput => Boolean
      verify that the semigroup of the
      configuration matrix is pointed
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
    Text
      If the option @TO CheckInput@ is false then the functions does
      not check if the semigroup $\NN A$ is pointed, which may result
      in unexpected behaviour.

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
    [markovBases, CheckInput]
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
    CheckInput => Boolean
      whether to verify that the semigroup $\NN A$ is pointed
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
    [randomMarkov, CheckInput]
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
    CheckInput => Boolean
      whether to verify that the semigroup $\NN A$ is pointed
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
