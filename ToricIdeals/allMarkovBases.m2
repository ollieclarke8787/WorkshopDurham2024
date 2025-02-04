newPackage(
    "allMarkovBases",
    Version => "0.1",
    Date => "December 16, 2024",
    Headline => "A package to compute all minimal Markov Bases of a given configuration matrix",
    Authors => {
        {Name => "Alex Milner", Email => "A.J.C.Milner@sms.ed.ac.uk", HomePage => ""},
        {Name => "Oliver Clarke", Email => "oliver.clarke@durham.ac.uk", HomePage => "https://www.oliverclarkemath.com/"}
        },
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"FourTiTwo","Graphs"}
    )

export {
    "pruferSequence",
    "markovBases",
    "randomMarkov",
    "NumberOfBases",
    "AlwaysReturnList",
    "fiberGraph",
    "ReturnConnectedComponents",
		"CheckInput"
    }

-* Code *-


fiberGraph = method(
    Options => {
        ReturnConnectedComponents => false,
				CheckInput => true
	}
    );

fiberGraph Matrix := opts -> adjacencyMatrix -> (
		if opts.CheckInput then (
				-- make sure the user has supplied a matrix ker(A) \cap \NN^n = {0}
				-- Qu. Is pointed in the sense of \NN A
				kerGenerators := transpose gens ker adjacencyMatrix;
				kerGenerators = promote(kerGenerators, QQ);
				kerGenerators = reducedRowEchelonForm kerGenerators;
				for gen in entries kerGenerators do (
						if (all(gen, z -> z >= 0) or all(gen, z -> z <= 0)) then error("matrix is not pointed");
						);
				);
    n := numColumns adjacencyMatrix;
    starterMarkovBasis := toricMarkov adjacencyMatrix;
    fiberStarters := new MutableHashTable;
    possibleMoves := new MutableList;
    for i from 0 to numRows starterMarkovBasis - 1 do(
        starterFiberElement := for j from 0 to n-1 list(if starterMarkovBasis_(i,j)>=0 then starterMarkovBasis_(i,j) else 0);
        fiberValue := adjacencyMatrix * transpose matrix{starterFiberElement};
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
    if opts.ReturnConnectedComponents then apply(fibers, connectedComponents)
    else fibers
    );



pruferSequence = method();
pruferSequence List := pruferList -> (
    numberOfNodes := #pruferList + 2;
    edgeList := new MutableList;
    nodeDegrees := new MutableList from toList(numberOfNodes : 1);
    for j in pruferList do(
	nodeDegrees#j = nodeDegrees#j + 1;
        );
    for j in pruferList do(
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
listProd List := lists -> (
    fold((combinedLists, listToBeAdded) -> flatten for combinedElement in combinedLists list for newElement in listToBeAdded list append(combinedElement, newElement),
	{{}},
	lists)
    );


markovBases = method(
		Options => {
				CheckInput => true
				}
		);
markovBases Matrix := opts -> adjacencyMatrix -> (
    allFibersConnectedComponents := fiberGraph(adjacencyMatrix,
				ReturnConnectedComponents => true,
				CheckInput => opts.CheckInput);
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

markovBases(Matrix, Ring) := opts -> (adjacencyMatrix, R) -> (
		listOfBases := markovBases(adjacencyMatrix, opts);
	  apply(listOfBases, B -> toBinomial(B, R))
		)


randomMarkov = method(
    Options => {
	NumberOfBases => 1,
	AlwaysReturnList => false,
	CheckInput => true
	}
    );

randomMarkov Matrix := opts -> adjacencyMatrix -> (
    allFibersConnectedComponents := fiberGraph(adjacencyMatrix,
				ReturnConnectedComponents => true,
				CheckInput => opts.CheckInput);
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


randomMarkov(Matrix, Ring) := opts -> (adjacencyMatrix, R) -> (
    listOfBases := randomMarkov(adjacencyMatrix, NumberOfBases => opts.NumberOfBases, AlwaysReturnList => true, CheckInput => opts.CheckInput);
    listOfIdeals := apply(listOfBases, B -> toBinomial(B, R));
    if (not opts.AlwaysReturnList and opts.NumberOfBases == 1) then listOfIdeals_0 else listOfIdeals
    );




-* Documentation section *-

beginDocumentation()

doc ///
  Key
    allMarkovBases
  Headline
    A package for computing all minimal Markov Bases of a toric ideal
  Description
    Text
      Fix a matrix $A = (a_{i,j}) \in \ZZ^{d \times n}$ satisfying $\ker(A) \cap (\ZZ_{\ge 0})^n = \{0\}$.
      The toric ideal $I_A$ is the kernel of the associated monomial map
      $\phi_A : k[x_1, \dots, x_n] \rightarrow k[t_1, \dots, t_d]$ given by
      $\phi(x_i) = t_1^{a_{1,i}} t_2^{a_{2,i}} \dots t_d^{a_{d,i}}$ for each $i \in [n]$.
      A Markov basis is a minimal generating set for a toric ideal.
      Has uses in Algebraic Statistics [+ref] for sampling

      This package computes the set of all minimal Markov bases of a given toric ideal $I_A$.
      We do this by using [+ref] FourTiTwo to compute one Markov basis $M$.
      We then find all spanning forests of the \emph{fiber graph} of $A$ in the \emph{generating fibers}.
      We then construct the Markov basis associated to each spanning forest.

    Example
      A = matrix "7,8,9,10"
      netList markovBases A

    Text
      The package also allows for the uniformly sampling of the space of minimal Markov bases where the number of random Markov bases can be specified using the option NumberOfBases.

    Example
      randomMarkov(A)
      netList randomMarkov(A, NumberOfBases => 2)

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
            "2007."}
        }@

  Subnodes
    randomMarkov
///


doc ///
	Key
		fiberGraph
		(fiberGraph, Matrix)
		[fiberGraph, ReturnConnectedComponents]
	Headline
		the relevant fibers of a configuration matrix as graphs
	Usage
		G = fiberGraph(A)
	Inputs
		A : Matrix
			the configuration matrix
		ReturnConnectedComponents => Boolean
			when true fiberGraph returns a list of connected components of each fiber instead of the whole graphs
	Outputs
		G : List
			a list of graphs corresponding to relevant fibers of A
	Description
		Text
			Constructs the relevant fibers of a configuration matrix $A$ using a recursive algorithm.
			The fibres are returned as a list of graphs where two vectors in a fiber are adjacent if their
			supports have non-trivial intersection.
			When ReturnConnectedComponents is true, instead of returning a list of graphs, fiberGraph returns a list of the connected components of each fiber.
		Example
			fiberGraph matrix "3,4,5"
			fiberGraph matrix "1,2,3"
			fiberGraph(matrix "1,2,3", ReturnConnectedComponents => true)
			fiberGraph matrix "1,2,3,4"
	SeeAlso
		markovBases
		allMarkovBases
///



doc ///
	Key
		pruferSequence
		(pruferSequence, List)
	Headline
		the corresponding edge set of the spanning tree corresponding to the given Prüfer sequence
	Usage
		E=pruferSequence(L)
	Inputs
		L : List
			Prüfer sequence to be converted into tree
	Outputs
		E : List
			the corresponding edge set of the spanning tree corresponding to the given Prüfer sequence L
	Description
		Text
			Computes the corresponding edge set of the spanning tree corresponding to the given Prüfer sequence L, calculated via Prüfer's algorithm
		Example
			pruferSequence {2}
			pruferSequence {1,3}

	SeeAlso
		markovBases
		allMarkovBases

--	References
    --@UL{
    --    {"Prüfer, H. (1918). Neuer Beweis eines Satzes über Permutationen.",
	--    EM "Arch. Math. Phys. 27: 742–744."}
    --    }@
	Subnodes
		fiberGraph
		markovBases
		pruferSequence
///



doc ///
	Key
		markovBases
		(markovBases, Matrix)
		(markovBases, Matrix, Ring)
	Headline
		every minimal Markov basis of a configuration matrix
	Usage
		K=markovBases(A)
		L=markovBases(A,R)
	Inputs
		A : Matrix
			the configuration matrix
		R : Ring
			ring with 1 generator for each column of A
	Outputs
		K : List
			a list of every minimal Markov basis formatted as matrices whose rows form a minimal Markov basis of A
		L : List
			a list of every ideal in R generated by a minimal Markov basis of A
	Description
		Text
			this method outputs a list of every minimal Markov basis for a given configuration matrix
		Example
			netList markovBases matrix "3,4,5"
			netList markovBases matrix "1,2,3"
			netList markovBases matrix "1,2,3,4"
			netList markovBases matrix "1,2,3;4,5,6"
		Text
			if, in addition, we specify a ring R, this method outputs a list of every ideal in R generated by a minimal Markov basis of A
		Example
			netList markovBases(matrix "3,4,5",QQ[x_1,x_2,x_3])
			gens (markovBases(matrix "3,4,5",QQ[x_1,x_2,x_3]))#0
			netList markovBases(matrix "1,2,3",QQ[x_1,x_2,x_3])
			gens (markovBases(matrix "1,2,3",QQ[x_1,x_2,x_3]))#1
	SeeAlso
		allMarkovBases
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
		random minimal Markov basis
	Usage
		B = randomMarkov A
		C = randomMarkov(A,R)
	Inputs
		A : Matrix
			the configuration matrix
		R : Ring
		        ring with 1 generator for each column of A
		NumberOfBases => ZZ
			number of Markov bases to return
		AlwaysReturnList => Boolean
		        if false and NumberOfBases == 1 then returns as a list of 1 element
	Outputs
		B : Matrix
			a Markov basis of A formatted as a list of vectors
		C : Ideal
			an ideal in R generated by a random Markov basis

	Description
		Text
			this method outputs one randomly chosen Markov basis for a given configuration matrix A
		Example
			randomMarkov matrix "1,2,3"
			randomMarkov matrix "1,2,3,4"
		Text
		        In addition, we can specify the number of random Markov bases can be specified using the option NumberOfBases in cases when there are many minimal Markov bases.
			randomMarkov(matrix "2,5,20", NumberOfBases => 3)
	SeeAlso
		markovBases
		allMarkovBases
///



-* Test section *-

TEST /// -- unique minimal Markov basis for monomial curve in A^3
assert(markovBases matrix "3,4,5" == {toricMarkov matrix "3,4,5"})
///

TEST /// -- two minimal Markov bases for (CI) monomial curve in A^3
assert(markovBases matrix "1,2,3" == {matrix {{2,-1,0},{3,0,-1}},matrix {{2,-1,0},{1,1,-1}}})
///

TEST /// -- hypersurface in A^3
assert(markovBases matrix "1,2,3;4,5,6" == {matrix {{1,-2,1}}})
///

TEST /// -- monomial curve in A^5 with five minimal Markov bases
result := {
    matrix {{5, -2, 0},{20, 0, -1}},
    matrix {{5, -2, 0},{15, 2, -1}},
    matrix {{5, -2, 0},{10, 4, -1}},
    matrix {{5, -2, 0},{5, 6, -1}},
    matrix {{5, -2, 0},{0, 8, -1}}};
assert(markovBases matrix "2,5,40" == result)
///


end--

-- development stuff
restart
uninstallPackage "allMarkovBases"
restart
installPackage "allMarkovBases"

loadPackage "allMarkovBases"
check allMarkovBases

viewHelp allMarkovBases

elapsedTime pruferSequence(8);


-- if a toric ideal is created by toricMarkov$0
-- then the information of the matrix A is not cached anywhere
A = matrix {{1,2,3,4,5}}
R = QQ[x_1 .. x_5]
I = toricMarkov(A, R)
I = randomMarkov(A, R)
I = randomMarkov(A, R, NumberOfBases => 0)
peek I.cache -- empty
peek (gens I).cache


loadPackage("allMarkovBases",Reload => true)
fiberGraph matrix "1,2,3"

-----
-- big to do:
-- check documentation [Ollie]

-- little to dos:

-- thinking about methodology that fiberGraph is using in order to reduce the number of mutable objects
-- come up with other examples (slightly bigger ones)







--Thoughts:

--I think we are always producing minimal Markov Bases so every time we say "Markov bases" in the documentation maybe we should add minimal in front?


-- Are the orderings of the results of markovBases always consistent? Maybe there is some
-- randomness caused by using sets or something else?
-- Might want to make the testt just count the number of bases instead
-- Or we could make the set of rows and the set of Markov bases and check their equality
