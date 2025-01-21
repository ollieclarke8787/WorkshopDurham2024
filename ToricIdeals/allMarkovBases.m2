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
    DebuggingMode => false,
    PackageExports => {"FourTiTwo","Graphs"}
    )

export {
    "fiberGraphGenerator",
    "pruferSequence",
    "markovBases",
    "randomMarkov",
    "NumberOfBases",
    "fiberGraph",
    "returnConnectedComponents"
    }

-* Code *-


fiberGraph = method(
    Options => {
        returnConnectedComponents => false
	}
    );

fiberGraph Matrix := opts -> A -> (
    local val;
    local stk;
    local temp;
    local ck;
    local cur;
    n := numColumns A;
    M := toricMarkov A;
    d := numRows M;
    L := new MutableList;
    Md := new MutableList;
    vales := new MutableList;
    -- vales as a MutableHashTable (values are the starting elements of the fiber i.e. L)
    -- to get the list of vales: keys vales
    --
    for i from 0 to d-1 do(
        temp=for j from 0 to n-1 list(if M_(i,j)>=0 then M_(i,j) else 0);
        val = (A * transpose matrix{temp});
        if all(vales,z -> z!=val) then L##L={temp,val};
        vales##vales=val;
	Mdel := flatten entries M^{i};
        Md##Md = Mdel;
        Md##Md = - Mdel;
        );
    Gindex := new MutableList;
    G := new MutableList;
    for k from 0 to #L - 1 do(
        stk := new MutableList from {L#k#0};
				Gi := new MutableList from {L#k#0};
				-- Gi as a MutableHashTable:
				--  keys: elements of the fiber
				--  valueso: index in the matrix
				-- so we can replace: "all(Gi, z-...)" with "Gi#?ck"
				Gt:=matrix"0";
				while #stk != 0 do(
						cur := stk#0;
						for i from 0 to #Md - 1 do(
								ck := Md#i + cur;
								if (all(ck,z -> z>=0) and all(Gi,z -> z!=ck)) then (
										stk##stk=ck;
										x:=matrix{for j from 0 to #Gi-1 list(
														if (not all(ck,Gi#j,(y,z) -> y<=0 or z<=0)) then 1 else 0)};
										Gt=matrix{{Gt,transpose x},{x,matrix{{0}}}};
										Gi##Gi=ck;
										);
                );
            remove(stk,0);
            );
        Gindex##Gindex=Gi;
        G##G=Gt;
				);
		if opts.returnConnectedComponents then (
				for k from 0 to #G - 1 list connectedComponents graph(toList Gindex#k,G#k))
		else (
				for k from 0 to #G - 1 list graph(toList Gindex#k,G#k))
		);




-- edge list of spanning tree corresponding to L
pruferSequence = method();
pruferSequence List := L ->(
    local n;
    local cg;
    local deg;
    n = #L + 2;
    cg = new MutableList; -- list of edges
    deg = new MutableList from toList(n : 1); -- degrees of vertices
    for j in L do(
	deg#j = deg#j + 1;
        );
    for j in L do(
        for l from 0 to n-1 do(
            if deg#l == 1 then(
		cg##cg = set {l,j};
		deg#j = deg#j -1;
		deg#l = deg#l -1;
                break;
                );
            );
        );
    cg##cg = set positions(deg,x -> x==1);
    toList cg
    );


-- direct product of lists (unexported)
listProd = method();
listProd List := Ls -> (
    fold((pr, ad) -> flatten for i in pr list for el in ad list append(i, el),
	{{}},
	Ls)
    );


markovBases = method();
markovBases Matrix := A -> (
    cc := fiberGraph(A,returnConnectedComponents =>true);
    poss:=for k from 0 to #cc-1 list(
        for i in listProd splice {#cc#k-2 : toList(0..#cc#k-1)} list pruferSequence i
        );
    fin:=listProd for k from 0 to #poss-1 list(
        flatten for i from 0 to #poss#k-1 list(
            listProd for j from 0 to #poss#k#i-1 list(
                x:=listProd for l in keys poss#k#i#j list cc#k#l;
                for w in x list w#0-w#1
                )
            )
        );
    for m in fin list matrix flatten m
    );

markovBases(Matrix, Ring) := (A, R) -> (
		listOfBases := markovBases(A);
	  apply(listOfBases, B -> toBinomial(B, R))
		)


randomMarkov = method(
    Options => {
	NumberOfBases => 1
	}
    );

randomMarkov Matrix := opts -> A -> (
    cc := fiberGraph(A,returnConnectedComponents =>true);
    result := for i from 0 to opts.NumberOfBases - 1 list(
        poss:=for k from 0 to #cc-1 list(
            pruferSequence for j from 0 to #cc#k-3 list random length cc#k
            );
        matrix flatten for k from 0 to #poss-1 list(
            for j from 0 to #poss#k-1 list(
                w:=for l in keys poss#k#j list cc#k#l#(random length cc#k#l);
                w#0-w#1
                )
            )
        );
    if opts.NumberOfBases == 1 then result_0 else result
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
      A Markov basis is a minimal generating set for of a toric ideal.
      Has uses in Algebraic Statistics [+ref] for sampling

			This package computes the set of all minimal Markov bases of a given toric ideal $I_A$.
			We do this by using [+ref] FourTiTwo to compute one Markov basis $M$.
			We then find all spanning forests of the \emph{fiber graph} of $A$ in the \emph{generating fibers}.
			We then construct the Markov basis associated to each spanning forest.

    Example
      A = matrix "7,8,9,10"
      netList markovBases A

    Text
      The package also allows for the uniformly sampling of the space of minimal Markov bases.

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
///


doc ///
	Key
		fiberGraph
		(fiberGraph, Matrix)
		[fiberGraph, returnConnectedComponents]
	Headline
		the relevant fibers of a configuration matrix as graphs
	Usage
		G = fiberGraph(A)
	Inputs
		A : Matrix
			the configuration matrix
		returnConnectedComponents => Boolean
			when true fiberGraph returns a list of connected components of each fiber
	Outputs
		G : List
			a list of graphs corresponding to relevant fibers of A
	Description
		Text
			This method constructs the relevant fibers of a configuration matrix $A$ using a recursive algorithm.
			The fibres are returned as a list of graphs where two vectors in a fiber are adjacent if their
			supports have non-trivial intersection.
			When returnConnectedComponents is true, instead of returning a list of graphs, fiberGraph returns a list of the connected components of each fiber.
		Example
			fiberGraph matrix "3,4,5"
			fiberGraph matrix "1,2,3"
			fiberGraph(matrix "1,2,3", returnConnectedComponents => true)
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
			computes the corresponding edge set of the spanning tree corresponding to the given Prüfer sequence L, calculated via Prüfer's algorithm
		Example
			pruferSequence {2}
			pruferSequence {1,3}
	SeeAlso
		markovBases
		allMarkovBases
	Subnodes
		fiberGraphGenerator
		markovBases
		pruferSequence
///



doc ///
	Key
		markovBases
		(markovBases, Matrix)
	Headline
		every minimal Markov basis of a configuration matrix
	Usage
		L=markovBases(A)
	Inputs
		A : Matrix
			the configuration matrix
	Outputs
		L : List
			a list of Markov bases
	Description
		Text
			this method outputs a list of every minimal Markov basis for a given configuration matrix
		Example
			markovBases matrix "3,4,5"
			markovBases matrix "1,2,3"
			markovBases matrix "1,2,3,4"
			markovBases matrix "1,2,3;4,5,6"
	SeeAlso
		allMarkovBases
///


doc ///
	Key
		randomMarkov
		(randomMarkov, Matrix)
		[randomMarkov, NumberOfBases]
		NumberOfBases
	Headline
		random minimal Markov basis
	Usage
		B = randomMarkov A
	Inputs
		A : Matrix
			the configuration matrix
		NumberOfBases => ZZ
			number of Markov bases to return
	Outputs
		B : List
			a Markov basis of A formatted as a list of vectors
	Description
		Text
			this method outputs one randomly chosen Markov basis for a given configuration matrix A
		Example
			randomMarkov matrix "1,2,3"
			randomMarkov matrix "1,2,3,4"
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


-- if a toric ideal is created by toricMarkov
-- then the information of the matrix A is not cached anywhere
A = matrix {{1,2,3,4,5}}
R = QQ[x_1 .. x_5]
I = toricMarkov(A, R)
I = randomMarkov(A, R)
peek I.cache -- empty
peek (gens I).cache


loadPackage("allMarkovBases",Reload => true)
fiberGraph matrix"1,2,3"

-----
-- big to do:
-- check documentation [Ollie]

-- little to dos:
-- markovBases(A, R) ---> list of ideals / generating sets in R (just like toricMarkov)
-- use 'toBinomial' (from FourTiTwo) to construct the polynomials from matrices

-- in fiberGenerating function replace Gi with a MutableHashTable [Ollie]
