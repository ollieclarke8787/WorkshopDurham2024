



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
    "randomMarkovBasis",
    "randomMarkovBases",
    "randomMarkov",
    "NumberOfBases"
    }







-* Code *-



fiberGraphGenerator = method();
fiberGraphGenerator Matrix := A ->(
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
        Md##Md = vector transpose M^{i};
        Md##Md = - vector transpose M^{i};
        );
    Gindex := new MutableList;
    G := new MutableList;
    for k from 0 to #L - 1 do(
        stk := new MutableList from {vector L#k#0};
        Gi := new MutableList from {vector L#k#0};
	-- Gi as a MutableHashTable:
	--  keys: elements of the fiber
	--  values: index in the matrix
	-- so we can replace: "all(Gi, z-...)" with "Gi#?ck" 
        Gt:=matrix"0";
        while #stk != 0 do(
            cur := stk#0;
            for i from 0 to #Md - 1 do(
                ck := Md#i + cur;
                if (all(entries ck,z -> z>=0) and all(Gi,z -> z!=ck)) then (
                    stk##stk=ck;
                    x:=matrix{for j from 0 to #Gi-1 list(
                        if (not all(entries ck,entries Gi#j,(y,z) -> y<=0 or z<=0)) then 1 else 0
                        )};
                    Gt=matrix{{Gt,transpose x},{x,matrix{{0}}}};
                    Gi##Gi=ck;
                    );
                );
            remove(stk,0);
            );
        Gindex##Gindex=Gi;
        G##G=Gt;
        );
    for k from 0 to #G - 1 list graph(toList Gindex#k,G#k)
    );



-*

Old method without using adjacency matrices
fiberGraphGenerator = method();
fiberGraphGenerator Matrix := A ->(
    local val;
    local stk;
    local temp;
    local ck;
    local cur;
    n := length (entries A)_0;
    M := toricMarkov A;
    d := length entries M;
    L := {};
    Md := {};
    vales := {};
    for i from 0 to d-1 do(
        temp = {};
        for j from 0 to n-1 do(
            if M_(i,j) < 0 then temp = append(temp,0)
            else temp = append(temp, M_(i,j));
            );
        val = (A * transpose matrix{temp});
        if (not isMember(val,vales)) then L=append(L,{temp,val});
        vales = append(vales,val);
        Md = append(Md, vector transpose M^{i});
        Md = append(Md, - vector transpose M^{i});
        );
    G:={};
    for k from 0 to (length L) -1 do(
        stk = {vector (L_k)_0};
        G = append(G,graph({vector (L_k)_0},{}));
        while (not length stk == 0) do(
            cur = stk_0;
            for i from 0 to (length Md)-1 do(
                ck = (Md_i + cur);
                if isMember(ck, vertexSet G_k) then continue;
                if all(entries ck,z -> if z<0 then false else true) then (
                    stk = append(stk,ck);
                    G = replace(k,addVertex(G_k,ck),G);
                    for v in (vertexSet G_k) do(
                        if (not all(entries ck,entries v,(x,y) -> if (x>0 and y>0) then false else true)) then (
                            G = replace(k,addEdge(G_k,set {ck,v}),G);
                            );
                        );
                    );
                );
            stk=drop(stk,1);
            );
        );
    G
    );*-



--Connected components of fibres (unexported)
fiberConnectedComponents = method();
fiberConnectedComponents Matrix := A ->(
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
    for i from 0 to d-1 do(
        temp=for j from 0 to n-1 list(if M_(i,j)>=0 then M_(i,j) else 0);
        val = (A * transpose matrix{temp});
        if all(vales,z -> z!=val) then L##L={temp,val};
        vales##vales=val;
        Md##Md = vector transpose M^{i};
        Md##Md = - vector transpose M^{i};
        );
    Gindex := new MutableList;
    G := new MutableList;
    for k from 0 to #L - 1 do(
        stk := new MutableList from {vector L#k#0};
        Gi := new MutableList from {vector L#k#0};
        Gt:=matrix"0";
        while #stk != 0 do(
            cur := stk#0;
            for i from 0 to #Md - 1 do(
                ck := Md#i + cur;
                if (all(entries ck,z -> z>=0) and all(Gi,z -> z!=ck)) then (
                    stk##stk=ck;
                    x:=matrix{for j from 0 to #Gi-1 list(
                        if (not all(entries ck,entries Gi#j,(y,z) -> y<=0 or z<=0)) then 1 else 0
                        )};
                    Gt=matrix{{Gt,transpose x},{x,matrix{{0}}}};
                    Gi##Gi=ck;
                    );
                );
            remove(stk,0);
            );
        Gindex##Gindex=Gi;
        G##G=Gt;
        );
    for k from 0 to #G - 1 list connectedComponents graph(toList Gindex#k,G#k)
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




-*
-- lists edges of all labelled trees on {1 .. n}
pruferSequence = method();
pruferSequence ZZ := n ->(
    local cg;
    local deg;
    ite := listProd splice {(n-2) : toList(0..(n-1))}; -- {1 .. n}^(n-2)
    for i in ite list (
	cg = new MutableList; -- list of edges
	deg = new MutableList from toList(n : 1); -- degrees of vertices
        for j in i do(
	    deg#j = deg#j + 1;
            );
        for j in i do(
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
	)
    );


-- previous version of pruferSequence
-- Note: 'replace' and 'addEdge' create new objects
-- so new version is around 100x faster:
-- E.g. n = 7. old version: 54.9312 seconds, new version: 0.242806 seconds 
pruferSequence = method();
pruferSequence ZZ := n ->(
    local cg;
    local deg;
    out :={};
    ite := listProd splice {(n-2):toList(0..(n-1))};
    for i in ite do(
        cg = graph(toList(0..(n-1)),{});
        deg=for l from 0 to n-1 list(1);
        for j in i do(
            deg=replace(j,(deg_j)+1,deg);
            );
        for j in i do(
            for l from 0 to n-1 do(
                if (deg_l==1) then(
                    cg = addEdge(cg,set {l,j});
                    deg=replace(j,(deg_j)-1,deg);
                    deg=replace(l,(deg_l)-1,deg);
                    break;
                    );
                );
            );
        cg = addEdge(cg,set positions(deg,x -> x==1));
        out=append(out,edges(cg));
        );
    out
    );
*-


-- direct product of lists (unexported)
listProd = method();
listProd List := Ls -> (
    fold((pr, ad) -> flatten for i in pr list for el in ad list append(i, el),
	{{}},
	Ls)
    );



markovBases = method();
markovBases Matrix := A -> (
    cc:= fiberConnectedComponents A;
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
    for m in fin list flatten m
    );



randomMarkov = method(
    Options => {
	NumberOfBases => 1
	}
    );

randomMarkov Matrix := opts -> A -> (
    cc:= fiberConnectedComponents A;
    result := for i from 0 to opts.NumberOfBases - 1 list(
        poss:=for k from 0 to #cc-1 list(
            pruferSequence for j from 0 to #cc#k-3 list random length cc#k
            );
        flatten for k from 0 to #poss-1 list(
            for j from 0 to #poss#k-1 list(
                w:=for l in keys poss#k#j list cc#k#l#(random length cc#k#l);
                w#0-w#1
                )
            )
        );
    if opts.NumberOfBases == 1 then result_0 else result 
    );


---------------
-- Todo: remove these random functions (they are combined above)
randomMarkovBasis = method();
randomMarkovBasis Matrix := A -> (
    cc:= fiberConnectedComponents A;    
    poss:=for k from 0 to #cc-1 list(
        pruferSequence for i from 0 to #cc#k-3 list random length cc#k
        );
    flatten for k from 0 to #poss-1 list(
        for j from 0 to #poss#k-1 list(
            w:=for l in keys poss#k#j list(
                cc#k#l#(random length cc#k#l)
                    );
            w#0-w#1
            )
        )
    );

randomMarkovBases = method();
randomMarkovBases (Matrix,ZZ) := (A,n) -> (
    cc:= fiberConnectedComponents A;
    for i from 0 to n-1 list(
        poss:=for k from 0 to #cc-1 list(
            pruferSequence for j from 0 to #cc#k-3 list random length cc#k
            );
        flatten for k from 0 to #poss-1 list(
            for j from 0 to #poss#k-1 list(
                w:=for l in keys poss#k#j list cc#k#l#(random length cc#k#l);
                w#0-w#1
                )
            )
        )
    );

--------------------------





-* Documentation section *-

beginDocumentation()



doc ///
  Key
    allMarkovBases
  Headline
    a package to compute all minimal Markov Bases of a given configuration matrix
///

doc ///
  Key
    fiberGraphGenerator
    (fiberGraphGenerator, Matrix)
  Headline
    the relevant fibers of a configuration matrix as graphs
  Usage
    G = fiberGraphGenerator(A)
  Inputs
    A : Matrix
      the configuration matrix
  Outputs
    G : List
      a list of graphs corresponding to relevant fibers of A
  Description
    Text
      This method constructs the relevant fibers of a configuration matrix $A$ using a recursive algorithm.
      The fibres are returned as a list of graphs where two vectors in a fiber are adjacent if their
      supports have non-trivial intersection.
    Example
      fiberGraphGenerator matrix "3,4,5"
      fiberGraphGenerator matrix "1,2,3"
      fiberGraphGenerator matrix "1,2,3,4"
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
    randomMarkovBasis
    (randomMarkovBasis, Matrix)
  Headline
    one randomly chosen minimal Markov basis
  Usage
    B=randomMarkovBasis(A)
  Inputs
    A : Matrix
      the configuration matrix
  Outputs
    B : List
      a Markov basis of A formatted as a list of vectors
  Description
    Text
      this method outputs one randomly chosen Markov basis for a given configuration matrix A
    Example
      randomMarkovBasis matrix "1,2,3"
      randomMarkovBasis matrix "1,2,3,4"
  SeeAlso
    randomMarkovBases
    markovBases
    allMarkovBases
///



doc ///
  Key
    randomMarkovBases
    (randomMarkovBases, Matrix, ZZ)
  Headline
    n randomly chosen minimal Markov bases
  Usage
    B=randomMarkovBases(A,n)
  Inputs
    A : Matrix
      the configuration matrix
    n : ZZ
      a positive integer
  Outputs
    B : List
      a list of n randomly chosen Markov bases
  Description
    Text
      this method outputs n randomly chosen Markov bases for a given configuration matrix A
    Example
      randomMarkovBases(matrix "1,2,3,4",2)
      randomMarkovBases(matrix "1,1,1,1",10)
  SeeAlso
    randomMarkovBasis
    markovBases
    allMarkovBases
///





-* Test section *-

TEST /// -- unique minimal Markov basis for monomial curve in A^3
assert(markovBases matrix "3,4,5" == {{vector {1,-2,1},vector {2,1,-2}, vector {3,-1,-1}}})
///

TEST /// -- two minimal Markov bases for (CI) monomial curve in A^3
assert(markovBases matrix "1,2,3" == {{vector {2,-1,0},vector {3,0,-1}},{ vector {2,-1,0}, vector {1,1,-1}}})
///

TEST /// -- hypersurface in A^3
assert(markovBases matrix "1,2,3;4,5,6" == {{vector {1,-2,1}}})
///

TEST /// -- monomial curve in A^5 with five minimal Markov bases
result := {
    {vector {5, -2, 0}, vector {20, 0, -1}},
    {vector {5, -2, 0}, vector {5, 6, -1}},
    {vector {5, -2, 0}, vector {10, 4, -1}},
    {vector {5, -2, 0}, vector {15, 2, -1}},
    {vector {5, -2, 0}, vector {0, 8, -1}}};
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


elapsedTime pruferSequence(8);


-- if a toric ideal is created by toricMarkov
-- then the information of the matrix A is not cached anywhere
A = matrix {{1,2,3,4,5}}
R = QQ[x_1 .. x_5]
I = toricMarkov(A, R)
peek I.cache -- empty
peek (gens I).cache

-----
-- big to do:
-- check documentation [Ollie]

-- little to dos:
-- 
-- use matrices over vectors [Alex]
-- return the Markov bases as matrices just like "toricMarkov" [Alex]
-- 
-- markovBases(A, R) ---> list of ideals / generating sets in R (just like toricMarkov)
-- use 'toBinomial' (from FourTiTwo) to construct the polynomials from matrices

-- in fiberGenerating function replace Gi with a MutableHashTable [Ollie]

-- combine the functions for generating fibers and add an otpional parameter: ReturnConnectedComponents



-- wibbly wobbly
