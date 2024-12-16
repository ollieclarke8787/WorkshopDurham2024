

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
    "markovBases"
    }



-* Code *-

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
    );



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



listProd = method();
listProd List := Ls -> (
    lP := (pr,ad) -> (
        flatten for i in pr list(for el in ad list(append(i,el)))
        );
    cur := {{}};
    for j in Ls do(
        cur=lP(cur,j);
        );
    cur
    );



markovBases = method();
markovBases Matrix := A -> (
    G:=fiberGraphGenerator A;
    cc:=for j from 0 to (length G)-1 list(connectedComponents G_j);
    poss:=for k from 0 to (length G)-1 list(pruferSequence length cc_k);
    fin:=listProd(for k from 0 to (length poss)-1 list(flatten for i from 0 to (length poss_k)-1 list(listProd(for j from 0 to (length (poss_k)_i)-1 list(for w in listProd(for l in keys ((poss_k)_i)_j list((cc_k)_l)) list(w_0-w_1))))));
    for m in fin list(flatten m)
    );




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
    (pruferSequence, ZZ)
  Headline
    the edge set of every spanning tree on n vertices via Prüfer's algorithm
  Usage
    E=pruferSequence(n)
  Inputs
    n : ZZ
      the number of vertices of the tree
  Outputs
    L : List
      a list of edge sets corresponding to every spanning tree on n nodes
  Description
    Text
      this method constructs the edge set of every spanning tree on n nodes via Prüfer's algorithm
    Example
      pruferSequence 3
      pruferSequence 4
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
uninstallPackage "allMarkovBase"
restart
installPackage "allMarkovBases"

check allMarkovBases
