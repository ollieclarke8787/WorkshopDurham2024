

--This method computes every minimal Markov basis for a given configuration matrix
--To run the method allMarkovBases you will need the following 2 packages

loadPackage "FourTiTwo"
loadPackage "Graphs"

allMarkovBases = method();
allMarkovBases Matrix := A -> (
    n=length (entries A)_0;
    M=toricMarkov A;
    d=length entries M;
    
    L={};
    vales={};
    Md={};
    
    for i from 0 to d-1 do(
        temp={};
        for j from 0 to n-1 do(
            if M_(i,j) < 0 then temp= append(temp,0)
            else temp=append(temp, M_(i,j));
            );
        val=(A * transpose matrix{temp});
        if (not isMember(val,vales)) then L=append(L,{temp,val});
        vales=append(vales,val);
        Md=append(Md, vector transpose M^{i});
        Md=append(Md, - vector transpose M^{i});
        );
    
    pos = z -> if z<0 then false else true;
    inters = (x,y) -> if (x>0 and y>0) then false else true;
    
    G={};
    
    for k from 0 to (length L) -1 do(
        stk={vector (L_k)_0};
        G=append(G,graph({vector (L_k)_0},{}));
        while (not length stk == 0) do(
            cur=stk_0;
            for i from 0 to (length Md)-1 do(
                ck = (Md_i + cur);
                if isMember(ck, vertexSet G_k) then continue;
                if all(entries ck,pos) then (
                    stk=append(stk,ck);
                    G=replace(k,addVertex(G_k,ck),G);
                    for v in (vertexSet G_k) do(
                        if (not all(entries ck,entries v,inters)) then (
                            G=replace(k,addEdges'(G_k,{{ck,v}}),G);
                            );
                        );
                    );
                );
            stk=drop(stk,1);
            );
        );
    
    cc={};
    
    for k from 0 to (length G)-1 do(
        cc = append(cc,connectedComponents G_k);
        );
    
    poss={};
    
    prod = (u,v) -> for le in u ** v list(toList(le));
    prod3 = (u,v) -> for le in prod(u,v) list(flatten(le));
    prod2 = method();
    prod2 List := x -> (
        curr=x_0;
        for w from 1 to (length x)-1 do curr=prod3(curr,x_w);
        curr
        );
    
    prod4 = method();
    prod4 List := x -> (
        curr={};
        for w in prod3(x_0,x_1) do curr=append(curr,w_0-w_1);
        curr
        );
    
    prufer = method();
    prufer ZZ := a ->(
        out={};
        ite = prod2 (splice {(a-2):toList(0..(a-1))});
        for i in ite do(
            cg = graph(toList(0..(a-1)),{});
            deg=for l from 0 to a-1 list(1);
            for j in i do(
                deg=replace(j,(deg_j)+1,deg);
                );
            for j in i do(
                for l from 0 to a-1 do(
                    if (deg_l==1) then(
                        cg = addEdge(cg,set {l,j});
                        deg=replace(j,(deg_j)-1,deg);
                        deg=replace(l,(deg_l)-1,deg);
                        break;
                        );
                    );
                );
            pss=positions(deg,x -> if x==1 then true else false);
            cg = addEdge(cg,set pss);
            out=append(out,edges(cg));
            );
        out
        );
    
    for k from 0 to (length G)-1 do(
        cl = length cc_k;
        if cl==2 then (
            poss=append(poss,{{set {0,1}}});
            continue;
            );
        if cl==3 then (
            poss=append(poss,{{set {0,1},set {1,2}},{set {0,1},set {0,2}},{set {0,2},set {1,2}}});
            continue;
            );
        poss=append(poss,prufer cl);
        );
    
    fin={};
    
    
    for k from 0 to (length poss)-1 do(
        tin={};
        for i from 0 to (length poss_k)-1 do(
            tm2={};
            for j from 0 to (length (poss_k)_i)-1 do(
                tm={};
                for l in keys ((poss_k)_i)_j do(
                    tm = append(tm,(cc_k)_l);
                    );
                tm2=append(tm2,prod4(tm));
                );
            tin=tin | prod2(tm2);
            );
        fin=append(fin,tin);
        );
    prod2(fin)
);

end

--Examples
allMarkovBases matrix "3,4,5"
allMarkovBases matrix "1,2,3"
allMarkovBases matrix "1,1,1,1"
allMarkovBases matrix "1,2,3,4"
allMarkovBases matrix "1,2,3;4,5,6"
