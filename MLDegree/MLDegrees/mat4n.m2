-- code for writing down matroid strata:
-- matroids on [n] elements
-- of rank 4

load "matroids.m2"


-- loadMatroid : load list of matroids from a file
--
-- File format
-- > Each line of the file must be text involving "*" and "0"
-- > The end of each line is given by "\n"
-- > Each line encodes a matroid by its bases:
--   -- order the r-subsets of [n] in RevLex order
--   -- write * if the subset is a basis and 0 if not
--
-- Options:
-- FileName : String : name of the file 
--                     if it is "allrRnN.txt" then we replace R and N
--                     with the rank (r) and ground set size (n)
--
-- MinBases : ZZ : include only matroids with at least MinBases many bases
--                 if MinBases = -1 then include only matroid at least
--                 1 + r(n-r) many bases

loadMatroids = method(
    Options => {
        FileName => "allrRnN.txt", -- R -> rank, N -> ground set size
        MinBases => -1,
	Verbose => false,
	StartLine => 0, -- Start at this line number (0-indexed)
	StopLine => -1  -- Stop at this line number (0-indexed), i.e., don't include this line
	}
    )

loadMatroids(ZZ, ZZ) := opts -> (r, n) -> (
    -- if user supplies a file name then use that one
    -- otherwise we reformat the default one
    fileName := (
        if opts.FileName == "allrRnN.txt" then (
            rankText := toString r;
            nText := if n < 10 then "0" | toString n else toString n;
            replace("R", rankText, replace("N", nText, opts.FileName))
            )
        else (
            opts.FileName
            )
        );
    if opts.Verbose then print ("-- loading file: " | fileName);
    file := openIn fileName;
    lineLength := binomial(n, r) + 2; -- "+2" for "\n" characters
    minBases := if opts.MinBases == -1 then 1 + r*(n-r) else opts.MinBases; 
    subsetList := subsets(n, r);
    numberLines := fileLength file // lineLength;
    
    tick := currentTime();
    if opts.Verbose then (
	print ("-- file contains " | toString numberLines | " lines");
	print ("-- extracting matroids with at least " | toString minBases | " bases");
	print ("-- parsing [current line number / total line numbers]:");
	);
    for lineNo from 0 to numberLines -1 list (
        if opts.Verbose and tick + 3 < currentTime() then (
	    tick = currentTime();
	    print ("-- " | toString lineNo | "/" | toString numberLines);
	    );
	line := read(file, lineLength);
        if line == "" then break;
	if lineNo < opts.StartLine then continue;
        if lineNo == opts.StopLine then break;
	numberBases := (tally line)#"*";
        if numberBases < minBases then continue else (
            matroid for i from 0 to lineLength -3 list (
                if line_i == "*" then subsetList_i else continue
                )
            )
        )
    )


-- isSpecial : check is a matroid is special
-- 
-- A matroid is special if there exists a basis B such that
-- for each i \in B and j \in [n]\B we have:
-- (B-i)+j is a basis 
-- 

isSpecial = method(
    Options => {
	Verbose => false
	}
    )
isSpecial Matroid := opts -> M -> (
    B := bases M;
    specialBases := new MutableHashTable from for b in B list b => true;
    hasSpecialBasis := false;
    for b in B do (
	if opts.Verbose then print ("-- checking b = " | net b);
	if not specialBases#b then continue else (
	    if opts.Verbose then print ("-- b has not already been ruled out");
	    isThisBasisSpecial := true;
	    for i in keys b do ( -- look at b-i
		modsAreSpecial := true;
	    	bMods := for j in keys (M.groundSet - b) list ( -- b' = b-i+j (b modification)
		    b' := b - set{i} + set{j};
		    if specialBases#?b' then b' else (
			if opts.Verbose then print ("-- non-basis: b - " | toString i | " + " | toString j);
			modsAreSpecial = false; 
			continue
			) 
		    );
		if not modsAreSpecial then (
		    if opts.Verbose then print ("-- deduce non-special bases: " | net bMods);
		    for b' in bMods do (
			specialBases#b' = false;
			);
		    isThisBasisSpecial = false;
		    break
		    )
		);
	    if isThisBasisSpecial then (
		hasSpecialBasis = true; 
		break
		);
	    )
	);
    hasSpecialBasis
    )

-- beta invariant of a matroid
-- b(M) = (-1)^(rk(M) -1) * d/dx X_M(x) |_1
-- in words: the beta invariant is the normalised (absolute value)
-- of the evaluation at x=1 of the derivative of the characteristic polynomial
-- of the matroid
beta = method ()
beta Matroid := M -> (
    X := characteristicPolynomial M;
    x := (ring X)_0;
    X' := diff(x, X);
    abs sub(X', x => 1)
    )

end --

load "mat4n.m2"
M = loadMatroids(4, 9, Verbose => true, StartLine => 180000, StopLine => -1);
#M
specialM = select(M, isSpecial);
#specialM
betaInvariants = apply(specialM, m -> beta m);
tally betaInvariants


-- Results:
-- r = 4, n = 8:
       Tally{1 => 1  }
             2 => 6
             3 => 10
             4 => 16
             5 => 17
             6 => 26
             7 => 27
             8 => 33
             9 => 29
             10 => 47
             11 => 59
             12 => 74
             13 => 84
             14 => 67
             15 => 40
             16 => 20
             17 => 7
             18 => 3
             19 => 1
             20 => 1

-- r = 4, n = 9:
-- Lines 0 to 20K
       Tally{23 => 41  }
             24 => 697
             25 => 3442
             26 => 6537
             27 => 5682
             28 => 2619
             29 => 752
             30 => 166
             31 => 37
             32 => 9
             33 => 3
             34 => 1
             35 => 1

-- lines 20K - 40K
o154 = Tally{22 => 9   }
             23 => 356
             24 => 2477
             25 => 6125
             26 => 6562
             27 => 3322
             28 => 901
             29 => 165
             30 => 26
             31 => 4
             32 => 1

-- lines 40K - 60K
o7 = Tally{22 => 6   }
           23 => 770
           24 => 4700
           25 => 7813
           26 => 4983
           27 => 1430
           28 => 207
           29 => 18
           30 => 1

-- lines 60K - 80K
o7 = Tally{18 => 1   }
           19 => 4
           20 => 15
           21 => 70
           22 => 667
           23 => 3290
           24 => 6361
           25 => 5742
           26 => 2769
           27 => 772
           28 => 137
           29 => 17
           30 => 2
	   
-- lines 80K - 100K
o7 = Tally{20 => 1   }
           21 => 44
           22 => 803
           23 => 4140
           24 => 7231
           25 => 5466
           26 => 1881
           27 => 304
           28 => 26
           29 => 1

-- lines 100K - 120K
o7 = Tally{14 => 1   }
           15 => 1
           16 => 3
           17 => 4
           18 => 7
           19 => 36
           20 => 254
           21 => 1209
           22 => 3920
           23 => 5941
           24 => 4774
           25 => 2282
           26 => 804
           27 => 238
           28 => 59
           29 => 13
           30 => 4
           31 => 1

-- lines 120K - 140K
o7 = Tally{19 => 8   }
           20 => 54
           21 => 596
           22 => 3169
           23 => 6403
           24 => 5941
           25 => 2842
           26 => 716
           27 => 102
           28 => 11
           29 => 1

-- lines 140K - 160K
o7 = Tally{15 => 1   }
           16 => 2
           17 => 12
           18 => 83
           19 => 586
           20 => 2223
           21 => 5222
           22 => 6279
           23 => 3692
           24 => 1159
           25 => 231
           26 => 39
           27 => 6
           28 => 1

-- lines 160K - 180K
o7 = Tally{13 => 4   }
           14 => 28
           15 => 95
           16 => 278
           17 => 762
           18 => 1805
           19 => 3590
           20 => 5081
           21 => 4410
           22 => 2283
           23 => 690
           24 => 138
           25 => 19
           26 => 2

-- lines 180K - end
o7 = Tally{1 => 1    }
           2 => 9
           3 => 20
           4 => 34
           5 => 48
           6 => 75
           7 => 93
           8 => 133
           9 => 168
           10 => 265
           11 => 361
           12 => 486
           13 => 632
           14 => 731
           15 => 748
           16 => 897
           17 => 1049
           18 => 985
           19 => 543
           20 => 179
           21 => 49
           22 => 17
           23 => 5
           24 => 2
           25 => 1
