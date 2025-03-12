# All Markov Bases for Macaulay2

This repository contains:
- 'AllMarkovBases.m2' - the code for the Macaulay2 package "AllMarkovBases"
- 'paperCode.m2' - the code from the [paper](https://arxiv.org/abs/2502.19031) associated with this package

## Web Interface for Macaulay2 

Try out Macaulay2 at the [Macaulay2 Server](https://www.unimelb-macaulay2.cloud.edu.au/). To load the package on the server, press the 'upload file' button in the top-right corner of the page. 

### Local file upload
It is recommended to save the package 'AllMarkovBases.m2' locally and use 'local file upload' to load the file on the server. After doing this, it should be possible to load the package:

    i1 : needsPackage "AllMarkovBases";
    
    -- storing configuration for package FourTiTwo in /home/m2user/.Macaulay2/init-FourTiTwo.m2
    -- storing configuration for package Graphs in /home/m2user/.Macaulay2/init-Graphs.m2
     -- warning: symbol "tensorProduct" in Graphs.Dictionary is shadowed by a symbol in TensorComplexes.Dictionary
     --   use the synonym Graphs$tensorProduct

     i2 : help AllMarkovBases

### Github upload
It is also possible to perform a direct 'github upload' with:

- Organisation: ollieclarke8787
- Project: WorkshopDurham2024
- Branch or commit: main

However, after performing the github upload, it is necessary append the file location of 'AllMarkovBases.m2' to the 'path' variable in the Macaulay2 session:

    i1 : needsPackage "AllMarkovBases";

    stdio:1:12:(3): error: file not found on path: "AllMarkovBases.m2" 
    i2 : path = {"ollieclarke8787-WorkshopDurham2024-423e8ff/ToricIdeals/"} | path
    
    o2 =  {ollieclarke8787-WorkshopDurham2024-423e8ff/ToricIdeals/,./,.Macaulay2/code/,.Macaulay2/local/share/Macaulay2/,/usr/share/Macaulay2/} 
    
    o2 :  List 
    i3 : needsPackage "AllMarkovBases";
    
    -- storing configuration for package FourTiTwo in /home/m2user/.Macaulay2/init-FourTiTwo.m2
    -- storing configuration for package Graphs in /home/m2user/.Macaulay2/init-Graphs.m2
     -- warning: symbol "tensorProduct" in Graphs.Dictionary is shadowed by a symbol in TensorComplexes.Dictionary
     --   use the synonym Graphs$tensorProduct

     i4 : help AllMarkovBases

**Warning.** The path shown above 'ollieclarke8787-WorkshopDurham2024-423e8ff/ToricIdeals/' may not be correct. To find the correct path, click the 'editor' tab on the left-hand panel and click the 'home button' at the bottom of the page. This will display the file system, which can be navigated to find the folder 'ToricIdeals'. The textbox at the bottom of the panel is populated with the current file location. This file location should be used in place of the aforementioned path. 

## Macaulay2 on Linux / Windows

If you have Macaulay2 available in a terminal (e.g. with a Linux subsystem on Windows), then installing the package can be done as follows. Clone the repository, start an instance of Macaulay2 in this foler, and run:

    loadPackage "AllMarkovBases";

The package is fully documented. For help see:

    help "AllMarkovBases"

or

    viewHelp "AllMarkovBases"

## References

- [Computing all minimal Markov bases in Macaulay2
](https://arxiv.org/abs/2502.19031) - Paper associated to this package
- [Minimal Systems of Binomial Generators and the Indispensable Complex of a Toric Ideal](https://www.jstor.org/stable/20534971) - This package is based on the combinatorial structures of this paper
