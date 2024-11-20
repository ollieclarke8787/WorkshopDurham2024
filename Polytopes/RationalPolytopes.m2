newPackage(
    "RationalPolytopes",
    Version => "0.1",
    Date => "",
    Headline => "A package for Ehrhart theory of rational polytopes",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Polyhedra"}
    )

export {"fx"}

-* Code section *-
fx = x -> x^2;


-* Documentation section *-
beginDocumentation()

doc ///
  Key
    RationalPolytopes
  Headline
    A package for Ehrhart theory of rational polytopes
///


doc ///
  Key
    fx
  Headline
    a function
  Usage
    n = fx a
  Inputs
    a : ZZ
      a number to be squared
  Outputs
    n : ZZ
      the square of a
  Description
    Text
      it squares things
    Example
      fx 4
      fx 2
  SeeAlso
    RationalPolytopes
///


-* Test section *-
TEST /// -- (0)
assert(1 == fx 1)
///

end--

-* Development section *-
restart
debug needsPackage "RationalPolytopes"
check "RationalPolytopes"

uninstallPackage "RationalPolytopes"
restart
installPackage "RationalPolytopes"
viewHelp "RationalPolytopes"
