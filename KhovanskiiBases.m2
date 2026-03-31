newPackage(
    "KhovanskiiBases",
    Version => "0.1",
    Date => "Oct 15 2025",
    Headline => "computing Khovanskii bases and Cox rings of Mori dream spaces",
    Authors => {
	{ Name => "Courtney George",   Email => "courtney.george@uky.edu",   HomePage => "https://sites.google.com/view/courtneygeorge" },
	{ Name => "Christopher Manon", Email => "Christopher.Manon@uky.edu", HomePage => "https://www.ms.uky.edu/~cama268" },
	{ Name => "Mahrud Sayrafi",    Email => "mahrud@mcmaster.ca",        HomePage => "https://mahrud.github.io" }
	},
    Keywords => { "Toric Geometry" },
    PackageImports => { "gfanInterface" },
    PackageExports => { },
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "adaptedBasis",
    "findMissingGen",
    "khovanskiiBasis",
    "khovanskiiPresentation",
    }

-* Code section *-

-- Function to identify an element that is in J but not in(I).
-- Takes in both ideals and outputs an element.
findMissingGen = method()
findMissingGen(Ideal, Ideal, List) := RingElement => (K, J, D) -> (
    -- initialize a list that will contain all of the missing generators.
    R := ring K;
    -- Initialize a polynomial ring with the variables from J and in(I).
    -- So that elements are ordered, variables are weighted consecutively
    -- so that small y's and large x's are prioritized. Degrees established
    -- so degree is taken only with resect to the y's.
    R' := QQ(monoid[flatten entries vars R,
	MonomialOrder => {
	    Weights => join(toList(#D:0), toList(#(transpose D): -1)),
	    Weights => join(toList(#D:1), toList(#(transpose D):  0)) },
	Global => false]);
    -- the ring maps going between R and R'
    toR  := map(R, R');
    toR' := map(R', R);
    -- find minimal generators of J and make all generators in R'.
    -- Also serves to order the elements by above.
    J' := flatten entries toR'(mingens J);
    -- make all generators of K = in(I) in R'.
    -- Also serves to order the elements by above.
    K' := toR' K;
    -- add missing generators to the list.
    newGens := apply(J', ell -> ell % K');
    -- Since we adopt the min convention, the list is reordered "backwards." Zeros are removed.
    toR first rsort delete(0_R', newGens)
    )

associatedWeight = (w, inB) -> for b in inB list (
    matrix {w} * transpose matrix { first exponents b })_(0,0);

-- Function to extend an algebra generating set to a Khovanskii basis.
-- Input is a weight vector, a polynomial ring, a list of algebra generators,
-- a positive integer (limit), and the diagram matrix.
-- Output is a list of algebra generators with at most one additional generator
-- added to the list to bring it closer to being a Khovanskii basis.
khovanskiiBasis = (w, R, algebraGens, limit, D, count) -> (
    assert(class \ (w, R, algebraGens, limit, D, count) === (List, QuotientRing, List, ZZ, List, ZZ));
    -- number of rays of the ambient toric variety, fixed
    n0 := #D;
    -- number of columns of D
    m0 := # transpose D;
    -- number of algebra generators
    n := #algebraGens;
    -- establish domain polynomial ring. One X for every row of D, one Y for column of D.
    X := local X;
    Y := local Y;
    S := QQ(monoid[X_1..X_n0, Y_1..Y_(n-n0)]);
    -- establish a list of zeros the length of the limit.
    B := new MutableList from toList(limit:0);
    -- zeros from previous list replaced with algebra generators.
    for i from 0 to n - 1 do B#i = algebraGens#i;

    -- establish intermediate polynomial ring
    R' := ambient R;

    -- put algebra generators in previous polynomial ring
    subB := apply((toList B)_(toList(n0..n-1)), i -> sub(i, R'));

    -- take initial forms of algebra generators and sub them into the ring R
    -- ~18% of the computation is here
    inB := flatten prepend((toList B)_(toList(0..(n0-1))), gfanInitialForms(subB, -w));
    inB  = apply(inB, i -> sub(i, R));

    -- map from S to R with target algebra generators
    phi := map(R, S, (toList B)_(toList(0..n-1)));
    -- map from S to R with target initial forms of algebra generators
    psi := map(R, S, inB);

    I := ker phi; -- kernel of first map, phi
    J := ker psi; -- kernel of second map, psi

    if I == 0 then return (D, select(toList B, not zero), I);

    -- creates the weight associated to w in the ring S
    u := associatedWeight(w, inB);

    -- takes initial form wrt u of the elements of the kernel of phi, I
    K := ideal gfanInitialForms(flatten entries mingens I, -u, "ideal" => true);

    while isSubset(J, K) == false do ( -- if the ideals are not yet equal
	if n > limit then ( -- and the algorithm has not yet gone "limit" times
	    break
	    ) else (
	    -- let g be the lowest-degree element of J but not K, then sub into the ring S.
	    g := sub(findMissingGen(K, J, D), S);
	    -- add the image of the new element to the list of algebra generators
	    B#n = phi(g);
	    -- increase the number of algebra generators
	    n = n + 1;
	    -- reestablish subB with new list of generators
	    subB = apply((toList B)_(toList(n0..n-1)), i -> sub(i,R'));
	    -- reestablish inB with new list of algebra generators
	    inB = apply(flatten prepend((toList B)_(toList(0..(n0-1))),gfanInitialForms(subB, -w)), i -> sub(i, R));
	    expG := exponents phi(g);
	    YexpG := for i from 0 to #expG-1 list (expG_i)_{0..m0-1};
	    expVal := min(for i in YexpG list sum(apply(i, D_count, (m,n) -> m*n)));
	    expG = replace(m0+count, expVal, expG_0);

	    -- extend the matrix D by adding a new column corresponding to new variable
	    D = transpose( transpose D | { expG_{m0..m0 + n0 - 1} } );

	    S = QQ(monoid[X_1..X_n0, Y_1..Y_(n-n0)]); -- reestablish ring S

	    phi = map(R, S, (toList B)_(toList(0..n-1))); -- repeat map phi
	    psi = map(R, S, inB); -- repeat map psi

	    I = ker phi; -- kernel of phi
	    J = ker psi; -- kernel of psi

	    -- creates the weight associated to w in the ring S
	    u = associatedWeight(w, inB);

	    -- takes initial form wrt u of the elements of the kernel of phi, I
	    K = ideal gfanInitialForms(flatten entries mingens I, -u, "ideal" => true);
	    )
	);

    -- if "limit" number of iterations is reached, print a warning
    -- and return the progress made on the list of algebra generators
    if n > limit then printerr "limit reached";
    -- otherwise K = J and the list of algebra generators is finished
    (D, toList B, I))

-- Function to rewrite the algebra generators in terms of a basis, determined by the row of D.
adaptedBasis = (L, w, alggens, R) -> (
    -- input is the ideal L, the weight vector row of D, the algebra generators, and the polynomial ring
    -- establish the polynomial ring that orders terms by the weight and breaks ties with lex ordering
    divRing := newRing(R,
	MonomialOrder => { Weights => -w, Lex },
	Global => false);
    -- sub ideal into newly defined ring
    L' := sub(L, divRing);
    -- adapted basis is formed by quotienting each algebra generator
    -- by the new ideal in the newly defined ring and substituting
    -- back into the original ring
    -- TODO: can we reduce the substitutions
    for g in alggens list sub(sub(g, divRing) % L', R))

-- Main function to run through algorithm
khovanskiiPresentation = method() -- TODO: Options => { Limit => infinity }
khovanskiiPresentation(Ideal, List,   ZZ) := List => (L, D,    limit) -> khovanskiiPresentation(L, matrix D, limit)
khovanskiiPresentation(Ideal, Matrix, ZZ) := List => (L, DMat, limit) -> (
    -- L is an ideal of linear relations in the toric vector bundle, i.e. R/L = Sym(E)
    -- D is a matrix encoding the last occurance positions in the Klyachko data
    -- limit is a positive integer, for how many iterations before aborting
    -- We add a zeros row to the bottom of D.
    -- This allows the algorithm to run one additional time
    -- without a weight to homogenize as needed.
    -- TODO: figure out a way not to need the extra row
    D0 := entries(DMat || map(ZZ^1, source DMat, 0));
    n0 := #D0; -- number of rays in the toric variety
    -- R is the quotient ring from the QRing function
    t := local t;
    s := local s;
    -- the quotient ring that serves as the primary ring in the computation.
    -- TODO: maybe use Inverses => true?
    R' := QQ[gens ring L, t_1..t_n0, s_1..s_n0];
    -- list of relations that make t and s units
    I := ideal for i from 1 to n0 list t_i * s_i - 1;
    -- quotient by the previous list to make the variables t and s invertible
    R := R' / I;
    -- a list of ones, one for each t
    oneList := toList(n0 : 1);
    -- a list of ones, one for every future algebra generator
    expT := new MutableList;
    expT#0 = toList(n0 + #transpose(D0):1);

    -- establish starting Khovanskii basis, the inverse of t's
    -- and the variables of the polynomial ring
    KB := new MutableList;
    KB#0 = toList(s_1..s_n0) | gens ring L;

    D := D0;
    B := {};

    newBasis := new MutableList;
    alggens := new MutableList;

    -- run through all of the rows of D, one at a time
    for k from 0 to n0-1 do ( -- almost 100% of the computation is here
	-- weight vector is the row of D and the zero list
	-- to give the variables s and t weight zero
	w := flatten append(D0_k, toList(2*n0 : 0));
	-- form the adapted basis of the of the algebra generators
	-- with respect to the previous weight
	-- ~22% of the computation is here
	alggens#k = adaptedBasis(L, w, KB#k, R);
	-- pass previous list of algebra generators through
	-- khovanskii basis algorithm to add an additional generator,
	-- if needed. Delete any additional zeros if necessary.
	-- ~55% of the computation is here
	(D, B, I) = khovanskiiBasis(w, R, alggens#k, limit, D, k);
	newBasis#k = delete(0, B);

	-- create a list of t's to homogenize the new basis.
	-- Powers of t come from the entries of the matrix.
	expT#(k+1) = flatten prepend(oneList, apply(D_k, j -> t_(k+1)^j));
	-- sub the previous list into the ring R
	expT#(k+1) = apply((expT#(k+1)), j -> sub(j, R));

	-- run through the list of t's and multiply the list through the new basis
	KB#(k+1) = apply(#expT#(k+1), j -> (newBasis#k)_j * (expT#(k+1))_j);
	);
    -- remove the additional variable created for the zero row
    KB#(n0+1) = drop(KB#n0, {n0-1, n0-1});
    -- return the final Khovanskii basis and Cox ring
    (matrix {last KB}, quotient I))

-* Documentation section *-
beginDocumentation()

doc ///
Key
  KhovanskiiBases
Headline
  computing Khovanskii bases and Cox rings of Mori dream spaces
Description
  Text
    This is a package implementing the Khovanskii basis search algorithm
    and, as an application, the Kaveh-Manon algorithm for computing
    a presentation of the Cox ring of a projectivized toric vector bundle
    from [1].
  Example
    S = QQ[y_0, y_1, y_2];
    L = ideal(y_0 + y_1 + y_2);
    D = id_(ZZ^3)
    (KB, R) = elapsedTime khovanskiiPresentation(L, D, 15);
    entries KB
    describe R
-- Acknowledgement
-- Contributors
References
  [1] Kiumars Kaveh and Christopher Manon, Toric flat families, valuations, and applications to projectizied toric vector bundles. @arXiv "1907.00543"@
-- Caveat
-- SeeAlso
-- Subnodes
///

///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

-* Test section *-

TEST /// -- test for findMissingGen
  R = QQ[x,y]
  assert(y == findMissingGen(ideal(x), ideal(x,y), entries id_(ZZ^2)))
///

TEST /// -- test for khovanskiiBasis and adaptedBasis
  S = QQ[y_0, y_1, y_2]
  L = ideal(y_0 + y_1 + y_2)
  D = entries id_(ZZ^3)

  R = QQ[y_0..y_2, t_1..t_4, s_1..s_4]/(
      t_1*s_1-1,t_2*s_2-1,t_3*s_3-1,t_4*s_4-1)
  w = {1,0,0,0,0,0,0,0,0,0,0}

  alggens = {s_1,s_2,s_3,s_4,y_0,y_1,y_2}
  algebraGens = adaptedBasis(L, w, alggens, R)
  assert(algebraGens == {s_1,s_2,s_3,s_4,y_0,-y_0-y_2,y_2})

  limit = 15
  count = 0
  (D', B, L') = khovanskiiBasis(w, R, algebraGens, limit, D, count)
  assert(D' == D)
  assert(B == {s_1,s_2,s_3,s_4,y_0,-y_0-y_2,y_2,0,0,0,0,0,0,0,0})
  assert(toString L' == "ideal(Y_2+Y_3+Y_4)")
///

TEST /// -- test for khovanskiiBasis and adaptedBasis
  S = QQ[y_0, y_1, y_2]
  L = ideal(y_0 + y_1 + y_2)
  D = id_(ZZ^3)

  (KB, R) = elapsedTime khovanskiiPresentation(L, D, 15) -- ~0.56s
  assert(toString net KB == "| s_1 s_2 s_3 -y_1t_1-y_2t_1 y_1t_2 y_2t_3 |")
  assert(toString ideal R == "ideal(X_1*Y_1+X_2*Y_2+X_3*Y_3)")
///

end--

-* Development section *-
restart
debug needsPackage "KhovanskiiBases"
check "KhovanskiiBases"

uninstallPackage "KhovanskiiBases"
restart
installPackage "KhovanskiiBases"
viewHelp "KhovanskiiBases"
