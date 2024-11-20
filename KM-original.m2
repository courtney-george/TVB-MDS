loadPackage "gfanInterface"

--Function to identify an element that is in J but not in(I). Takes in both ideals and outputs an element.
findMissingGen = (K,J) -> (
    newGens0 = {}; --initialize a list that will contain all of the missing generators.
    orderingRing = QQ[flatten entries vars ring J, MonomialOrder => {Weights => join(toList(#newD:0), toList(#(transpose newD): -1)), Weights => join(toList(#newD:1), toList(#(transpose newD): 0))}, Global=>false];
    --Initialize a polynomial ring with the variables from J and in(I). So that elements are ordered, variables are weighted consecutively so that small y's and large x's are prioritized. Degrees established so degree is taken only with resect to the y's.
    L1 = flatten entries mingens J;
    L1 = apply(L1, i -> sub(i, orderingRing)); -- make all generators of L in the orderingRing. Also serves to order the elements by above.
    K = ideal(apply(flatten entries gens K, i -> sub(i, orderingRing))); --make all generators of in(I) in the orderingRing. Also serves to order the elements by above.
    for i from 0 to #L1-1 do(newGens0 = append(newGens0, L1_i % K)); --add missing generators to the list.
    newGens = rsort delete(0_orderingRing,newGens0); --Since we adopt the min convention, the list is reordered "backwards." Zeros are removed.
    return newGens#0;
    )


--Function to extend an algebra generating set to a Khovanskii basis. Input is a weight vector, a polynomial ring, a list of algebra generators, a positive integer (limit), and the diagram matrix. Output is a list of algebra generators with at most one additional generator added to the list to bring it closer to being a Khovanskii basis.

khovanskiiBasis = (w, polyRing, algebraGens, limit, D,count) -> (
    R = polyRing; --rename the polynomial ring
    n = #algebraGens; --number of algebra generators
    numVars = #D + #(transpose D);
    S = QQ[X_1..X_#D, Y_1..Y_(n-#D)]; --establish domain polynomial ring. One X for every row of D, one Y for column of D.
    B = new MutableList from toList(limit:0); --establish a list of zeros the length of the limit.
    for i from 0 to n - 1 do (
	B#i = algebraGens#i; --zeros from previous list replaced with algebra generators.
	);


    R' = QQ[(gens R)_{0..#transpose(D)-1},t_1..t_#D, s_1..s_#D]; --establish intermediate polynomial ring

    subB = apply((toList B)_(toList((#D)..n-1)), i -> sub(i,R')); --put algebra generators in previous polynomial ring

    inB = apply(flatten prepend((toList B)_(toList(0..(#D-1))), gfanInitialForms(subB, -w)), i -> sub(i, R)); --take initial forms of algebra generators and sub them into the ring R

    phi = map(R,S, (toList B)_(toList(0..n-1))); --map from S to R with target algebra generators
    psi = map(R,S, inB); --map from S to R with target initial forms of algebra generators

    I = ker phi; --kernel of first map, phi
    J = ker psi; --kernel of second map, psi

    u = for b in inB list (
	E = matrix{(exponents(b))#0};
	matrix{w}*transpose(E))_(0,0)
    ; --creates the weight associated to w in the ring S

    if I == 0 then (
	return toList B;
	) else (
	K = ideal gfanInitialForms(flatten entries mingens I, -u, "ideal" => true); --takes initial form wrt u of the elements of the kernel of phi, I

	while (isSubset(J,K) == false) do ( --if the ideals are not yet equal
	    if n > limit then ( --and the algorithm has not yet gone "limit" times
		break
		) else (
		g = sub(findMissingGen(K,J), S); --let g be the lowest-degree element of J but not K, then sub into the ring S.
		B#n = phi(g); --add the image of the new element to the list of algebra generators
		n = n + 1; --increase the number of algebra generators
		subB = apply((toList B)_(toList((#D)..n-1)), i -> sub(i,R')); --reestablish subB with new list of generators
		inB = apply(flatten prepend((toList B)_(toList(0..(#D-1))),gfanInitialForms(subB, -w)), i -> sub(i, R)); --reestablish inB with new list of algebra generators
		expG = exponents phi(g);
		YexpG = for i from 0 to #expG-1 list (expG_i)_{0..#transpose(D)-1};
		expVal = min(for i in YexpG list sum(apply(i, D_count, (m,n) -> m*n)));
		expG = replace(#transpose(D)+count, expVal, expG_0);

		newD = transpose( transpose newD | { (expG)_{#transpose(D)..#transpose(D) + #D - 1} } ); --expend the matrix D by adding a new column corresponding to new variable

		S = QQ[X_1..X_#D, Y_1..Y_(n-#D)]; --reestablish ring S

		phi = map(R,S, (toList B)_(toList(0..n-1))); --repeat map phi
		psi = map(R,S, inB); --repeat map psi

		I = ker phi; --kernel of phi
		J = ker psi; --kernel of psi

		u = for b in inB list (
		    E = matrix{(exponents(b))#0};
		    (matrix{w}*transpose(E))_(0,0)
		    ); --creates the weight associated to w in the ring S

		K = ideal gfanInitialForms(flatten entries mingens I, -u, "ideal" => true); --takes initial form wrt u of the elements of the kernel of phi, I
		)
	    );

	if n > limit then (
	    print "limit reached"; --if "limit" number of iterations is reached, stop and print
	    return toList B; --even if "limit" is reached, return the progress made on the list of algebra generators
	    ) else (
	    return toList B; --if K=J, done and return list of algebra generators
	    )
	)
    )



--Function to rewrite the algebra generators in terms of a basis, determined by the row of D.
adaptedBasis = (L, w, alggens, originalRing) -> (--input is the ideal L, the weight vector row of D, the algebra generators, and the polynomial ring
    divRing = QQ[flatten gens originalRing, MonomialOrder => {Weights => -w, Lex}, Global => false]; --establish the polynomial ring that orders terms by the weight and breaks ties with lex ordering
    L' = sub(L, divRing); --sub ideal into newly defined ring
    alggens' = for i in alggens list sub(i, divRing); --sub algebra gens into newly defined ring
    adaptB = for i in alggens' list i%L'; --adapted basis is formed by quotienting each algebra generators by the new ideal
    adaptB = adaptB / (f -> sub(f,originalRing)); --sub the adapted basis back into the original ring
    return adaptB; --return the adapted basis
    )






--Function to establish the quotient ring that serves as the primary ring in the computation.
QRing = (L,D') -> ( --imput is ideal and diagram matrix
    tempR = QQ[gens ring L,t_1..t_#D', s_1..s_#D']; --polynomial ring with all the necessary variables
    Ilist = {};
    for i from 1 to #D do Ilist = append(Ilist, t_i*s_i-1); --list of relations that make t and s units
    R = tempR/ideal(Ilist); --quotient by the previous list to make the variables t and s invertible
    return R; --return the quotient ring
    )



--Main function to run through algorithm
KM = (L, DMat, limit) -> (  --input is ideal L, matrix D, and positive integer "limit"
    D' = append(DMat, toList(#transpose(DMat):0)); --add a zeros row to the bottom of D. Allows the algorithm to run one additional time without a weight to homogenize as needed.
    R = QRing(L, D'); --R is the quotient ring from the QRing function
    zeroList = toList(2*#D': 0); --a list of zeros, one for each s and t
    oneList= toList(#D': 1); --a list of ones, one for each t
    expT_0 = toList(#D'+#transpose(D'):1); --a list of ones, one for every future algebra generator
    kBasis_0 = toList(s_1..s_#D')| gens ring L; --establish starting basis, the inverse of t's and the variables of the polynomial ring
    newD = D'; --begin with newD as the matrix D'

    for k from 0 to (#D'-1) do( --run through all of the rows of D, one at a time

	w_k=flatten append(D'_k, zeroList); --weight vector is the row of D and the zero list to give the variables s and t weight zero
	alggens_k = adaptedBasis(L, w_k, kBasis_k, R); --form the adapted basis of the of the algebra generators with respect to the previous weight
	newBasis_k = delete(0, khovanskiiBasis(w_k,R,alggens_k,limit,D',k)); --pass previous list of algebra generators through khovanskii basis algorithm to add an additional generator, if needed. Delete any additional zeros if necessary.


	expT_(k+1) = flatten prepend(oneList,apply(newD_k, j->t_(k+1)^j)); --create a list of t's to homogenize the new basis. Powers of t come from the entries of the matrix.
	expT_(k+1) = apply((expT_(k+1)), j -> sub(j, R)); --sub the previous list into the ring R

	kBasis_(k+1) = {};

	for j from 0 to #(expT_(k+1))-1 do( --run through the list of t's
	    kBasis_(k+1) = append(kBasis_(k+1),(newBasis_k)_j*((expT_(k+1))_j)); --multiply the list through the new basis
	    R = QRing(L,newD);
	    )
	);
    return drop(kBasis_#D', {#D'-1, #D'-1}); --return basis and remove the additional variable created for the zero row

    )
