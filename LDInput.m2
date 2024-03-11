

loadPackage "gfanInterface"



findMissingGen = (K,J) -> (  
    newGens0 = {};
    L1 = flatten entries mingens J;
    for i from 0 to #L1-1 do(newGens0 = append(newGens0, L1_i % K));
    newGens = delete(0_S,newGens0);
    return newGens#0;
    )


khovanskiiBasis = (w, polyRing, algebraGens, limit, D) -> ( 
    R = polyRing;
    n = #algebraGens;
    S = QQ[X_1..X_#D, Y_1..Y_(n-#D)];
         
    B = new MutableList from toList(limit:0);
              
    for i from 0 to n - 1 do (
         B#i = algebraGens#i;
     );
     
    R' = QQ[y_1..y_(#transpose(D)),t_1..t_#D];
         
    subB = apply((toList B)_(toList((#D)..n-1)), i -> sub(i,R'));
         
    inB = apply(flatten prepend((toList B)_(toList(0..(#D-1))),gfanInitialForms(subB, -w)), i -> sub(i, R));       
         
    phi = map(R,S, (toList B)_(toList(0..n-1)));
    psi = map(R,S, inB);
         
    I = ker phi;
    J = ker psi;
         
    u = for b in inB list (
    E = matrix{(exponents(b))#0}; 
        matrix{w}*transpose(E))_(0,0)
        ;
         
    if I == 0 then (
        return toList B;
     ) else (
        K = ideal gfanInitialForms(flatten entries mingens I, -u, 
            "ideal" => true);
         
        while (isSubset(J,K) == false) do (
        if n > limit then (
        break
        ) else (
        g = sub(findMissingGen(K,J), S);
        B#n = phi(g);
            n = n + 1;
        subB = apply((toList B)_(toList((#D)..n-1)), i -> sub(i,R'));
        inB = apply(flatten prepend((toList B)_(toList(0..(#D-1))), 
gfanInitialForms(subB, -w)), i -> sub(i, R));
        S = QQ[X_1..X_#D, Y_1..Y_(n-#D)];
         
        phi = map(R,S, (toList B)_(toList(0..n-1)));
        psi = map(R,S, inB);
         
        I = ker phi;
        J = ker psi;
             
        u = for b in inB list (
            E = matrix{(exponents(b))#0}; 
            (matrix{w}*transpose(E))_(0,0)
            );
         
     K = ideal gfanInitialForms(flatten entries mingens I, -u, 
        "ideal" => true);
         )
    );
          
    if n > limit then (
    print "limit reached";
    return toList B;
    ) else (
    return toList B;
        )
      )
    )



adaptedBasis = (L, w, alggens, originalRing) -> (
	divRing = QQ[flatten gens originalRing, MonomialOrder => {Weights => -w, Lex}, Global => false];
	L' = sub(L, divRing);
	alggens' = for i in alggens list sub(i, divRing);
	adaptB = for i in alggens' list i%L';
	adaptB = adaptB / (f -> sub(f,originalRing));
	return adaptB;
)






QRing = (D) -> (
	R'=QQ[y_1..y_(#transpose(D)),t_1..t_#D, s_1..s_#D]; 
	Ilist = {};
	for i from 1 to #D do Ilist = append(Ilist, t_i*s_i-1); 
	R = R'/ideal(Ilist);

	return R;
	)



allRows = (L, DMat, limit) -> (  
    D = append(DMat, toList(#transpose(DMat):0)); 
    R = QRing(D);
    zeroList = toList(2*#D: 0);
    oneList= toList(#D: 1);
    expT_0 = toList(#D+#transpose(D):1);
    kBasis_0 = toList(s_1..s_#D)|toList {y_1..y_(#transpose(D))}_0;

    for k from 0 to (#D-1) do(
    
    almostW_k = {};
    for i in (expT_k)_{#D..#(expT_k)-1} do if i - 1 == 0 then almostW_k = append(almostW_k,0) else almostW_k = append(almostW_k, 1);	
    w_k=flatten append(almostW_k, zeroList); 
    w_0 = flatten append(D_0, zeroList);
    alggens_k = adaptedBasis(L, w_k, kBasis_k, R);

    
    newBasis_k = delete(0, khovanskiiBasis(w_k,R,alggens_k,limit,D)); 
		
    expT_(k+1) = flatten prepend(oneList,apply(D_k, j->t_(k+1)^j)); 
    extraTs = {};
    if k < #D-2 then (for i from 1 to (#newBasis_k - #(expT_(k+1))) do
    (extraTs = append(extraTs,t_(k+1)));
    expT_(k+1) = flatten append((expT_(k+1)), extraTs));
    
    expT_(k+1) = apply((expT_(k+1)), j -> sub(j, R)); 
		
    kBasis_(k+1) = {};
		
    for j from 0 to #(expT_(k+1))-1 do( 
        kBasis_(k+1) = append(kBasis_(k+1), (newBasis_k)_j*((expT_(k+1))_j)); 
    
    if k < #D-2 then if #D_k != (#expT_(k+1)-#D) then D = entries(matrix D | matrix (for i in replace(k,1,toList(#D:0)) list {i}));
    R = QRing(D);
	));
    return kBasis_#D;
	)



makeGenMatrix = (m, n) -> (
M = fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n));
vGen = isVeryGeneral(M);
while vGen == false do(M = fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n))+fillMatrix(mutableMatrix(ZZ,m,n));
vGen = isVeryGeneral(M););
return M
)


isVeryGeneral = (mat) -> (
m = # entries mat;
n = # entries transpose mat;
k = min(m,n);
bVal = for i from 1 to k list ((#flatten entries gens minors(i,matrix mat)) == ((m!)/((i!)*(m-i)!))*((n!)/((i!)*(n-i)!)));
return all(bVal, i -> i == true)
) 

makeL = (m,n) -> (
mat = makeGenMatrix(m,n);
n = # entries transpose mat;
m = # entries mat;
coeff = entries mat;
iRing = QQ[y_1..y_n];
for i from 0 to m-1 do gen_i = sum(for j from 0 to n-1 list(((coeff_i)_j)*y_(j+1)));
genGens = for i from 0 to m-1 list gen_i;
I = ideal(genGens);
return I
)

makeD = (m,n) -> (
M = for i from 0 to m-1 list new MutableList from toList(n:0);
for i from 0 to m-1 do((M_i)#(2*i) = 1; (M_i)#((2*i)+1) = 1;);
M = for i from 0 to m-1 list toList M_i;
return M
)

