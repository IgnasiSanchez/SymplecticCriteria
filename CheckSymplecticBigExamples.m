/* This function computes the p-torsion basis of an elliptic curve E defined over a finite field FF_z, the extension of F_l by a p-th root of unity.
 *
 * Input:
 *    - E is assumed to be over FF_z.
 *    - p is a prime. 
 *    - Verbose (optional): if true, it prints timing information.
 */
function computeTorsionBasis(E, p : Verbose := true)
    
    FF := BaseRing(E);
    Fl := BaseField(FF);
    PolyFF<x> := PolynomialRing(FF);
    PolyFl<y> := PolynomialRing(Fl);

    t00 := Realtime();
    f := DivisionPolynomial(E, p);
    ff := PolyFl!f;
    F := Factorization(ff);

    if Verbose then
        print "Time to compute and factor p-division polynomial:", Realtime(t00), "seconds";
        print "Number of irreducible factors:", #F;
        print "Degrees of factors:", [Degree(ff[1]) : ff in F];
    end if;
    

    smallDegFactors := [ff[1] : ff in F | Degree(ff[1]) eq Degree(F[1][1])];
    bigDegFactors := [ff[1] : ff in F | Degree(ff[1]) gt Degree(F[1][1])];
    ff_small := &*smallDegFactors;

    smallDegFactorsInFF := [f[1] : f in Factorization(PolyFF!ff_small)];

    t00 := Realtime();
    if Degree(smallDegFactorsInFF[1]) eq 1 then
        FF_small := FF;
        a := -Coefficients(smallDegFactorsInFF[1])[1];
    else
        FF_small<a> := ext<FF | smallDegFactorsInFF[1]>;
    end if;

    PolyFF_small<yy> := PolynomialRing(FF_small);
    E_small := EllipticCurve([FF_small!a : a in aInvariants(E)]);
    fESmall := Evaluate(DefiningPolynomial(E_small), [a, yy, 1]);
    quadExtComputed := 0;
    if IsIrreducible(fESmall) then
        FF_small<aY> := ext<FF_small | fESmall>;
        quadExtComputed := 1;
    else
        aY := Roots(fESmall, FF_small)[1][1];
    end if;

    E_small := EllipticCurve([FF_small!a : a in aInvariants(E_small)]);
    P1 := E_small![a, aY, 1];

    if Verbose then
        print "Creation of small field took", Realtime(t00), "seconds";
        print "Small field degree:", Degree(FF_small);
        print "First torsion point P1 found over field of degree:", Degree(Parent(P1[1]));
    end if;

    t00 := Realtime();
    E2, phi := IsogenyFromKernel(E_small, PolyFl!ff_small);
    if Verbose then
        print "Time to compute Isogeny:", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    phid := DualIsogeny(phi);
    if Verbose then
        print "Time to compute dual isogeny:", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    K := Kernel(phid);
    if Verbose then
        print "Time to compute kernel of dual isogeny:", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    pts := Points(K);
    if Verbose then
        print "Time to compute points on kernel:", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    P := 1;
    for pt in pts do
        if pt eq E2!0 then
            continue;
        else
            P := pt;
            break;
        end if;
    end for;
    if Verbose then
        print "Time to find a point in kernel:", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    f_x := IsogenyMapPhi(phi);
    x_coord_num := f_x - P[1]*IsogenyMapPsiSquared(phi);
    if Verbose then
        print "Time to compute x_coord polynomial:", Realtime(t00), "seconds";
    end if;


    t00 := Realtime();
    FF_big<b> := ext<FF_small | x_coord_num>;
    if Verbose then
        print "Creation of big field took", Realtime(t00), "seconds";
    end if;
    t00 := Realtime();
    PolyFF_big<z> := PolynomialRing(FF_big);
    E_big := EllipticCurve([FF_big!a : a in aInvariants(E_small)]);
    if Verbose then
        print "Took ", Realtime(t00), "seconds to change ring to big field";
    end if;
    t00 := Realtime();
    fEBig := Evaluate(DefiningPolynomial(E_big), [b, z, 1]);
    if Verbose then
        print "It took ", Realtime(t00), "seconds to check if quadratic extension is needed";
    end if;
    t00 := Realtime();
    if quadExtComputed eq 0 and IsIrreducible(fEBig) then
        FF_big<bY> := ext<FF_big | fEBig>;
    else
        isSq, bYsq := IsSquare(Discriminant(fEBig));
        if isSq then
            cfs := Coefficients(fEBig);
            bY := (- cfs[2] + bYsq)/(2*cfs[3]);
        else
            error "Discriminant for fEBig is nonsquare but polynomial is not irreducible.";
        end if;
    end if;
    if Verbose then
        print "Took ", Realtime(t00), "seconds to construct quadratic extension";
    end if;

    t00 := Realtime();
    E_big := EllipticCurve([FF_big!a : a in aInvariants(E_big)]);
    P2 := E_big![b, bY, 1];
    if Verbose then
        print "Creation of P2 and changing ring took", Realtime(t00), "seconds";
        print "Big field degree:", Degree(FF_big);
    end if;
    
    return P1, P2, FF_small, FF_big, E_small, E_big;
end function;

/* Given P1, P2 the basis of the p-torsion module of E, both defined over FF_big (i.e. E has to be defined over FF_big), this function does the following: 
 *      - It computes WP(P1, P2) to check if the basis is symplectic or not. If not, it replaces P2 by -P2.
 *      - It computes WP(P2, Frob_ell(P2)) where Frob_ell is the Frobenius at ell (the characteristic of the base field of E).
 *      - It returns (k1, k2) where WP(P1, P2) = zeta^k1 and WP(P2, Frob_ell(P2)) = zeta^k2, where zeta is a fixed primitive p-th root of unity.
 *      - If computeRepresentation is true, it also computes the matrix of rho_{E,p}(Frob_ell) in the basis P1, P2 and prints it in the screen. 
 * Input:
 *     - P1, P2: points in E[p] forming a basis of the p-torsion module of E.
 *     - E_big: an elliptic curve defined over FF_big such that P1, P2 are defined over FF_big.
 *     - p: a prime.
 *     - zeta: a fixed primitive p-th root of unity. It tries to embed zeta into FF_big, throwing an error if its not possible (it should not be a problem
 *             since FF_big is expected to contain the base field of zeta, by construction in the function computeTorsionBasis). 
 *     - computeRepresentation (optional): if true, it computes the matrix of rho_{E,p}(Frob_ell) in the basis P1, P2.
 * 
 */ 
function computeWP(P1, P2, E_big, p, zeta : computeRepresentation := false)

    Zp := Integers(p);

    FF_big := BaseRing(E_big);
    if Degree(FF_big) / Degree(BaseField(FF_big)) eq 2 then
        FF_big := BaseField(FF_big);
    end if;    
    FF_small := BaseField(FF_big);
    if Degree(FF_small) / Degree(BaseField(FF_small)) eq 2 then
        FF_small := BaseField(FF_small);
    end if;
    if Degree(BaseField(FF_small)) eq 1 then
        FF_z := FF_small;
    else
        FF_z := BaseField(FF_small);
    end if;

    ell := Characteristic(FF_z);
    
    try
        Embed(Parent(zeta), FF_big);
    catch e
        error "Embedding failed base field of zeta into base field of E_big failed";
    end try;

    zetaInFF_z := FF_z!zeta;
    powOfZeta := [k : k in [1..p] | zetaInFF_z eq FF_z.1^k][1];

    P1_big := E_big!P1;
    P2_big := E_big!P2;
    WPP1P2 := WeilPairing(P1_big, P2_big, p);

    k1 := [k : k in [1..p] | zetaInFF_z^k eq WPP1P2][1];

    if p mod 4 eq 3 then
        ns := -1;
    else
        _:=exists(ns){ x : x in [1..p] | not IsSquare(GF(p)!x) };
    end if;

    if not IsSquare(Zp!k1) then
        P2 := P2 * ns;
    end if;

    if computeRepresentation then

        FrobP1 := E_big![P1_big[1]^ell, P1_big[2]^ell];
        FrobP2 := E_big![P2_big[1]^ell, P2_big[2]^ell];
        
        coeffsP1 := [];
        coeffsP2 := [];
        
        for a,b in [0..p-1] do
            if a*P1 + b*P2 eq FrobP1 then
                Append(~coeffsP1, [a,b]);
            end if;
            if a*P1 + b*P2 eq FrobP2 then
                Append(~coeffsP2, [a,b]);
            end if;
        end for;

        print "Matrix of rho_{E,p}(Frob_ell) in the basis P1, P2:";
        print GL(2,p)!Transpose(Matrix([coeffsP1[1], coeffsP2[1]]));

    end if;

    FrobEllP2 := E_big![P2[1]^ell, P2[2]^ell];

    WPP2FrobP2 := WeilPairing(P2, FrobEllP2, p);

    k2 := [k : k in [1..p] | zetaInFF_z^k eq WPP2FrobP2][1];

    return Zp!(k1*powOfZeta), Zp!(k2*powOfZeta);
end function;

p := 211;
ell := 73;
FF := GF(ell);
PolyFF<x> := PolynomialRing(FF);
f_z := Factorization(x^p-1);
FF_z<zeta> := ext<FF|f_z[2][1]>;
PolyFF<x> := PolynomialRing(FF_z);

E_1 := EllipticCurve([FF_z | 0, 0, 0, 70, 6]);
E_2 := EllipticCurve([FF_z | 0, 0, 0, 55, 5]);
E_3 := EllipticCurve([FF_z | 0, 0, 0, 36, 63]); 

t0 := Realtime();

P1_1, P2_1, FF_small_1, FF_big_1, E_small_1, E_big_1 := computeTorsionBasis(E_1, p);
P1_2, P2_2, FF_small_2, FF_big_2, E_small_2, E_big_2 := computeTorsionBasis(E_2, p);
P1_3, P2_3, FF_small_3, FF_big_3, E_small_3, E_big_3 := computeTorsionBasis(E_3, p);
computeWP(P1_1, P2_1, E_big_1, p, zeta);
computeWP(P1_2, P2_2, E_big_2, p, zeta);
computeWP(P1_3, P2_3, E_big_3, p, zeta);

print "Total ellapsed:", Realtime(t0), "seconds";