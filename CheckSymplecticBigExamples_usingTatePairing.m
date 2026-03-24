/* This function computes the Tate pairing obstruction for an elliptic curve E 
 * defined over a finite field FF containing the p-th roots of unity.
 *
 * Input:
 * - E: an elliptic curve over FF.
 * - p: a prime. 
 * - zeta: a fixed primitive p-th root of unity in FF.
 * - Verbose (optional): if true, it prints timing information.
 *
 * Output:
 * - k: The exponent such that the normalized Tate Pairing of P_W is zeta^k.
 */
function computeTateObstruction(E, p, zeta : Verbose := true)
    
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
    W, phi := IsogenyFromKernel(E_small, PolyFl!ff_small);
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
    P_W := 1;
    for pt in pts do
        if pt eq W!0 then
            continue;
        else
            P_W := pt;
            break;
        end if;
    end for;
    if Verbose then
        print "Time to find a point in kernel:", Realtime(t00), "seconds";
    end if;

    // --- The Reviewer's Optimization: Tate Pairing ---
    t00 := Realtime();
    
    // 1. Compute the raw Tate pairing of P_W with itself
    tate_root := ReducedTatePairing(P_W, P_W, p);
    
    if Verbose then
        print "Time to compute Tate Pairing and final exponentiation:", Realtime(t00), "seconds";
    end if;

    // 3. Extract the discrete log base zeta to find the exponent k
    t00 := Realtime();
    zeta_small := FF_small!zeta;
    
    // Linear search for the exponent (p is assumed to be small enough for this, e.g., 211)
    k := [i : i in [1..p] | zeta_small^i eq tate_root][1];
    
    if Verbose then
        print "Time to extract discrete log k:", Realtime(t00), "seconds";
        print "Found k =", k;
    end if;

    return k;
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


computeTateObstruction(E_1, p, zeta : Verbose := true);
computeTateObstruction(E_2, p, zeta : Verbose := true);
computeTateObstruction(E_3, p, zeta : Verbose := true);