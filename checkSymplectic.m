function jTildePowModEll(j, p, ell)
    j_tilde := j / ell^Valuation(j, ell);
    pow := Integers()!((ell-1)/p);
    j_tildePower := j_tilde^pow;
    j_tildePower_d := Integers(ell)!Denominator(j_tildePower);
    j_tildePower_n := Integers(ell)!Numerator(j_tildePower);
    return j_tildePower_n/j_tildePower_d;
end function;

function findHSMCase(E, p, ell, zeta)
    j := jInvariant(E);
    j_tilde_pow := GF(ell)!jTildePowModEll(j, p, ell);

    return Log(zeta, j_tilde_pow);
end function;

function pTorsionBasis(E, p)
    FF := BaseRing(E);
    PolyFF<x> := PolynomialRing(FF);

    f := DivisionPolynomial(E, p);
    ff := PolyFF!f;
    F := Factorization(ff);

    smallDegFactors := [ff[1] : ff in F | Degree(ff[1]) eq Degree(F[1][1])];
    bigDegFactors := [ff[1] : ff in F | Degree(ff[1]) gt Degree(F[1][1])];
    ff_small := &*smallDegFactors;

    smallDegFactorsInFF := [f[1] : f in Factorization(ff_small)];

    if Degree(smallDegFactorsInFF[1]) eq 1 then
        FF_small := FF;
        a := Roots(smallDegFactorsInFF[1], FF)[1][1];
    else
        FF_small<a> := ext<FF | smallDegFactorsInFF[1]>;
    end if;

    PolyFF_small<yy> := PolynomialRing(FF_small);
    E_small := ChangeRing(E, FF_small);
    fESmall := Evaluate(DefiningPolynomial(E_small), [a, yy, 1]);
    quadExtComputed := 0;
    if IsIrreducible(fESmall) then
        FF_small<aY> := ext<FF_small | fESmall>;
        quadExtComputed := 1;
    else
        aY := Roots(fESmall, FF_small)[1][1];
    end if;

    E_small := ChangeRing(E_small, FF_small);
    P1 := E_small![a, aY, 1];

    E2, phi := IsogenyFromKernel(E_small, ff_small);
    phid := DualIsogeny(phi);
    K := Kernel(phid);
    pts := Points(K);
    P := 1;
    for pt in pts do
        if pt eq E2!0 then
            continue;
        else
            P := pt;
            break;
        end if;
    end for;
    f_x := IsogenyMapPhi(phi);
    x_coord_num := f_x - P[1]*IsogenyMapPsiSquared(phi);


    FF_big<b> := ext<FF_small | x_coord_num>;
    PolyFF_big<z> := PolynomialRing(FF_big);
    E_big := ChangeRing(E_small, FF_big);
    fEBig := Evaluate(DefiningPolynomial(E_big), [b, z, 1]);
    if quadExtComputed eq 0 and IsIrreducible(fEBig) then
        FF_big<bY> := ext<FF_big | fEBig>;
    else
        bY := Roots(fEBig, FF_big)[1][1];
    end if;

    E_big := ChangeRing(E_big, FF_big);
    P2 := E_big![b, bY, 1];

    return E_big!P1, P2, FF_big;
end function;

function findHGRCase(E, p, ell, zeta)
    // FF_z := Parent(zeta);
    // E_z := ChangeRing(E,FF_z);
    // not needed, F_z == F_ell
    FF := GF(ell);
    E := ChangeRing(E, FF);
    P1, P2, FF_big := pTorsionBasis(E, p);
    
    if p mod 4 eq 3 then
        ns := -1;
    else
        _:=exists(ns){ x : x in [1..p] | not IsSquare(GF(p)!x) };
        assert LegendreSymbol(ns,p) eq -1;
    end if;

    pairing := WeilPairing(P1, P2, p);
    k:=Index([zeta^k eq pairing : k in [1..p]], true);

    if not IsSquare(Zp!k) then
        P2 := P2 * ns;
    end if;


    GP2 := Parent(P2)![P2[1]^ell, P2[2]^ell];
    WPP2FrobP2 := WeilPairing(GP2, P2, p);
    k2 := Index([zeta^k eq WPP2FrobP2 : k in [1..p]], true);

    return k2;     
end function;

load "PairsLists/pairs_mod7_irred_symp_withEll.m";

p := 7;
isPairsSq := [];
for pair in pairs do
    print "+++";
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);
    ell := pair[3];

    PolyFF<z> := PolynomialRing(GF(ell));
    zeta:=Roots(z^p - 1)[2,1];
    assert zeta ne 1;

    if ReductionType(E1, ell) eq "Good" then
        h1 := findHGRCase(E1, p, ell, zeta);
    elif ReductionType(E1, ell) eq "Split multiplicative" or ReductionType(E1, ell) eq "Nonsplit multiplicative" then
        h1 := findHSMCase(E1, p, ell, zeta);
    else
        print "E1 is of reduction type", ReductionType(E1, ell), "which is not handled.";
    end if;

    if ReductionType(E2, ell) eq "Good" then
        h2 := findHGRCase(E2, p, ell, zeta);
    elif ReductionType(E2, ell) eq "Split multiplicative" or ReductionType(E2, ell) eq "Nonsplit multiplicative" then
        h2 := findHSMCase(E2, p, ell, zeta);
    else
        print "E2 is of reduction type", ReductionType(E2, ell), "which is not handled.";
    end if;

    h1 := GF(p)!h1;
    h2 := GF(p)!h2;
    print ReductionType(E1,ell), IsSquare(h1);
    print ReductionType(E2,ell), IsSquare(h2);
    isSq := IsSquare(-h1/h2);
    print "h/h' is square:", isSq;
    Append(~isPairsSq, isSq);

end for;

