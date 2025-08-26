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

    return -Log(zeta, j_tilde_pow);
end function;

function pTorsionBasis(E, p, ell)
    FF := GF(ell);
    PolyFF<x> := PolynomialRing(FF);
    E1 := ChangeRing(E, FF);

    f := DivisionPolynomial(E, p);
    ff := PolyFF!f;
    F := Factorization(ff);

    smallDegFactors := [ff[1] : ff in F | Degree(ff[1]) eq Degree(F[1][1])];
    bigDegFactors := [ff[1] : ff in F | Degree(ff[1]) gt Degree(F[1][1])];

    FF_small<a> := ext<FF | smallDegFactors[1]>;
    if Evaluate(ff, a) ne 0 then // this should only happen when the ext has deg 1
        a := Roots(ff, FF)[1][1];
    end if;
    PolyFF_small<y> := PolynomialRing(FF_small);
    E1_small := ChangeRing(E1, FF_small);
    fESmall := Evaluate(DefiningPolynomial(E1_small), [a, y, 1]);
    if IsIrreducible(fESmall) then
        FF_small<aY> := ext<FF_small | fESmall>;
    else
        aY := Roots(fESmall, FF_small)[1][1];
    end if;

    P1 := ChangeRing(E1_small, FF_small)![a, aY, 1];

    FF_big<b> := ext<FF_small | bigDegFactors[1]>;
    PolyFF_big<z> := PolynomialRing(FF_big);
    E1_big := ChangeRing(E1, FF_big);
    fEBig := Evaluate(DefiningPolynomial(E1_big), [b, z, 1]);
    if IsIrreducible(fEBig) then
        FF_big<bY> := ext<FF_big | fEBig>;
    else
        bY := Roots(fEBig, FF_big)[1][1];
    end if;

    P2 := ChangeRing(E1_big, FF_big)![b, bY, 1];

    return ChangeRing(E1_big, FF_big)![a, aY, 1], P2, FF_big;
end function;

function findHGRCase(E, p, ell, zeta)
    P1, P2, FF_big := pTorsionBasis(E, p, ell);
    FF := GF(ell);

    // check if basis is symplectic: 
    _:=exists(ns){ x : x in [1..p] | not IsSquare(GF(p)!x) };
    assert LegendreSymbol(ns,p) eq -1;

    pairing := WeilPairing(P1, P2, p);
    k:=Index([zeta^k eq pairing : k in [1..p]], true);
    if IsSquare(GF(p)!k) then
        P2:=P2;
    else
        P2:=ns*P2;
    end if;

    // Find Frobenius matrix
    Gal, _, toAut := AutomorphismGroup(FF_big, FF);
    Frob_ell := toAut(Gal.1);
    GP2 := Parent(P1)![Frob_ell(P2[1]), Frob_ell(P2[2]), 1];

    // hp := WeilPairing(P2, GP2, p);
    // kp:=Index([zeta^k eq hp : k in [1..p]], true);

    for h in [1..p] do 
        if h*P1 + P2 eq GP2 then
//            assert IsSquare(GF(p)!(kp*h));
            return h;
        end if;
    end for;
    
    error "We didn't find h";
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
    isSq := IsSquare(h1/h2);
    print "h/h' is square:", isSq;
    Append(~isPairsSq, isSq);

end for;

