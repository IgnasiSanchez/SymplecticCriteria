// Translation of test_cong function from Sage to Magma
// Based on John Cremona's congruences repository
// https://github.com/JohnCremona/congruences

function HasSplitMultiplicativeReduction(E,p)
    return ReductionType(E,p) eq "Split Multiplicative";
end function;

function HasNonSplitMultiplicativeReduction(E,p)
    return ReductionType(E,p) eq "Nonsplit Multiplicative";
end function;

function test_cong(p, E1, E2 : mumax := 5000000, Pr := [], verbose := false, twist := true)
    /*
    Given elliptic curves E1 and E2 and a prime p, use Kraus's Prop. 4
    to determine whether or not E1[p] and E2[p] have isomorphic
    semisimplifications (ignoring whether a symplectic isomorphism exists).
    
    Parameters:
    - p: prime number
    - E1, E2: elliptic curves
    - mumax: only test a_l for l up to this even if the bound is greater
    - verbose: print additional information
    - twist: whether to apply minimal quadratic twist
    
    Returns:
    - boolean: true if representations have isomorphic semisimplifications
    - string: additional information about the result
    */
    
    N1 := Conductor(E1);
    N2 := Conductor(E2);
    
    if twist then
        E1orig := E1;
        E2orig := E2;
        N1orig := N1;
        N2orig := N2;
        
        E1, d := MinimalQuadraticTwist(E1);
        
        if d ne 1 then
            E2 := QuadraticTwist(E2, d);
            if verbose then
                printf "Twisting by %o before testing congruence\n", d;
                printf "Before twisting, conductors were %o and %o\n", N1, N2;
            end if;
            N1 := Conductor(E1);
            N2 := Conductor(E2);
            if verbose then
                printf "After twisting, conductors are %o and %o\n", N1, N2;
            end if;
            if N2 gt 400000 then // we have made E2 worse, so untwist
                if verbose then
                    print "After twisting, E2 is not in the database, so we undo the twisting";
                end if;
                E1 := E1orig;
                E2 := E2orig;
                N1 := N1orig;
                N2 := N2orig;
            end if;
        end if;
    end if;
    
    // Compute the set S of bad primes
    gcd_N := GCD(N1, N2);
    S := PrimeDivisors(gcd_N);
    S1 := [ell : ell in S | 
           HasSplitMultiplicativeReduction(E1, ell) and 
           HasNonSplitMultiplicativeReduction(E2, ell)];
    S2 := [ell : ell in S | 
           HasSplitMultiplicativeReduction(E2, ell) and 
           HasNonSplitMultiplicativeReduction(E1, ell)];
    S := S1 cat S2;
    
    // Compute the bound
    if IsEmpty(S) then
        S := [1];
    end if;
    M := LCM(N1, N2) * &*S;

    mu := M * &*[(ell + 1) / ell : ell in PrimeDivisors(M)];
    
    mu6 := Integers()!Floor(mu / 6);
    
    if verbose and mu6 gt mumax then
        printf "Curves %o and %o: testing ell up to %o mod %o\n", 
               CremonaReference(E1), CremonaReference(E2), mu6, p;
    end if;
    
    if mu6 gt mumax then
        printf " ---- WARNING! for curves %o and %o, to test for isomorphic semisimplifications we should have tested ell mod %o up to %o. The bound is smaller so we skip this pair.\n", 
               CremonaReference(E1), CremonaReference(E2), p, mu6;
        return false, "not tested up to required bound";
    end if;
    
    if verbose then
        printf "Curves %o and %o: testing ell up to %o mod %o\n", 
               CremonaReference(E1), CremonaReference(E2), mu6, p;
    end if;
    
    N1N2 := N1 * N2;

    if IsEmpty(Pr) then
        Pr := PrimesUpTo(mu6);
    else
        Pr := [p : p in Pr | p le mu6];
    end if;
    
    // Test congruence for primes up to the bound
    for ell in Pr do
        if ell eq p then
            continue;
        end if;
        
        a1 := TraceOfFrobenius(E1, ell);
        a2 := TraceOfFrobenius(E2, ell);
        
        if N1N2 mod ell eq 0 then
            if Valuation(N1N2, ell) eq 1 and (a1*a2 - (ell + 1)) mod p ne 0 then
                return false, <ell, a1, a2>;
            end if;
        else
            if (a1 - a2) mod p ne 0 then
                return false, <ell, a1, a2>;
            end if;
        end if;
    end for;
    
    if verbose then
        printf "The two mod-%o representations have isomorphic semisimplifications\n", p;
    end if;
    
    return true, "up to semisimplification";
end function;

PolyQ<x> := PolynomialRing(Rationals());
FFQ<t> := FieldOfFractions(PolyQ);

function Homogenize(P)
    PolyQ2<x,y> := PolynomialRing(Rationals(), 2);
    coeffs := Coefficients(P);
    deg := Degree(P);
    return &+[coeffs[i+1]*y^(deg-i)*x^i : i in [0..deg]];
end function;

function test_cong_mod5_symp(E1, E2)
    jInv1 := jInvariant(E1);
    jInv2 := jInvariant(E2);
    E1 := WeierstrassModel(E1);
    aInv := aInvariants(E1);
    a := aInv[4];
    b := aInv[5];
    alpha,beta := RubinSilverbergPolynomials(5, jInv1/1728);

    // We found some examples where the only root of j(t)-j2 is at infinity
    // so we need to homogenize to find this root.
    alpha := a*Homogenize(alpha);
    beta := b*Homogenize(beta);
    alpha_x := FFQ!Evaluate(alpha, [x,1]);
    beta_x := FFQ!Evaluate(beta, [x,1]);
    alpha_y := FFQ!Evaluate(alpha, [1,x]);
    beta_y := FFQ!Evaluate(beta, [1,x]);
    E_x := EllipticCurve([alpha_x, beta_x]);
    E_y := EllipticCurve([alpha_y, beta_y]);
    jInv_x := jInvariant(E_x);
    jInv_y := jInvariant(E_y);

    rt_x := Roots(Numerator(jInv_x - jInv2));
    rt_y := Roots(Numerator(jInv_y - jInv2));

    if IsEmpty(rt_x) and IsEmpty(rt_y) then
        return false; 
    else
        ref_2 := CremonaReference(E2);
        for rr in rt_x do
            tt := rr[1];
            alpha_t := Evaluate(alpha, [tt,1]);
            beta_t := Evaluate(beta, [tt,1]);
            E_tt := EllipticCurve([alpha_t, beta_t]);
            try
                ref_t := CremonaReference(E_tt);
                if ref_t eq ref_2 then
                    return true;
                end if;
            catch e
                continue;
            end try;
        end for;
        for rr in rt_y do
            tt := rr[1];
            alpha_t := Evaluate(alpha, [1,tt]);
            beta_t := Evaluate(beta, [1,tt]);
            E_tt := EllipticCurve([alpha_t, beta_t]);
            try
                ref_t := CremonaReference(E_tt);
                if ref_t eq ref_2 then
                    return true;
                end if;
            catch e
                continue;
            end try;
        end for;
    end if;

    return false;
end function;

function test_cong_mod5_antisymp(E1, E2)
    jInv1 := jInvariant(E1);
    jInv2 := jInvariant(E2);
    DD,cc4,cc6 := HessePolynomials(5, 2, cInvariants(E1));
    cc4_x := FFQ!(-12*Evaluate(cc4,[x,1]));
    cc6_x := FFQ!(-16*Evaluate(cc6, [x,1]));
    cc4_y := FFQ!(-12*Evaluate(cc4,[1,x]));
    cc6_y := FFQ!(-16*Evaluate(cc6, [1,x]));
    E_x := EllipticCurve([cc4_x, cc6_x]);
    E_y := EllipticCurve([cc4_y, cc6_y]);
    jInv_x := jInvariant(E_x);
    jInv_y := jInvariant(E_y);
    rt_x := Roots(Numerator(jInv_x - jInv2));
    rt_y := Roots(Numerator(jInv_y - jInv2));
    if IsEmpty(rt_x) and IsEmpty(rt_y) then
        return false; 
    else
        ref_2 := CremonaReference(E2);
        for rr in rt_x do
            tt := rr[1];
            cc4_tt := Evaluate(cc4_x, tt);
            cc6_tt := Evaluate(cc6_x, tt);
            E_tt := EllipticCurve([cc4_tt, cc6_tt]);
            try
                ref_t := CremonaReference(E_tt);
                if ref_t eq ref_2 then
                    return true;
                end if;
            catch e
                continue;
            end try;
        end for;
        for rr in rt_y do
            tt := rr[1];
            cc4_tt := Evaluate(cc4_y, tt);
            cc6_tt := Evaluate(cc6_y, tt);
            E_tt := EllipticCurve([cc4_tt, cc6_tt]);
            try
                ref_t := CremonaReference(E_tt);
                if ref_t eq ref_2 then
                    return true;
                end if;
            catch e
                continue;
            end try;
        end for;
    end if;

    return false;
end function;

load "IntermediateFiles/mod5_irred_UpToIsogeny.m";
p := 5;
retest := [];
remove := [];
mumax := 10^7;
Pr := PrimesUpTo(mumax);
t00 := Realtime();
i := 1;
for pair in pairsIsogenyClass do
    print i, "/", #pairsIsogenyClass;
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);
    ans, text := test_cong(p, E1, E2 : mumax := mumax, Pr := Pr);
    if not ans then
        if Type(text) eq Type("") then
            Append(~retest, pair);
        else
            Append(~remove, pair);
        end if;
    end if;
    i +:= 1;
end for;
print "Took", Realtime(t00), "seconds";

t00 := Realtime();
i := 1;
for pair in pairs do
    print i, "/", #pairs;
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);
    symp := test_cong_mod5_symp(E1, E2);
    if not symp then
        antisymp := test_cong_mod5_antisymp(E1, E2);
        if not antisymp then
            print "--- deleting pair", pair;
            Append(~remove, pair);
        end if;
    end if;
    i +:= 1;
end for;
print "Took", Realtime(t00), "seconds";

// retest2 := [];
// mumax := 5*10^7;
// Pr := PrimesUpTo(mumax);
// i := 1;
// for pair in retest do
//     print i, "/", #retest;
//     E1 := EllipticCurve(pair[1]);
//     E2 := EllipticCurve(pair[2]);
//     ans, text := test_cong(p, E1, E2 : mumax := mumax, Pr := Pr);
//     if not ans then
//         if Type(text) eq Type("") then
//             Append(~retest2, pair);
//         else
//             Append(~remove, pair);
//         end if;
//     end if;
//     i +:= 1;
// end for;

// retest3 := [];
// mumax := 3*10^8;
// Pr := PrimesUpTo(mumax);
// i := 1;
// for pair in retest2 do
//     print i, "/", #retest2;
//     E1 := EllipticCurve(pair[1]);
//     E2 := EllipticCurve(pair[2]);
//     ans, text := test_cong(p, E1, E2 : mumax := mumax, Pr := Pr);
//     if not ans then
//         if Type(text) eq Type("") then
//             Append(~retest3, pair);
//         else
//             Append(~remove, pair);
//         end if;
//     end if;
//     i +:= 1;
// end for;
