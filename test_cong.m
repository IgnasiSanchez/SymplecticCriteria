// Translation of test_cong function from Sage to Magma
// Based on John Cremona's congruences repository
// https://github.com/JohnCremona/congruences

function HasSplitMultiplicativeReduction(E,p)
    return ReductionType(E,p) eq "Split Multiplicative";
end function;

function HasNonSplitMultiplicativeReduction(E,p)
    return ReductionType(E,p) eq "Nonsplit Multiplicative";
end function;

function test_cong(p, E1, E2 : mumax := 5000000, verbose := false, twist := true)
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
    
    actual_mu6 := mu6;
    if mu6 gt mumax then
        mu6 := mumax;
    end if;
    
    if verbose then
        printf "Curves %o and %o: testing ell up to %o mod %o\n", 
               CremonaReference(E1), CremonaReference(E2), mu6, p;
    end if;
    
    N1N2 := N1 * N2;
    
    // Test congruence for primes up to the bound
    for ell in PrimesUpTo(mu6) do
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
    
    if mu6 lt actual_mu6 then
        printf " ---- WARNING! for curves %o and %o, to test for isomorphic semisimplifications we should have tested ell mod %o up to %o, but we only tested up to %o\n", 
               CremonaReference(E1), CremonaReference(E2), p, actual_mu6, mu6;
        return false, "not tested up to required bound";
    end if;
    
    if verbose then
        printf "The two mod-%o representations have isomorphic semisimplifications\n", p;
    end if;
    
    return true, "up to semisimplification";
end function;

load "PairsLists/pairs_mod7_red.m";
p := 7;
retest := [];
remove := [];
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);
    ans, text := test_cong(p, E1, E2 : mumax := 10^7);
    if not ans then
        if Type(text) eq Type("") then
            Append(~retest, pair);
        else
            Append(~remove, pair);
        end if;
    end if;
end for;

