PolyQ<x> := PolynomialRing(Rationals());
function QuarticTwist(E, d)
    K := BaseRing(E);
    Eshort := WeierstrassModel(E);
    ainvs := aInvariants(Eshort);
    A := ainvs[4];
    B := ainvs[5];

    assert B eq 0;
    Ed := EllipticCurve([K|0,0,0, A*d, 0]);
    assert jInvariant(E) eq jInvariant(Ed);  // both 1728

    return Ed;
end function;

function corollary25(E, p)
    b, D := HasComplexMultiplication(E);
    if not b then
        return [];
    end if;

    if Abs(D) notin [3,4] then
        if p lt 5 then
            return [];
        end if;
        return [QuadraticTwist(E, D)];
    end if;
    if Abs(D) eq 3 then
        if p mod 9 in [1,8] then
            return [QuadraticTwist(E, D)];
        end if;
        return [];
    end if;
    if Abs(D) eq 4 then
        if p lt 5 then
            return [];
        end if;
        return [QuarticTwist(E, D)];
    end if;

end function;

function theorem12(E)
    jInv := jInvariant(E);

    Eshort := WeierstrassModel(E);
    ainvs := aInvariants(Eshort);
    A := ainvs[4];
    B := ainvs[5];

    if jInv eq 1728 then
        assert B eq 0;

        return [
            [* 3, [EllipticCurve([0,0,0,-1/(3*A), 0])], [EllipticCurve([0,0,0,-4*A,0]), EllipticCurve([0,0,0,4/(3*A),0])]*], 
            [* 5, [EllipticCurve([0,0,0,5/A, 0])], [EllipticCurve([0,0,0,-4*A,0]), EllipticCurve([0,0,0,-20/A,0])]*]
        ];
    end if;

    if jInv eq 0 then
        assert A eq 0;

        return [
            [* 5, [EllipticCurve([0,0,0,0,4/(5*B)])], [EllipticCurve([0,0,0,0,-27*B]), EllipticCurve([0,0,0,0,-108/(5*B)])]*],
            [* 7, [EllipticCurve([0,0,0,0,-28/B])], [EllipticCurve([0,0,0,0,-27*B]), EllipticCurve([0,0,0,0,756/B])]*]
        ];
    end if;

    return [];

end function;


load "auxfiles/mod5_irred_j0Pairs.m";
p := 5;
i := 1;
remove := [];
for pair in E1E2j0 do
    print i, "/", #E1E2j0;
    E1 := EllipticCurve(pair[1]);

    crvs := [];
    crvs12 := theorem12(E1);
    idx := Index([p eq c[1] : c in crvs12], true);
    if idx gt 0 then
        crvs := crvs12[idx][2] cat crvs12[idx][3];
    end if;

    crvs25 := corollary25(E1, p);
    crvs cat:= crvs25;
    
    flag := 0;
    if not IsEmpty(crvs) then
        for E2 in crvs do
            if CremonaReference(E2) eq pair[2] then
                flag := 1;
                break;
            end if;
        end for;
    end if; 

    if flag eq 0 then
        Append(~remove, pair);
    end if;

    i +:= 1;
end for;

// load "auxfiles/mod7_irred_j0_upToTwist.m";
// p := 7;
// i := 1;
// for pair in pairs do
//     print i, "/", #pairs;
//     E1 := EllipticCurve(pair[1]);

//     crvs := theorem12(E1);
//     Index() ne 0;
//     if not IsEmpty(crvs) then
//         for E2 in crvs do
//             if CremonaReference(E2) eq pair[2] then
//                 print "Found pair via Corollary 2.5:", pair;
//                 break;
//             end if;
//         end for;
//     end if;
    
//     i +:= 1;
// end for;