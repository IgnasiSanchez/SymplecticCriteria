function DiscList(x)
    if ((x mod 4) in [2,3]) or (x ge 0) then
        return [];
    end if;
    D, h := Squarefree(x);
    if (D mod 4) in [2,3] then
        D := D * 4;
        h := h div 2;
    end if;
    L := [];
    for d in Divisors(h) do
        Append(~L, D*d^2);
    end for;
    return L;
end function;

function EndomorphismRingDiscriminant(E)
    a := TraceOfFrobenius(E);
    k := BaseField(E);
    q := #k;
    p := Characteristic(k);
    r := Valuation(q, p);
    Delta := a^2 - 4*q;
    if Delta eq 0 then
        return 0, -1, a, false;
    end if;
    if (a mod p) eq 0 then
        if ((p mod 4) eq 3) and (a eq 0) and ((r mod 2) eq 1) then
            if #Generators(SylowSubgroup(TorsionSubgroup(E), 2)) eq 2 then
            return (-1)*p, 2*p^((r-1) div 2), a, false;
            else
            return (-4)*p, p^((r-1) div 2), a, false;
            end if;
        else
            D, h := Squarefree(Delta);
            if (D mod 4) in [2,3] then
            D := D * 4;
            h := h div 2;
            end if;
            return D, h, a, false;
        end if;
    else
        j_E := jInvariant(E);
        Discs := DiscList(Delta);
        for D in Discs do
            if Evaluate(ChangeRing(HilbertClassPolynomial(D), k), j_E) eq 0 then
            return D, Floor(SquareRoot(Delta div D)), a, true;
            end if;
        end for;
    end if;
end function;

function IntegralFrobenius(E)
    D, b, a, flag := EndomorphismRingDiscriminant(E);
    if D eq 0 then
        return Matrix([[a div 2, 0], [0, a div 2]]);
    end if;

    Delta := D*b^2;
    return Matrix([[(a - b*D) div 2, (b*D*(1-D)) div 4], [b, (a + b*D) div 2]]);
end function;

function jTildePowModEll(j, p, ell)
    j_tilde := j / ell^Valuation(j, ell);
    pow := Integers()!((ell-1)/p);
    j_tildePower := j_tilde^pow;
    j_tildePower_d := Integers(ell)!Denominator(j_tildePower);
    j_tildePower_n := Integers(ell)!Numerator(j_tildePower);
    return j_tildePower_n/j_tildePower_d;
end function;

function checkTheorem1Hypothesis(j_1, j_2, p, ell)
	if Integers(p)!ell ne 1 then
		return false;
	end if;

	if Valuation(j_1, ell) mod p eq 0 and Valuation(j_2, ell) mod p eq 0 then
		j1_tilde_pow := jTildePowModEll(j_1, p, ell);
		j2_tilde_pow := jTildePowModEll(j_2, p, ell);
		if (j1_tilde_pow ne 1) and (j2_tilde_pow ne 1) then
			return true;
		end if;
	end if;

	return false;
end function;

// j_1 is always split multiplicative at l, j_2 is always good red at l
function checkTheorem2Hypothesis(j_1, E2, p, ell)
	GLp := GL(2, GF(p));
	if Integers(p)!ell ne 1 then
		return false;
	end if;

	j1_tilde_pow := jTildePowModEll(j_1, p, ell);
	if Valuation(j_1, ell) mod p eq 0 and (j1_tilde_pow ne 1) then
		E2_modell := ChangeRing(E2, GF(ell));
        frobell := IntegralFrobenius(E2_modell);
        if Order(GLp!frobell) eq p then
			return true;
		end if;
	end if;

	return false;
end function;

function findSuitableEll(E1, E2, p)
    j_1 := jInvariant(E1);
    j_2 := jInvariant(E2);

    badRedE1 := [q[1] : q in Factorization(Conductor(E1))];
    badRedE2 := [q[1] : q in Factorization(Conductor(E2))];

	// we only want ell = 1 mod p
    badRedE1_1modp := [q : q in badRedE1 | q mod p eq 1];
    badRedE2_1modp := [q : q in badRedE2 | q mod p eq 1];

    if IsEmpty(badRedE1_1modp) and IsEmpty(badRedE2_1modp) then
        return [];
    end if;

    multRedE1 := [q : q in badRedE1_1modp | ReductionType(E1, q) eq "Split multiplicative" or ReductionType(E1, q) eq "Nonsplit multiplicative"];//"Split multiplicative"];
    multRedE2 := [q : q in badRedE2_1modp | ReductionType(E2, q) eq "Split multiplicative" or ReductionType(E2, q) eq "Nonsplit multiplicative"];//"Split multiplicative"];

    commonPrimesOfSplitMultRed := SetToSequence(Set(multRedE1) meet Set(multRedE2));
    E1multE2good := SetToSequence(Set(multRedE1) diff Set(badRedE2));
    E1goodE2mult := SetToSequence(Set(multRedE2) diff Set(badRedE1));

    finalPrimes := [];

    if not IsEmpty(commonPrimesOfSplitMultRed) then
        for ell in commonPrimesOfSplitMultRed do
			if checkTheorem1Hypothesis(j_1, j_2, p, ell) then
				Append(~finalPrimes, ell);
			end if;
		end for;
	end if;

    if not IsEmpty(E1multE2good) then
        for ell in E1multE2good do
            if Integers(p)!ell ne 1 then
                continue;
            end if;
            j1_tilde_pow := jTildePowModEll(j_1, p, ell);
            if checkTheorem2Hypothesis(j_1, E2, p, ell) then
				Append(~finalPrimes, ell);
			end if;
        end for;
    end if;

    if not IsEmpty(E1goodE2mult) then
        for ell in E1goodE2mult do
            if Integers(p)!ell ne 1 then
                continue;
            end if;
            j2_tilde_pow := jTildePowModEll(j_2, p, ell);
            if checkTheorem2Hypothesis(j_2, E1, p, ell) then
				Append(~finalPrimes, ell);
			end if;
        end for;
    end if;

    return finalPrimes;

end function;

out := "pairs := [*\n";
load "mod5_irred_symppairs.m";
p := 5;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"SP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod5_irred_antipairs.m";
p := 5;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"AP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod7_antipairs.m";
p := 7;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"AP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod7_red_anti_pairs.m";
p := 7;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"RAP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod7_red_symp_pairs.m";
p := 7;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"RSP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod7_symppairs.m";
p := 7;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o, \"SP\"*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod11pairs_uptotwist.m";
p := 11;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod13pairs_uptotwist.m";
p := 13;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;

load "mod17pairs.m";
p := 17;
for pair in pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);

    l := findSuitableEll(E1, E2, p);
    if not IsEmpty(l) then 
        for ell in l do
            out cat:= Sprintf("   [*%o, \"%o\", \"%o\", %o*],\n", p, CremonaReference(E1), CremonaReference(E2), ell);
        end for;
    end if;
end for;


out cat:= "*];";

print out;

