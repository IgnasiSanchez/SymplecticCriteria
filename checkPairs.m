load "IntFrobFunctions.m";

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

function WriteListOfPairsToFile(pairs, p, filename)
    out := "pairs := [*\n";
    i := 1;
    for pair in pairs do
        E1 := EllipticCurve(pair[1]);
        E2 := EllipticCurve(pair[2]);
        ells := findSuitableEll(E1, E2, p);
        if not IsEmpty(ells) then
            for ell in ells do
                out cat:= Sprintf("[*\"%o\", \"%o\", %o *]", pair[1], pair[2], ell);
            end for;
        end if;
        if i lt #pairs then
            out cat:= ",";
        end if;
        out cat:= "\n";
        i +:= 1;
    end for;
    out cat:= "*];";
    f := Open(filename, "w");
    Write(f, out);
    return 1;
end function;

// Mod 5
load "PairsLists/pairs_mod5_irred_symp.m";
WriteListOfPairsToFile(pairs, 5, "PairsLists/pairs_mod5_irred_symp_withEll.m");

load "PairsLists/pairs_mod5_irred_antisymp.m";
WriteListOfPairsToFile(pairs, 5, "PairsLists/pairs_mod5_irred_antisymp_withEll.m");

load "PairsLists/pairs_mod5_red_symp.m";
WriteListOfPairsToFile(pairs, 5, "PairsLists/pairs_mod5_red_symp_withEll.m");

load "PairsLists/pairs_mod5_red_antisymp.m";
WriteListOfPairsToFile(pairs, 5, "PairsLists/pairs_mod5_red_antisymp_withEll.m");


// Mod 7
load "PairsLists/pairs_mod7_irred_symp.m";
WriteListOfPairsToFile(pairs, 7, "PairsLists/pairs_mod7_irred_symp_withEll.m");

load "PairsLists/pairs_mod7_irred_antisymp.m";
WriteListOfPairsToFile(pairs, 7, "PairsLists/pairs_mod7_irred_antisymp_withEll.m");

load "PairsLists/pairs_mod7_red_symp.m";
WriteListOfPairsToFile(pairs, 7, "PairsLists/pairs_mod7_red_symp_withEll.m");

load "PairsLists/pairs_mod7_red_antisymp.m";
WriteListOfPairsToFile(pairs, 7, "PairsLists/pairs_mod7_red_antisymp_withEll.m");


// Mod 11
load "PairsLists/pairs_mod11_irred_symp.m";
WriteListOfPairsToFile(pairs, 11, "PairsLists/pairs_mod11_irred_symp_withEll.m");

load "PairsLists/pairs_mod11_irred_antisymp.m";
WriteListOfPairsToFile(pairs, 11, "PairsLists/pairs_mod11_irred_antisymp_withEll.m");


// Mod 13
load "PairsLists/pairs_mod13_irred_symp.m";
WriteListOfPairsToFile(pairs, 13, "PairsLists/pairs_mod13_irred_symp_withEll.m");

load "PairsLists/pairs_mod13_irred_antisymp.m";
WriteListOfPairsToFile(pairs, 13, "PairsLists/pairs_mod13_irred_antisymp_withEll.m");


// Mod 17
load "PairsLists/pairs_mod17_irred_symp.m";
WriteListOfPairsToFile(pairs, 17, "PairsLists/pairs_mod17_irred_symp_withEll.m");

load "PairsLists/pairs_mod17_irred_antisymp.m";
WriteListOfPairsToFile(pairs, 17, "PairsLists/pairs_mod17_irred_antisymp_withEll.m");

