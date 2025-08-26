load "PairsLists/pairs_mod11_irred_symp_withEll.m";
pairs2 := pairs;
load "PairsLists/pairs_mod11_irred_antisymp_withEll.m";
pairs cat:= pairs2;

function multRed(E,ell)
    return ReductionType(E,ell) eq "Nonsplit multiplicative" or ReductionType(E,ell) eq "Split multiplicative";
end function;

function splitRed(E,ell)
    return ReductionType(E,ell) eq "Split multiplicative";
end function;

function nonsplitRed(E,ell)
    return ReductionType(E,ell) eq "Nonsplit multiplicative";
end function;

function goodRed(E,ell)
    return ReductionType(E,ell) eq "Good";
end function;

function filterNonSplitPairs(pairs)
    return [pair : pair in pairs | not (nonsplitRed(EllipticCurve(pair[1]), pair[3]) or nonsplitRed(EllipticCurve(pair[2]), pair[3]))];
end function;

function pairInList(pair, list)
    for pp in list do
        if (pp[1] eq pair[1] and pp[2] eq pair[2]) or (pp[1] eq pair[2] and pp[2] eq pair[1]) then
            return true;
        end if;
    end for;
    return false;
end function;

split_pairs := filterNonSplitPairs(pairs);
split_pairs_norep := {[p[1],p[2]] : p in  split_pairs};
print "There are ", #split_pairs_norep, " pairs mod p who satisfy hypothesis of thm 1 or 2";

AAthm := AssociativeArray();
AAthm["thm1"] := [];
AAthm["thm2"] := [];
for pair in split_pairs do
    E1 := EllipticCurve(pair[1]);
    E2 := EllipticCurve(pair[2]);
    ell := pair[3];
    if multRed(E1, ell) and multRed(E2, ell) then
        Append(~AAthm["thm1"], pair);
    else
        Append(~AAthm["thm2"], pair);
    end if;
end for;

print "There are ", #{[p[1], p[2]] : p in AAthm["thm1"]}, " pairs mod p who satisfy the hypothesis of thm 1";
print "There are ", #{[p[1], p[2]] : p in AAthm["thm2"]}, " pairs mod p who satisfy the hypothesis of thm 2";

print "There are", {*pairInList(p, pairs2) : p in {[p[1], p[2]] : p in AAthm["thm2"]}*}, "pairs that are symplectic";

AA := AssociativeArray();
for pair in split_pairs do
    if (pair[1] cat "," cat pair[2]) in Keys(AA) then
        Append(~AA[pair[1] cat "," cat pair[2]], pair[3]);
    else
        AA[pair[1] cat "," cat pair[2]] := [pair[3]];
    end if;
end for;

ks := [k : k in Keys(AA)];
print "There are ",#[i : i in [1..#ks] | #AA[ks[i]] ge 2], "pairs satisfying the criteria at diff values of ell";