function ReduceListUpToQuadraticTwistAndIsogeny(pairs)
    AA := AssociativeArray();
    for pair in pairs do
        E1 := EllipticCurve(pair[1]);
        E2 := EllipticCurve(pair[2]);
        j1 := jInvariant(E1);
        j2 := jInvariant(E2);

        if j1 in [0, 1728] and j2 in [0, 1728] then
            // We don't handle these cases
            continue;
        end if;


        if [j1,j2] in Keys(AA) then
            Append(~AA[[j1,j2]], pair);
            continue;
        end if;
        if [j2,j1] in Keys(AA) then
            Append(~AA[[j2,j1]], [pair[2], pair[1]]);
            continue;
        end if;
        if j1 eq 0 or j1 eq 1728 then
            AA[[j2,j1]] := [[pair[2], pair[1]]];
        else
            AA[[j1,j2]] := [pair];
        end if;
    end for;

    AAUpToTwist := AssociativeArray();
    for k in Keys(AA) do
        initial_list := AA[k];
        i := 1;

        repeat
            pair := initial_list[i];
            to_remove := [];
            for j in [(i+1)..#initial_list] do
                try
                    _,d := IsQuadraticTwist(EllipticCurve(pair[1]), EllipticCurve(initial_list[j][1]));
                    if IsIsomorphic(EllipticCurve(pair[2]), QuadraticTwist(EllipticCurve(initial_list[j][2]), d)) then
                        Append(~to_remove, initial_list[j]);
                    end if;
                catch e
                    print e;
                    print pair, initial_list[j];
                    break;
                end try;
            end for;
            for j in to_remove do
                Exclude(~initial_list, j);
            end for;
            i +:= 1;
            
        until i gt #initial_list;
        assert not IsEmpty(initial_list);
        AAUpToTwist[k] := initial_list;
    end for;

    // Desaturate list
    pairsUpToTwist := Flat([AAUpToTwist[k] : k in Keys(AAUpToTwist)] : Depth:=1);

    function isogenyLabel(label)
        _,match,_ := Regexp("^[0-9]+[a-z]+", label); 
        return match;
    end function;

    AAIsog := AssociativeArray();
    pairsIsogenyClasses := {[isogenyLabel(pair[1]), isogenyLabel(pair[2])] : pair in pairsUpToTwist};
    for pair in pairsIsogenyClasses do
        AAIsog[pair] := [];
    end for;

    for pair in pairsUpToTwist do
        Append(~AAIsog[[isogenyLabel(pair[1]), isogenyLabel(pair[2])]], pair);
    end for;

    pairsIsogenyClasses := [AAIsog[k][1] : k in Keys(AAIsog)];

    return pairsUpToTwist, pairsIsogenyClasses;
end function;


function WriteListOfPairsToFile(pairs, filename)
    out := "pairs := [*\n";
    for pair in pairs do
        out cat:= Sprintf("[*\"%o\", \"%o\"*],\n", pair[1], pair[2]);
    end for;
    out := out[1..(#out-2)]; // remove last comma and \n
    out cat:= "\n*];\n";
    f := Open(filename, "w");
    Write(f, out);
    return 1;
end function;


load "PairsLists/pairs_mod17_irred.m";
pairsUpToTwist, pairsIsogenyClasses := ReduceListUpToQuadraticTwistAndIsogeny(pairs);
WriteListOfPairsToFile(pairsUpToTwist, "IntermediateFiles/mod17_irred_UpToTwist.m");
WriteListOfPairsToFile(pairsIsogenyClasses, "IntermediateFiles/mod17_irred_UpToIsogeny.m");

load "PairsLists/pairs_mod13_irred.m";
pairsUpToTwist, pairsIsogenyClasses := ReduceListUpToQuadraticTwistAndIsogeny(pairs);
WriteListOfPairsToFile(pairsUpToTwist, "IntermediateFiles/mod13_irred_UpToTwist.m");
WriteListOfPairsToFile(pairsIsogenyClasses, "IntermediateFiles/mod13_irred_UpToIsogeny.m");

load "PairsLists/pairs_mod11_irred.m";
pairsUpToTwist, pairsIsogenyClasses := ReduceListUpToQuadraticTwistAndIsogeny(pairs);
WriteListOfPairsToFile(pairsUpToTwist, "IntermediateFiles/mod11_irred_UpToTwist.m");
WriteListOfPairsToFile(pairsIsogenyClasses, "IntermediateFiles/mod11_irred_UpToIsogeny.m");

load "PairsLists/pairs_mod7_irred.m";
pairsUpToTwist, pairsIsogenyClasses := ReduceListUpToQuadraticTwistAndIsogeny(pairs);
WriteListOfPairsToFile(pairsUpToTwist, "IntermediateFiles/mod7_irred_UpToTwist.m");
WriteListOfPairsToFile(pairsIsogenyClasses, "IntermediateFiles/mod7_irred_UpToIsogeny.m");

load "PairsLists/pairs_mod5_irred.m";
pairsUpToTwist, pairsIsogenyClasses := ReduceListUpToQuadraticTwistAndIsogeny(pairs);
WriteListOfPairsToFile(pairsUpToTwist, "IntermediateFiles/mod5_irred_UpToTwist.m");
WriteListOfPairsToFile(pairsIsogenyClasses, "IntermediateFiles/mod5_irred_UpToIsogeny.m");


