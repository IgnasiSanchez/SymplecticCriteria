function test_pairs(pairs, p);

    missed:=[];
    symplectics:=[];
    antisymplectics:=[];

    for i in [1..#pairs] do 
        tps:=[];
        pr:=pairs[i];
        print "i = ", i, ", pair = ", pr;
        E1:=MinimalModel(EllipticCurve(pr[1]));
        E2:=MinimalModel(EllipticCurve(pr[2]));

        s1:=multiplicativeTest(E1,E2,p);
        if s1 ne 0 then 
            Append(~tps,s1);
            print "success with multiplicative test";
        end if;

        s2:=H8test(E1,E2,p);
        if s2 ne 0 then 
            Append(~tps,s2);
            print "success with H8 test";
        end if;

        s3:=SL2test(E1,E2,p);
        if s3 ne 0 then 
            Append(~tps,s3);
            print "success with SL2 test";
        end if;

        s4:=Dic12test(E1,E2,p);
        if s4 ne 0 then 
            Append(~tps,s4);
            print "success with Dic12 test";
        end if;


        s5:=C3test(E1,E2,p);
        if s5 ne 0 then 
            Append(~tps,s5);
            print "success with C3 test";
        end if;

        s6:=C4test(E1,E2,p);
        if s6 ne 0 then 
            Append(~tps,s6);
            print "success with C4 test";
        end if;

        s7:=C3testWild(E1,E2,p);	
        if s7 ne 0 then 
            Append(~tps,s7);
            print "success with wild C3 test";
        end if;

        s8:=C4testWild(E1,E2,p);	
        if s8 ne 0 then 
            Append(~tps,s8);
            print "success with wild C4 test";
        end if;


        if #tps ne 0 then
                // check that all test which applied agree:
                assert #Set(tps) eq 1;
                sgn := Rep(Set(tps));
            if sgn eq 1 then Append(~symplectics,i);
                elif sgn eq -1 then Append(~antisymplectics,i);
                end if;
            print i, sgn;
            print "+++++++++++++++++++++";
        else
            print i, "no test applied";
            Append(~missed,i);
            print "+++++++++++++++++++++";
        end if;
    end for;


    // applies test of good reduction only to those who missed all the tests

    missed2:=[];
    Bound:=1000;

    print "After testing ", #pairs, " pairs, ";
    print #symplectics, " pairs were proved to be symplectic, ";
    print #antisymplectics, " pairs were proved to be antisymplectic, and";
    print #missed, " failed (no test applied)";
    print "Now applying the test of good reduction to these";

    for i in [1..#missed] do 
        tps:=[];
        pr:=pairs[i];
        print "i = ", i, ", pair = ", pr;
        E1:=MinimalModel(EllipticCurve(pr[1]));
        E2:=MinimalModel(EllipticCurve(pr[2]));

        s9:=QuickGoodRedTest(E1,E2,Bound,p);
        if s9 ne 0 then 
            Append(~tps,s9);
            print "success with quick good reduction test";
        end if;

        s10:=FullGoodRedTest(E1,E2,Bound,p);
        if s10 ne 0 then 
            Append(~tps,s10);
            print "success with full good reduction test";
        end if;

        if #tps ne 0 then
            assert #Set(tps) eq 1; 
                sgn := Rep(Set(tps));
            if sgn eq 1 then Append(~symplectics,i);
                elif sgn eq -1 then Append(~antisymplectics,i);
                end if;
            print i, Rep(tps);
            print "+++++++++++++++++++++";
        else
            print i, "no test applied";
            Append(~missed2,i);
            print "+++++++++++++++++++++";
        end if;
    end for;

    // print "After additional tests of ", #missed, " pairs";
    // print #symplectics, " pairs were proved to be symplectic, ";
    // print #antisymplectics, " pairs were proved to be antisymplectic, and";
    // print #missed2, " still failed (no test applied)";

    // return statement to avoid error message, useless otherwise
    return symplectics, antisymplectics, missed2;

end function;

function WriteListOfPairsToFile(list, filename)
    f := Open(filename, "w");

    str := "[\n";
    for i in [1..#list] do
        str := Sprintf("[%o, %o]", list[i][1], list[i][2]);
        if i lt #list then
            str cat:= ",";
        end if;
        str cat:= "\n";
    end for;

    str cat:= "\n]";

    Write(f, str);
    return 1;
end function;


load "PairsLists/pairs_mod5_irred.m";
symp, antisymp, missed := test_pairs(pairs, 5);
WriteListOfPairsToFile(pairs[symp], "PairsLists/pairs_mod5_irred_symp.m");
WriteListOfPairsToFile(pairs[antisymp], "PairsLists/pairs_mod5_irred_antisymp.m");
if not IsEmpty(pairs[missed]) then
    WriteListOfPairsToFile(pairs[missed], "PairsLists/pairs_mod5_irred_MISSED.m");
end if;

load "PairsLists/pairs_mod5_red.m";
symp, antisymp, missed2 := test_pairs(pairs, 5);
WriteListOfPairsToFile(pairs[symp], "PairsLists/pairs_mod5_red_symp.m");
WriteListOfPairsToFile(pairs[antisymp], "PairsLists/pairs_mod5_red_antisymp.m");
if not IsEmpty(pairs[missed2]) then
    WriteListOfPairsToFile(pairs[missed2], "PairsLists/pairs_mod5_red_MISSED.m");
end if;

load "PairsLists/pairs_mod11_irred.m";
symp, antisymp, missed3 := test_pairs(pairs, 11);
WriteListOfPairsToFile(pairs[symp], "PairsLists/pairs_mod11_irred_symp.m");
WriteListOfPairsToFile(pairs[antisymp], "PairsLists/pairs_mod11_irred_antisymp.m");
if not IsEmpty(pairs[missed3]) then
    WriteListOfPairsToFile(pairs[missed3], "PairsLists/pairs_mod11_irred_MISSED.m");
end if;

load "PairsLists/pairs_mod13_irred.m";
symp, antisymp, missed4 := test_pairs(pairs, 13);
WriteListOfPairsToFile(pairs[symp], "PairsLists/pairs_mod13_irred_symp.m");
WriteListOfPairsToFile(pairs[antisymp], "PairsLists/pairs_mod13_irred_antisymp.m");
if not IsEmpty(pairs[missed4]) then
    WriteListOfPairsToFile(pairs[missed4], "PairsLists/pairs_mod13_irred_MISSED.m");
end if;

load "PairsLists/pairs_mod17_irred.m";
symp, antisymp, missed5 := test_pairs(pairs, 17);
WriteListOfPairsToFile(pairs[symp], "PairsLists/pairs_mod17_irred_symp.m");
WriteListOfPairsToFile(pairs[antisymp], "PairsLists/pairs_mod17_irred_antisymp.m");
if not IsEmpty(pairs[missed5]) then
    WriteListOfPairsToFile(pairs[missed5], "PairsLists/pairs_mod17_irred_MISSED.m");
end if;
