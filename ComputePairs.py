#%autoindent off

from sage.all import ZZ, QQ, EllipticCurve, prime_range, prod, Set, cremona_optimal_curves, srange, next_prime, CremonaDatabase, polygen, legendre_symbol, PolynomialRing, NumberField, SteinWatkinsAllData
from sage.schemes.elliptic_curves.isogeny_small_degree import Fricke_polynomial

from tqdm import tqdm
import numpy as np

CDB = CremonaDatabase()
x = polygen(QQ)

###
### The following functions are taken from John Cremona's https://github.com/JohnCremona/congruences
### 

def SW_label(E):
    return ".".join([str(E.conductor()), str(E.ainvs())])


def Elabel(E):
    try:
        return E.label()
    except:
        return SW_label(E)


# Given elliptic curves E1 and E2 and a prime p, use Kraus's Prop. 4
# to determine whether or not E1[p] and E2[p] have isomorphic
# semisimplifications (ignoring whether a symplectic isomorphism
# exists).
def test_cong(p, E1, E2, mumax=5000000, semisimp=True, verbose=False, twist=True):
    """mumax: only test a_l for l up to this even if the bound is
    greater, but then output a warning semisimp: if True, output True
    when the two reps have isomorphic semisimplifications, don't try
    to prove that the representations themselves are isomorphic
    (which is not fully implemented anyway in the reducible case).
    Note that proving that the semisimplfications are isomorphic only
    depends on the isogeny class, but the condition that the
    representations themselves are isomorphic depends in general on
    the specific curves in their classes.

    """
    N1 = E1.conductor()
    N2 = E2.conductor()
    if twist:
        E1orig = E1
        E2orig = E2
        N1orig = N1
        N2orig = N2
        E1, d = E1.minimal_quadratic_twist()
        if d!=1:
            E2 = E2.quadratic_twist(d)
            if verbose:
                print("Twisting by {} before testing congruence".format(d))
                print("Before twisting, conductors were {} and {}".format(N1,N2))
            N1 = E1.conductor()
            N2 = E2.conductor()
            if verbose:
                print("After  twisting, conductors are {} and {}".format(N1,N2))
            if N2>400000: # we have made E2 worse, so untwist
                if verbose:
                    print("After twisting, E2 is not in the database, so we undo the twisting")
                E1 = E1orig
                E2 = E2orig
                N1 = N1orig
                N2 = N2orig
    S = N1.gcd(N2).support()
    S1 = [ell for ell in S if E1.has_split_multiplicative_reduction(ell) and  E2.has_nonsplit_multiplicative_reduction(ell)]
    S2 = [ell for ell in S if E2.has_split_multiplicative_reduction(ell) and  E1.has_nonsplit_multiplicative_reduction(ell)]
    S = S1+S2
    M = N1.lcm(N2) * prod(S,1)
    mu = M * prod([(ell+1)/ell for ell in M.support()])
    mu6 = ZZ(int(mu/6)) # rounds down
    if verbose and mu6>mumax:
        print("Curves {} and {}: testing ell up to {} mod {}".format(Elabel(E1),Elabel(E2),mu6,p))
    actual_mu6 = mu6
    if mu6>mumax:
        mu6 = mumax
    if verbose:
        print("Curves {} and {}: testing ell up to {} mod {}".format(Elabel(E1),Elabel(E2),mu6,p))
    N1N2 = N1*N2
    for ell in prime_range(mu6):
        #print("testing ell = {}".format(ell))
        if ell==p:
            continue
        a1 = E1.ap(ell)
        a2 = E2.ap(ell)
        if ell.divides(N1N2):
            if N1N2.valuation(ell)==1 and (a1*a2-(ell+1))%p:
                return False, (ell,a1,a2)
        else:
            if (a1-a2)%p:
                return False, (ell,a1,a2)
    if mu6<actual_mu6:
        print("Warning! for curves {} and {}, to test for isomorphic semisimplifications we should have tested ell mod {} up to {}, but we only tested up to {}".format(Elabel(E1),Elabel(E2),p,actual_mu6,mu6))
    if verbose:
        print("The two mod-{} representations have isomorphic semisimplifications".format(p))
    if semisimp:
        return True, "up to semisimplification"
    #rho1 = E1.galois_representation()
    #rho2 = E2.galois_representation()
    #if rho1.is_irreducible(p) and rho2.is_irreducible(p):
    n1 = len(E1.isogenies_prime_degree(p))
    n2 = len(E2.isogenies_prime_degree(p))
    if n1==n2==0:
        if verbose:
            print("Both mod-{} representations are irreducible, hence they are isomorphic".format(p))
        return True, "irreducible"
    if n1==n2 and n1>1:
        if verbose:
            print("Both mod-{} representations are completely reducible, hence they are isomorphic".format(p))
        return True, "completely reducible"
    if  n1!=n2:
        return False, "nn"
    # now n1==n2==1 and it is harder to tell
    rho1 = E1.galois_representation()
    rho2 = E2.galois_representation()
    im1 = rho1.image_type(p)
    im2 = rho2.image_type(p)
    if im1 != im2:
        return False, "im"
    # Now they have the same image type.  If they are semistable at p
    # then they are isomorphic (either both have p-torsion point or
    # neither does)
    if N1.valuation(p)<=1 and N2.valuation(p)<=1:
        return True, "ss"
    # Giving up....
    return False, "ss" # flag that we have only proved that the semisimplfications are isomorphic

def report(res, info, p, lab1, lab2):
    if not res:
        print("Congruence mod {} fails for {} and {}".format(p,lab1,lab2))
        if info=="ss":
            print(" (isomorphic up to semisimplication but both are reducible, not totally reducible: failed to prove or disprove!)")
        elif info=="nn":
            print(" (isomorphic up to semisimplication but with different number of stable lines, so not isomorphic)")
        elif info=="im":
            print(" (isomorphic up to semisimplication but with different image types, so not isomorphic)")
        else:
            print(" (not even isomorphic up to semisimplication: {} )".format(info))
    else:
        print("{} and {} are proved to be congruent mod {} ({})".format(lab1,lab2,p,info))


def hash1(p,E,qlist):
    h = [E.ap(q)%p for q in qlist]
    return sum(ai*p**i for i,ai in enumerate(h))


def make_hash(p, N1, N2, np=20):
    plist = [next_prime(400000)]
    while len(plist)<np:
        plist.append(next_prime(plist[-1]))
    hashtab = {}
    nc = 0
    cremona_curves = cremona_optimal_curves(srange(N1,N2+1))
    for E in tqdm(cremona_curves, desc="Processing curves"):
        nc +=1
        h = hash1(p,E,plist)
        lab = E.label()
        #print("{} has hash = {}".format(lab,h))
        if h in hashtab:
            hashtab[h].append(lab)
            #print("new set {}".format(hashtab[h]))
        else:
            hashtab[h] = [lab]
    ns = 0
    for s in hashtab.values():
        if len(s)>1:
            ns += 1
            #print s
    print("{} sets of conjugate curves".format(ns))
    return hashtab


def test_irred(s, p=7):
    E = EllipticCurve(s[0])
    isog_pol = Fricke_polynomial(p)(x)-x*E.j_invariant()
    return len(isog_pol.roots())==0


def isogeny_kernel_field(phi, optimize=False):
    pol = phi.kernel_polynomial()
    Fx = pol.splitting_field('b',degree_multiple=pol.degree(), simplify_all=True)
    xP=pol.roots(Fx)[0][0]
    yP=phi.domain().lift_x(xP, extend=True)[1]
    Fxy = yP.parent()
    Fxy = Fxy.absolute_field('c')
    if optimize:
        Fxy = Fxy.optimized_representation()[0]
    return Fxy


###
### From here onwards it's our own code
###

def check_if_star_is_zero(E, p, prLim = 5):
    """
    Iteratively check if the star of the mod p representation of E is zero by checking the order of the mod p representation at different primes.
    This procedure is not 100% and it depends on the prLim set (prLim is the first prLim primes).
    """
    
    if type(E) == type("str"):
        lab = E
        E = EllipticCurve(lab)
    else:
        lab = E.cremona_label()
    badp = set([x[0] for x in list(E.conductor().factor())] + [p])
    pr = primes_first_n(prLim)
    _ = [pr.remove(p) for p in badp if p in pr]
    _ = magma.eval('E := EllipticCurve("{}");'.format(lab))
    _ = magma.eval('pr := {};'.format(pr))
    ans = magma.eval('{} in [Order(GL(2,{})!IntegralFrobenius(ChangeRing(E, GF(p)))) : p in pr];'.format(p,p))
    if ans == 'true':
        return False
    else:
        return True


def is_star_really_zero(lab, p):
    """
    This computes the field cut out by the p-torsion and checks if the star of the representation is zero explicitly.
    Of course this function is way slower than check_if_star_is_zero, but it is 100%.
    """
    E = EllipticCurve(lab)
    torFld = E.torsion_polynomial(p).splitting_field(names='a')
    return (mod(torFld.degree(), p) != 0)


def EC_star_field(E, p, optimize=True):
    """
    Compute the field cut out by the star in the representation (1, *), (0, 1)
    """
    # assume that a degree p isogeny exists
    if type(E) == type("str"):
        E = EllipticCurve(E)
    F_pol = Fricke_polynomial(p)
    t = F_pol.parent().gen()
    star_pol = F_pol - t * E.j_invariant()
    # Find a factor of degree p
    factors_of_degree_p = [f for f,e in star_pol.factor() if f.degree()==p]
    if not factors_of_degree_p:
        raise ValueError(f"No factor of degree {p} found in star polynomial factorization. Factors: {star_pol.factor()}")
    star_pol = factors_of_degree_p[0]  # Take the first one if multiple exist
    assert star_pol.is_irreducible()
    F = NumberField(star_pol, 's')
    if optimize:
        F = F.optimized_representation()[0]
    return F


def saturate_list(ss):
    """
    Saturate the list of curves by adding all curves in the isogeny class of each curve in the list ss.
    """
    saturated_list = []
    for isog in tqdm(ss):
        saturated = set(isog)
        for lab in isog:
            E = EllipticCurve(lab)
            isogeny_class = E.isogeny_class().curves
            for E2 in isogeny_class:
                saturated.add(Elabel(E2))
        saturated_list.append(list(saturated))
    return saturated_list


def remove_star_zero_cases_singleList(ss, p, prLim = 50):
    alive = []
    for lab in ss:
        E = EllipticCurve(lab)
        if not check_if_star_is_zero(E, p, prLim = prLim):
            alive.append(lab)
    return alive

def remove_star_zero_cases(ss, p, prLim = 50):
    """
    Remove cases where the top right corner entry of the mod p representation is zero. 
    This uses the function check_if_star_is_zero iteratively increasing the prime limit
    to eliminate false negatives.
    """
    filtered = []
    possible_star_zero_cases = []
    for isog in tqdm(ss):
        filtered_isog = remove_star_zero_cases_singleList(isog, p, prLim)
        removed = list(Set(isog) - Set(filtered_isog))
        newPrLim = prLim*2
        while removed and newPrLim < 1000:
            survivor = remove_star_zero_cases_singleList(removed, p, newPrLim)
            filtered_isog += survivor
            removed = list(Set(removed) - Set(survivor))
            newPrLim *= 2      
        filtered.append(filtered_isog)
        possible_star_zero_cases.append(removed)
    return filtered, possible_star_zero_cases    


def field_isomorphism(K1, K2):
    """
    I was getting errors using Sage's default .is_isomorphic (which uses pari's nfisom underneath)
    so we use Magma's IsIsomorphic function instead.
    """
    f1 = K1.defining_polynomial()
    f2 = K2.defining_polynomial()
    if f1.variable_name() != f2.variable_name():
        f2.change_variable_name(f1.variable_name())
    _ = magma.eval('PolyQ<{}> := PolynomialRing(Rationals());'.format(f1.variable_name()))
    _ = magma.eval('K1 := NumberField({});'.format(K1.defining_polynomial()))
    _ = magma.eval('K2 := NumberField({});'.format(K2.defining_polynomial()))
    return magma.eval('IsIsomorphic(K1, K2);')[0:4] == 'true'

#######################################################
######################## Mod 5 ########################
#######################################################
p = 5
# Compute the list of all possible curves whose p-torsion might be isomorphic by using the hash1 function
# this us a dictionary with key the hash (which is just the a_ell's of the curves as a p-adic integer) and
# the values are all curves with the same hash. Values of the dictionary of length < 1 are also removed. 
try:
    mod5_hashtable = load('IntermediateFiles/mod5_hashtable')
except IOError:
    mod5_hashtable = make_hash(p,11,500000,50)
    mod5_hashtable = dict([(k,v) for k,v in mod5_hashtable.items() if len(v)>1])
    save(mod5_hashtable, 'IntermediateFiles/mod5_hashtable')

isom_sets = mod5_hashtable.values()
print(len(isom_sets))

# Separate in reducible and irreducible mod p images since the treatment is different in each case.

isom_sets_red = []
isom_sets_irred = []
for s in isom_sets:
    isom_sets_irred.append(s) if test_irred(s,p) else isom_sets_red.append(s)
print("{} irreducible sets, {} reducible sets".format(len(isom_sets_irred),len(isom_sets_red)))

save(isom_sets_red, 'IntermediateFiles/mod5_isom_sets_red')
save(isom_sets_irred, 'IntermediateFiles/mod5_isom_sets_irred')

# Irreducible case:

# we use Kraus - Oesterlé bound to find which isomorphisms of the p-torsions are not really isomorphisms.
# (this needs to be more accurate, since we are using a static bound which does not work on all examples).
bad_pairs = []
for s in tqdm(isom_sets_irred):
    E1 = EllipticCurve(s[0])
    for r in s[1:]:
        E2 = EllipticCurve(r)
        res, info = test_cong(p,E1,E2, mumax=10^7)
        if not res:
            report(res,info,p,s[0],r)
            bad_pairs.append([s[0],r])

print("Found {} bad pairs".format(len(bad_pairs)))

assert len(bad_pairs)==0, "There are bad pairs in mod 5 isomorphism sets"

out = open("PairsLists/pairs_mod5_irred.m",'w')
out.write('pairs := [\\\n')
for i,s in enumerate(isom_sets_irred):
    for j,sj in enumerate(s):
        if j==0:
            continue    
        out.write('["{}", "{}"]'.format(s[0],sj))
        if j<len(s)-1 or i<len(isom_sets_irred)-1:
            out.write(',')
    out.write("\\\n")
out.write('];\n')
out.close()

print("Saved all irreducible pairs to mod5_IrredPairs.m")


# Reducible case:

# The main issue with the reducible case is that the mod p representation has the form 
# (1 *)
# (0 1)
# and sometimes * is zero. We need to eliminate these cases.

# first add all curves in the isogeny class for each curve in isom_sets_red
isom_sets_red_sat = saturate_list(isom_sets_red)
save(isom_sets_red_sat, 'IntermediateFiles/mod5_isom_sets_red_sat')

# load Centeleghe's code to compute the image of Frob_ell in Magma
magma.eval('load "IntFrobFunctions.m"')

# remove star zero cases
isom_sets_red_sat_nonzero, possible_zeros = remove_star_zero_cases(isom_sets_red_sat, 5)
for i in range(len(isom_sets_red_sat)):
    if possible_zeros[i]:
        for lab in possible_zeros[i]:
            iszero = is_star_really_zero(lab, 5)
            if iszero:
                print("Star of {} is really zero".format(lab))
            else:
                print("Star of {} is not really zero".format(lab))
                isom_sets_red_sat_nonzero[i].append(lab)

save(isom_sets_red_sat_nonzero, 'IntermediateFiles/mod5_isom_sets_red_sat_nonzero')
save(possible_zeros, 'IntermediateFiles/mod5_possible_zeros')


# Now from Cremona - Freitas https://arxiv.org/pdf/1910.12290 theorem 3.6 
# It states that the semisimplification of the mod p representation is a sum of characters
# χ + χ' (chip). We need to recognize whether the mod p representation is
# (χ  *)        (χ' *)
# (0 χ')   or   (0  χ)
# Of course the examples are one or another and their p-torsions will not be isomorphic between the two sets.
kernel_flds_chi = []
kernel_flds_chip = []
for ss in tqdm(isom_sets_red_sat_nonzero):
    base_curves = [EllipticCurve(lab) for lab in ss]
    isogenies = [E.isogenies_prime_degree(p)[0] for E in base_curves]
    isog_curves = [phi.codomain() for phi in isogenies]
    fld_chi = isogeny_kernel_field(isogenies[0], optimize=True)
    kernel_fld_chi = []
    kernel_fld_chip = []
    for i in range(len(base_curves)):
        if isogeny_kernel_field(isogenies[i], optimize=True).is_isomorphic(fld_chi):
           kernel_fld_chi.append(i)
        else:
            kernel_fld_chip.append(i)
    kernel_flds_chi.append(kernel_fld_chi)
    kernel_flds_chip.append(kernel_fld_chip)

save(kernel_flds_chi, 'IntermediateFiles/mod5_kernel_flds_chi')
save(kernel_flds_chip, 'IntermediateFiles/mod5_kernel_flds_chip')

# Finally, following the same theorem of Cremona-Freitas, we compute the fields F_1 and F_2 for each possible pair of
# elliptic curves E_1, E_2 respectively and check if they are isomorphic.
def pairs_mod_p_with_same_star_field(list, p):
    pairs = []
    starfield_dict = {EC_star_field(list[0], p, optimize=False) : [list[0]]}
    for i in range(1, len(list)):
        sf = EC_star_field(list[i], p, optimize=False)
        flag = 0
        for k in starfield_dict.keys():
            if field_isomorphism(k, sf):
                starfield_dict[k].append(list[i])
                flag = 1
                break
        if flag == 0:
            starfield_dict[sf] = [list[i]]
    for k, v in starfield_dict.items():
        if len(v) < 2:
            continue
        for i in range(len(v)):
            for j in range(i+1, len(v)):
                E1 = EllipticCurve(v[i])
                E2 = EllipticCurve(v[j])
                if E1.is_isogenous(E2) and gcd(E1.isogeny_degree(E2), p) == 1:
                    continue
                pairs.append([v[i], v[j]])
    return pairs

pairs = []
for iss in tqdm(range(len(isom_sets_red_sat_nonzero))):
    ss = isom_sets_red_sat_nonzero[iss]
    curves_with_chi_fld = [ss[x] for x in kernel_flds_chi[iss]]
    pairs += pairs_mod_p_with_same_star_field(curves_with_chi_fld, p)
    curves_with_chip_fld = [ss[x] for x in kernel_flds_chip[iss]]
    pairs += pairs_mod_p_with_same_star_field(curves_with_chip_fld, p)

out = open("PairsLists/pairs_mod5_red.m",'w')
out.write('pairs := [\\\n')
for i,s in enumerate(pairs):
    out.write('["{}", "{}"]'.format(s[0],s[1]))
    if i<len(pairs)-1:
        out.write(',')
    out.write("\\\n")
out.write('];\n')
out.close()

print("Saved all reducible pairs to pairs_mod5_red.m")

    

