# Symplectic criteria for elliptic curves, revisited
## Authors: Freitas, Nuno; Kraus, Alain; Sánchez-Rodríguez, Ignasi.

This Github repository contains the code, intermediate files and final results for the article [Symplectic criteria for elliptic curves, revisited]() (_in Arxiv soon_).

# Requisites
It is a `Sagemath` and `Magma` project so one needs both to run the algorithms. 
The files `ComputePairs.sage` and `test_cong.m` are based on John Cremona's [Congruences](https://github.com/JohnCremona/congruences) code for the paper [[1]](#1).

# How to reproduce the results
Let us explain in which order to run the files and what each file does. We warn the user that this process takes a long time and requires a lot of memory to run, so it is adivisible to run in steps or to split the code in different parallel parts. 

- **Step 1.** This corresponds to Section 7.1. We generate all pairs of non-isogenous elliptic curves with an isomorphism of the $p$-torsions, where $p\in ${5,7,11,13,17}. This is done by running `ComputePairs.sage`. The code from this file creates the lists `pairs_modp_red.m` and `pairs_modp_irred.m` in the folder `PairsLists` corresponding to all pairs $(E_1,E_2)$ with reducible and irreducible (respectively) mod $p$ representations such that the $a_p(E) = a_p(E')$ for the first 50 primes $> 500 000$. The lists are given as `Magma` lists for convenience. This procedure *does not* prove the isomorphism yet. To complete the proof continue as described in the subsection below.

    The code in `ComputePairs.sage` also creates "checkpoint" files that are stored in `IntermediateFiles`. The explanation of what each file stores can easily be understood from the `save` calls in the code. 


- **Step 2.** After computing all pairs as above, we split the lists into symplectic and antisymplectic isomorphisms. This is handled by `CheckSymplecticModp.m` which uses the functions in `InertiaTests.m` [[3]](#3) and `IntFrobFunctions.m` [[4]](#4) (this is handled internally and one does not need to worry about these files). This file creates the lists in `PairsLists` named `pairs_modp_(ir)red_symp.m` and `pairs_modp_(ir)red_antisymp.m`. 


- **Step 3.** By this point we have divided the pairs into reducible or irreducible and symplectic or antisymplectic $p$-torsion isomorphisms. For each pair, we find if there is any prime $\ell$ satisfying the hypothesis of Theorem 1.1 or Theorem 1.2 in the paper. This is handled by `checkPairs.m` and it creates the files in `PairsLists` named `pairs_modp_(ir)red_(anti)symp_withEll.m` which contains a list of triples $(E_1,E_2,\ell)$ that satisfy the hypothesis in Theorem 1.1 or 1.2. There can be multiple triples with the same $E_1$ and $E_2$ but different $\ell$. 

- **Step 4.** Finally, we provide the code in `checkSymplectic.m` which implements Theorems 1.1 and 1.2 which can be run in any of the `PairsLists/pairs_modp_(ir)red_(anti)symp_withEll.m` as a sanity check for the previous computation. 

#### Proving the isomorphisms between the $p$-torsions
We first group the pairs $(E1,E2)$ by $j$-invariants $(j1,j2)$ and keep only one representative among all pairs $(dE1,dE2)$ using `ListsUpToQuadraticTwist.m`. 
This function also removes the pairs with j-invariant pair $(0,0)$ or $(1728,1728)$, which are to be treated separately. Then, for the list of pairs up to twist, we apply Kraus-Oesterlé [[2]](#2). This computation requires some modifications depending on the reducibility of the mod $p$ representations for $E_1$ and $E_2$:  

- In the **irreducible** case, we run `ListsUpToQuadraticTwist.m`, which returns the lists in `IntermediateFiles` named `modp_irred_UpToTwist.m` (of pairs up to twist) and `modp_irred_UpToIsogeny.m` (of pairs up to twist and isogeny). Then one executes Proposition 4 by Kraus-Oesterlé [[2]](#2) which has been implemented in `test_cong.m`, proving the isomorphism of the semisimplifications of the representations which is enough as they are irreducible. 
*Remark:* For $p=5$ this method can take a very long time, so we implemented an alternative method. The code for it is also written in `test_cong.m` in the functions `test_cong_mod5_antisymp` and `test_cong_mod5_symp` which implement the parametrizations of Fisher [[5]](#5) and Rubin-Silverberg [[6]](#6) respectively and give all possible $5$-congruent curves to $E1$, in which we find $E2$.

- The **reducible** case occurs only for $p=5,7$ and is handled differently depending on $p$:
    - For $p=7$, we apply Kraus-Oesterlé [[2]](#2) to obtain the isomorphism of the semisimplifications of the representations, and then test the isomorphism of the fields where the curves acquire a second isogeny (as explained in 6) of $\S7.1$), hence concluding the isomorphism of the mod $p$ representations by [[1]](#1).
    - For $p=5$, to avoid using Kraus-Oesterlé as this would take a long time, we check equality of isogeny fields and use Lemma 7.2, to establish the ismorphism of the semisimplifications. Then we continue as for $p=7$. 

- Finally, the cases with j-invariant $(0,0)$ or $(1728,1728)$ are handled by `jInvariant0Cases.m` using implementations of Corollary 2.5 and Theorem 1.2 of [[1]](#1).

# Other files
- The code for Example 5.3 in the article can be found in `CheckSymplecticBigExample.m`.
- The code to generate the reducible examples for $p=5$ in section 7.3 can be found in `ReducibleMod5Examples.m`.

# References
<a id="1">[1]</a> J. Cremona and N. Freitas.
Global methods for the symplectic type of congruences between elliptic curves.
Rev. Mat. Iber., 38(1):1--32, 2022.

<a id="2">[2]</a> A. Kraus and J. Oesterlé.
ur une question de B. Mazur.
Math. Ann., 293(2):259--275, 1992.

<a id="3">[3]</a> N. Freitas and A. Kraus.
On the symplectic type of isomorphisms of the $p$-torsion of elliptic curves.
Memoirs of AMS, (2022), no. 1361.

<a id="4">[4]</a> T. G. Centeleghe.
Integral Tate modules and splitting of primes in torsion fields of elliptic curves.
International Journal of Number Theory, 2012.

<a id="5">[5]</a> K. Rubin and  A. Silverberg.
Families of elliptic curves with constant mod $p$ representations.
Elliptic curves, modular forms, & Fermat's last theorem (Hong Kong, 1993), 148–161.

<a id="6">[6]</a> T. Fisher.
Invariant theory for the elliptic normal quintic, I. Twists of X(5).
Math. Ann. 356 (2013), no. 2, 589–616.