# Symplectic criteria for elliptic curves, revisited
## Authors: Freitas, Nuno; Kraus, Alain; Sánchez-Rodríguez, Ignasi.

This Github repository contains the code, intermediate files and final results for the article [Symplectic criteria for elliptic curves, revisited]() (_in Arxiv soon_).

# Requisites
It is a `Sagemath` and `Magma` project so one needs both to run the algorithms. 
The files `ComputePairs.sage` and `test_cong.m` are based on John Cremona's [Congruences](https://github.com/JohnCremona/congruences) code for the paper [[1]](#1).

# How to reproduce the results
Let us explain in which order to run the files and what each one produces. We warn the user that this process takes a long time and requires a lot of memory to run, so it is adivisible to run in steps or to split the code in different parallel parts. 

- **Step 1.** This step corresponds to Section 7.1. We first generate all pairs of non-isogenous elliptic curves with an isomorphism of the $p$-torsions, where $p\in ${5,7,11,13,17}. This is done by running `ComputePairs.sage`. The code from this file creates the lists `pairs_modp_red.m` and `pairs_modp_irred.m` in the folder `PairsLists` corresponding to all pairs $(E_1,E_2)$ with reducible and irreducible (respectively) mod $p$ representations such that the $a_p(E) = a_p(E')$ for the first 50 primes. The lists are given as `Magma` lists for convenience.
To prove the isomorphism between the $p$-torsions, we do different approaches depending on the reducibility of the mod $p$ representations:
    - In the irreducible case, we run `ListsUpToQuadraticTwist.m`, which returns the lists in `IntermediateFiles` named `modp_irred_UpToTwist.m` (of pairs up to twist) and `modp_irred_UpToIsogeny.m` (of pairs up to twist and isogeny). Then one executes Proposition 4 by Kraus-Oesterlé [[2]](#2) which has been implemented in `test_cong.m`. This proves isomorphism of the semisimple representations which is enough. 
    - The reducible case is handled differently depending on $p$:
        - For $p=7$, we follow the procedure applied to the irreducible case, but only for the pairs up to twist. Applying Kraus-Oesterlé [[2]](#2) gives isomorphism of the semisimple residual representations, and then the isomorphism of the $F$ fields (as it is explained in 6) of $\S7.1$ and Lemma 7.1) concludes the isomorphism of the mod $p$ representations by Cremona-Freitas.
        - For $p=5$, reducing the list is not necessary and the theoretical argument in Lemma 7.1 solves the problem. 

    The code in `ComputePairs.sage` also creates a bunch of "checkpoint" files that are stored in `IntermediateFiles`. The explanation of what each file stores can be easily understood from the `save` calls in the code. 


- **Step 2.** After computing all possible pairs, one can split the lists into symplectic and antisymplectic isomorphisms between the $p$-torsions. This is handled by the code in `CheckSymplecticModp.m` which uses the functions in `InertiaTests.m` [[3]](#3) and `IntFrobFunctions.m` [[4]](#4) (this is handled internally and one does not need to worry about these files). This file creates the lists in `PairsLists` named `pairs_modp_(ir)red_symp.m` and `pairs_modp_(ir)red_antisymp.m`. 


- **Step 3.** After splitting every pair of curves $(E_1,E_2)$ into reducible or irreducible and symplectic or antisymplectic $p$-torsion isomorphisms, we find for each pair if there is any suitable $\ell$ that satisfies the hypothesis of Theorem 1.1 or Theorem 1.2 in the paper. This is handled by `checkPairs.m` and it creates the files in `PairsLists` named `pairs_modp_(ir)red_(anti)symp_withEll.m` which contains a list of triples $(E_1,E_2,\ell)$ that satisfy the hypothesis in Theorem 1.1 or 1.2. There can be multiple triples with the same $E_1$ and $E_2$ but different $\ell$. 

- **Step 4.** Finally, we provide the code in `checkSymplectic.m` which implements Theorems 1.1 and 1.2 which can be run in any of the `PairsLists/pairs_modp_(ir)red_(anti)symp_withEll.m` as a check that the algorithms are correct. 

## References
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
