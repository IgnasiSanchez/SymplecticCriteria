# Symplectic criteria for elliptic curves, revisited
## Authors: Freitas, Nuno; Kraus, Alain; Sánchez-Rodríguez, Ignasi.

This Github repository contains the code, intermediate files and final results for the article [Symplectic criteria for elliptic curves, revisited]() (_in Arxiv soon_).

# Requisites
It is a `Sagemath` and `Magma` project so one needs both to run the algorithms. 
The files `ComputePairs.sage` and `test_cong.m` are based on John Cremona's [Congruences](https://github.com/JohnCremona/congruences) code.

# How to reproduce the results
Let us explain in which order to run the files and what each one produces. We warn the user that this process takes a long time and requires a lot of memory to run, so it is adivisible to run in steps or to split the code in different parallel parts. 

1. (Section 7.1) The first step is to generate all pairs of non-isogenous elliptic curves with an isomorphism of the $p$-torsions, where $p\in {5,7,11,13,17}$. This is done by running `ComputePairs.sage`. The code from this file creates the lists `pairs_modp_red.m` and `pairs_modp_irred.m` in the folder `PairsLists` corresponding to all possible pairs $(E_1,E_2)$ with reducible and irreducible (respectively) mod $p$ representations such that $\rho_{E_1,p} \simeq \rho_{E_2,p}$ up to semisimplification. The lists are given as `Magma` lists for convenience.
To remove this _up to semisimplification_ condition, we do different approaches depending on the reducibility of the mod $p$ representations:
    - When it is irreducible, we run `ListsUpToQuadraticTwist.m`, which returns the lists in `IntermediateFiles` named `modp_irred_UpToTwist.m` (of pairs up to twist) and `modp_irred_UpToIsogeny.m` (of pairs up to twist and isogeny). Then one executes the proposition by Kraus which has been implemented in `test_cong.m`.
    - The reducible case is already handled in `ComputePairs.sage`.

    The code in `ComputePairs.sage` also creates a bunch of "checkpoint" files that are stored in `IntermediateFiles`. We leave the explanation of what each file stores to the user since it can be easily understood from the `save` calls in the code. 


2. After computing all possible pairs, one can split the lists into symplectic and antisymplectic isomorphisms between the $p$-torsions. This is handled by the code in `CheckSymplecticModp.m` which uses the functions in `InertiaTests.m` and `IntFrobFunctions.m` (this is handled internally and one does not need to worry about these files). This file creates the lists in `PairsLists` named `pairs_modp_(ir)red_symp.m` and `pairs_modp_(ir)red_antisymp.m`. 


3. After splitting every pair of curves $(E_1,E_2)$ into reducible or irreducible and symplectic or antisymplectic $p$-torsion isomorphisms, we find for each pair if there is any suitable $\ell$ that satisfies the hypothesis of Theorem 1.1 or Theorem 1.2 in the paper. This is handled by `checkPairs.m` and it creates the files in `PairsLists` named `pairs_modp_(ir)red_(anti)symp_withEll.m` which contains a list of triples $(E_1,E_2,\ell)$ that satisfy the hypothesis in Theorem 1.1 or 1.2. 

4. Finally, we provide the code in `checkSymplectic.m` which implements Theorems 1.1 and 1.2 which can be run in any of the `PairsLists/pairs_modp_(ir)red_(anti)symp_withEll.m` as a check that the algorithms are correct. 
