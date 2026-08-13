# Symmetric products in HoTT

## Repo structure

- Most of the relevant code is in the folder `SymmetricProducts`.
- The folder `Ideas` shows ideas that seem like they might lead towards a definition of symmetric products, but are hard to get with any further, or misguided.
- The folder `Experiments` contains AI generated code of proven problems and possible future directions.
- The folder `Utilities` contains relevant additions to the standard library.

#### Recent developments

- Added proof that $\pi_1(SP^2(A))=(\pi_1(A))^{ab}$ for $A$ connected
- Added proof that $SP^3$ sends sets to sets

## What is done

This repo contains a working definition of the second symmetric product (in `SP2.ard`) and third symmetric product
(in `SP3.ard`). It contains a direct calculation of the second symmetric product of the two-element set 
that can be extended to a calculation of the second symmetric product of a general decidable set.

There are formalized facts about the classifying space of the n-th symmetric group (in `BSn.ard` and `Commutative.ard`) and the Borel quotient of
the cartesian power of a space (in `Borel.ard`). Most of these facts come from a paper by Axel Ljungstrom and David Warn.

The result by Ulrik Buchholtz that $SP^2$ sends sets to sets is also formalized (in `SP2OfSet.ard` and `SetSP2.ard`).

It has been proven (with an LLM-assisted proof) that $SP^3$ sends sets to sets (see `Experiments.SP3`) and that the fundamental group of $SP^2(A)$ is the abelianization of the fundamental group of $A$ for a connected $A$ (see `Experiments.HomotopyGroup.SP2`).

At the moment, the definition of the $n$-th symmetric product for a general $n$ is not formalized, and the sketch can be found in `Experiments.SPn`