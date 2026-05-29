# Symmetric products in HoTT

## Repo structure

- Most of the relevant code is in the folder `SymmetricProducts`.
- The folder `Ideas` shows ideas that seem like they might lead towards a definition of symmetric products, but are hard to get with any further, or misguided.
- The folder `Experiments` contains possible future directions for the repo, but has some AI generated code.
- The folder `Utilities` contains relevant additions to the standard library.

## What is done

This repo contains a working definition of the second symmetric product (in `OrbitSP2.ard`) and third symmetric product
(in `PushoutSP3.ard`). It contains a direct calculation of the second symmetric product of the two-element set 
that can be extended to a calculation of the second symmetric product of a general decidable set.

There are formalized facts about the classifying space of the n-th symmetric group (in `BSn.ard` and `Commutative.ard`) and the Borel quotient of
the cartesian power of a space (in `Borel.ard`). Most of these facts come from a paper by Axel Ljungstrom and David Warn.

The result by Ulrik Buchholtz that $SP^2$ sends sets to sets is also formalized (in `SP2OfSet.ard` and `SetSP2.ard`).

At the moment, the definition of the $n$-th symmetric product for a general $n$ is not formalized.
The fundamental group of $SP^2$ is also not yet calculated.