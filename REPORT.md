# Symmetric Products in HoTT — Repository Report

A formalization of *symmetric products* SP^n(A) in HoTT-style synthetic
algebraic topology, written in [Arend](https://arend-lang.github.io/). The
project explores an axiomatic, BSn-indexed definition of SP^n that avoids
explicit set quotients in favor of the classifying space of the symmetric
group.

Source: `src/*.ard` (12 modules, ~1400 lines). Compiled with `arend.yaml`
against `arend-lib`. Running `arend` from the repo root reproduces the goal
list quoted below.

---

## 1. The central idea

The classical (topological) symmetric product is
SP^n(X) = X^n / Σ_n. Naively transcribing this to HoTT — e.g. as a
HIT on pairs with explicit symmetry constructors — does not give the
intended homotopy type. The repository even contains an explicit
counterexample:

- **`SPnInductiveWrong.ard`.** A natural-looking HIT for SP² with constructors
  `delta a`, `inSP a a'`, `inSPEq : inSP a a' = inSP a' a`, and
  `deltaEq : inSP a a = delta a` is shown to satisfy
  `SP² (Unit) = S¹`, where the correct answer is `Unit`. This rules out
  the naive HIT.

The chosen synthetic definition uses the connected groupoid

```
BSn n := Σ(X : Set), ‖ X ≃ Fin n ‖
```

i.e. *finite sets merely-equivalent to `Fin n`*. `BSn n` is a (1-truncated)
classifying space of Σ_n (for the constructions here `\Set` is enough),
and any map `X.1 → A` out of an element `X : BSn n` represents an
unordered n-tuple in `A`. This is packaged as the *commutative-function
structure* (`Commutative.ard`):

```
commstr n A B := Π (X : BSn n) → (X.1 → A) → B
```

Because `BSn n` is connected, a `commstr` is automatically symmetric:
specializing to a particular `X` already factors through the action of
permutations.

**The axiom (`SPnAxioms.ard`).** `SPnA` is a symmetric product of `A` of
arity `n` if it is a free type for the `commstr`-structure:

```
SPnAxiom A SPnA :=
  Σ (inj : commstr n A SPnA)
    Π (T : Type) (g : commstr n A T)
       ∃! h : SPnA → T  such that  ∀ x : Fin n → A, h (inj x) = g x
```

This reflects the universal property of the symmetric power as a left
adjoint, internally to HoTT, with `BSn n` taking the role of "Σ_n
torsor". The Borel construction
`borelXn n A := Σ (X : BSn n), X.1 → A`
is the obvious *fat* candidate for SP^n in degree 0; SP^n is then the
correct quotient/colimit on top of that.

---

## 2. What has been formalized

### Foundational layer

- **`BSn.ard` (≈460 lines).** The bulk of the technical infrastructure:
  basepoint `BSnbase`, path characterization via Univalence, connectedness
  (`connBSn`), prop-induction principles `recPropBSn` / `recPropBSn'`,
  decidable equality on the underlying set, contractibility of the total
  space `Σ (X : BSn n) (X ≃ Fin n)`, and the special-case eliminators
  `JBS2`, `elimBS2`, `setRecBS2` for `BSn 2` (including the swap
  `notBS2 : X.1 → X.1` and its involutivity). Also `extendBSn :
  BSn n → BSn (n+m)`.

- **`Borel.ard`.** The Borel construction `borelXn n A`, with:
  connectivity transfer (`connectedToBorelXnConnected`),
  `borelXn 1 X = X`,
  `borelXn n Unit = BSn n`,
  the pointed Borel construction `pointedBorelXn n (A,*)` as a pushout, and
  `Contr (pointedBorelXn n Unit)`.

- **`Commutative.ard`.** The `commstr` definition with helpers
  (`compose`, `precompose`, `constant`), and the explicit symmetry lemma
  `commstr2IsComm` in arity 2 (i.e. `f (a,b) = f (b,a)`).

- **`Utilities.ard`.** Sigma-path lemmas, `Or` associativity, `WellFoundedPoset`
  scaffolding, transport / coercion helpers, `OrlevelProp`, `funcToUnit`,
  etc.

### The axiomatic SP^n layer

- **`SPnAxioms.ard`.** General theorems about *any* type satisfying
  `SPnAxiom`:
  - **Uniqueness:** `SPnUniqueness` — two SP^n's of the same `A` are
    canonically equivalent.
  - **Singleton:** `contrSPnContr` — SP^n(Unit) = Unit.
  - **Inclusion:** `injSPnSPsucn : SPnA → SP_{n+1}A` for any `bp : A`.
  - **Functoriality:** `functorialSPn : (A → B) → SPA → SPB`.
  - **Connectedness preservation:** `isConnectedSPnX` — if `X` is
    0-connected, so is `SPnX` (modulo one technical hole, see §3).

- **`AlternativeCommf.ard`.** A second axiomatization
  `SPnAxiomAlt` based on `commfunc n A B = Σ f : (Fin n → A) → B,
  ‖ f extends to a commstr ‖`, and a translation `RegToAlt` /
  `AltToReg` between the two.

### Concrete constructions

- **`OrbitSP2.ard`.** A HIT model `SP2 A` with constructors
  `sigma : borelXn 2 A → SP2 A`,
  `delta : A → SP2 A`,
  `tau : delta a = sigma (X, λ_ ↦ a)` for every `a : A`, `X : BSn 2`.
  Includes the dependent eliminator and a universal property —
  **but with respect to an auxiliary structure `dcommf2`, not the
  `commstr 2` of `SPnAxiom`**. Specifically:

  ```
  dcommf2 A T := Σ (f : commstr 2 A T)
                   (Π (a : A) (X : BSn 2), f (BSnbase 2) (λ_ ↦ a) = f X (λ_ ↦ a))
  ```

  i.e. a `commstr 2` enriched with a chosen path connecting the constant
  tuples. The file proves `injSP2 : dcommf2 A (SP2 A)`,
  `liftSP2 : dcommf2 A T → SP2 A → T`, and uniqueness `liftSP2.uniq`
  for that lifting. It also proves `SP2 Unit = pointedBorelXn 2 Unit`,
  hence `Contr (SP2 Unit)`.

  > ⚠ **The bridge `dcommf2 ↔ commstr 2`, and consequently the statement
  > `SPnAxiom {2} A (SP2 A)`, are not formalized in the repository.**
  > Every `commstr 2 A T` does give the dcommf2 coherence *merely* —
  > because `BSn 2` is connected — but a chosen path is extra data. This
  > is the same issue that `AlternativeCommf.ard` addresses for the
  > `commstr ↔ commfunc` direction; the analogous translation has not
  > been written here.

- **`SetSP.ard`.** A set-truncated variant `SetSP2 A` with a single
  symmetry path constructor; commstr injection and recursor are written
  out, and the file *attempts* the corresponding set-truncated axiom
  `isSPSetSP : SPnAxiomSet {2} A (SetSP2 A)`, but the existence and
  uniqueness witnesses are still `{?}` (see §3).

- **`SP2OfBool.ard` (≈380 lines).** The flagship concrete computation:

  > **`sp22Type : SP2 (Fin 2) = Fin 3`**

  i.e. SP²({0,1}) = {00, 01, 11}. Strategy: decompose
  `borelXn 2 (Fin 2)` into "constant 0", "constant 1" and "off-diagonal"
  pieces (`borel2`), notice that each `tau a` collapses the constant
  copy of `BSn 2` to the corresponding `delta a`, identify the result
  with `Or (Or coneBS2 coneBS2) Unit`, and contract the two cones. The
  bulk of the file is bookkeeping for the path constructors `tau 0`,
  `tau 1`. Note that this gives the correct *underlying type* of SP²
  on `Fin 2`, but does so for the HIT `SP2 A`, whose link to
  `SPnAxiom {2}` is itself open (see above).

- **`PushoutSP3.ard`.** Definition of `SP3 X` as an iterated pushout and
  the proof `SP3ContrIsContr : Contr (SP3 Unit)` via reduction to a
  pushout of an equivalence.

- **`LEMConnectedness.ard`.** A reusable lemma `connectedLem`: a type with
  decidable path-truncations is connected if every Boolean-valued
  function on it is constant. Used to derive connectedness of SP^n from
  connectedness of the underlying type.

### Currently milestoned (commit log)

```
537655c SP^2(2)=3              ← latest
ab87f6d Borel quotient of 2^2
08e2175 Skeleton of SP^2 of Fin 2
e7f983e Skeleton of SP^n
85edec8 Prove SP3(*)=*
```

---

## 3. Open goals

`arend` reports **15 holes across 3 modules**: `SPn`, `SPnAxioms`, `SetSP`
(plus 2 scratch goals in `SPnInductiveWrong` and 2 in the now-obsolete
`Join.ard` — see §5 for the May 2026 round of work that closed `SetSP`'s
main goals and the `Trunc0Eq` goal in `Utilities`).
The remaining modules typecheck cleanly. In addition there are two
*unstated* gaps — items not even claimed as goals — that are documented
below.

### Key open goals

**(A) Bridging `dcommf2` and `commstr 2`; proving the SP^2 axiom for the
HIT model.** As flagged in §2, the universal property of `OrbitSP2.SP2`
is established only against `dcommf2`. The statement

```
SP2axiom : Π {A : Type}, SPnAxiom {2} A (SP2 A)
```

is **not formalized at all** — there is no `{?}`, the lemma is simply
absent, and `OrbitSP2.ard` does not even `\import SPnAxioms`. This is a
real gap: without it, none of the meta-theorems in `SPnAxioms.ard`
(uniqueness, connectedness preservation, SP^n(Unit)=Unit, inclusion,
functoriality) apply to `SP2 A`. Closing it requires a translation
`commstr 2 A T → dcommf2 A T` (and back), which in turn needs a
canonical choice of path between constant tuples — likely via the
`BS2`-induction principle `JBS2` already in `BSn.ard`.

**(B) The general SP^n construction — `SPn.ard`.** The central
unfinished piece. The intended construction expresses SP^n(X) as an
iterated pushout indexed by the well-founded poset of integer
partitions of `n`, gluing in for every partition λ a *contractible*
"orbit space" `contrSpace λ` parameterizing how the partition λ embeds
into a smaller one. The skeleton lays out:

- `partitionInto n k`, `partitions n`, `partitionCount` (✓ defined)
- `wfPartitions n : WellFoundedPoset` — **`<`, irreflexivity, transitivity,
  potential, monotonicity all `{?}`** (lines 41–45)
- `powerPartition.extend : powerPartition → borelXn n X` — `{?}` (line 37)
- `partExtensionsType`, `partExtension`, `classTypeExtension`,
  `iOnExtension` — all `{?}` (lines 47–55, 80)
- `contrF`, `contrG` — the two pushout legs of `SP-step n d X`
  (lines 109–121) — partial / `{?}`
- `contrInclusion` — termination via `<`-recursion needs the missing
  `<` (line 132)

Even when (B) is filled in, the resulting type still has to be shown to
satisfy `SPnAxiom`; that proof is also not yet stated.

**(C) `SetSP.ard` — set-truncated SP² satisfies its axiom.** The
universal property
`isSPSetSP : SPnAxiomSet {2} A (SetSP2 A)`
has its `inj` filled in but the `Contr` witness — both the coherence
`Π x → liftSetSP2 g (inj x) = g x` and the contraction onto every
candidate `h` — are `{?}`. This is the analogue at the
set-truncated level of (A). (The closely-related `setTruncSP2` and
`setTruncNaiveSP2` are *closed* — see §5.)

**(D) `SPnAxioms.ard:53` — connectedness of SP^n preserved.** In
`isConnectedSPnX`, after using `connectedLem` to reduce to "every
`Bool`-valued function on SPX is constant", the proof needs

```
TruncP (Π y : Fin n → X, mapValue = commstr.f map y)
```

from the pointwise `TruncP (mapValue = commstr.f map y)`. This is
"axiom of choice through Π over a non-set", which is not generally
available. The author's comment marks the problem explicitly:

> `{?} -- Here we would need to apply the axiom of choice to something
> that isn't a set. I have no idea how to fix it`

A real fix probably routes around `Bool` (use a strictly stronger
classifier) or replaces `connectedLem` by a direct connectedness
argument on `Borel`-style cofibers.

### Small / technical goals

The remaining `SPn` goals (lines 37, 41–55, 81, 113–121, 132) are all
downstream of (B): once the well-founded order on partitions and the
extension machinery are in place, those holes become routine. They are
not independent open problems.

---

## 4. Status summary

| Module | Status | Highlights |
|---|---|---|
| `BSn` | ✓ | Path char., contractible total, `JBS2`, `elimBS2` |
| `Borel` | ✓ | `Connected0`, `borelXn 1 = id`, pointed Borel |
| `Commutative` | ✓ | `commstr` and arity-2 symmetry |
| `LEMConnectedness` | ✓ | reusable connectedness lemma |
| `Utilities` | ✓ | sigma paths, well-founded poset class |
| `OrbitSP2` | ✓ \* | SP² HIT, recursor, `SP² Unit ≃ pointedBorelXn 2 Unit`. \* Universal property is for `dcommf2`, not `commstr 2`; SP^2-axiom for `SP2 A` is **not stated/proved**. |
| `SP2OfBool` | ✓ \* | **`SP² (Fin 2) = Fin 3`** for the HIT model; depends on (A) for an axiomatic reading. |
| `PushoutSP3` | ✓ | **`Contr (SP³ Unit)`** |
| `AlternativeCommf` | ✓ | equivalent axiomatization (commstr ↔ commfunc) |
| `SPnInductiveWrong` | ✓ | counterexample: naive HIT yields `S¹` |
| `SPnAxioms` | ◯ | uniqueness, singleton, inclusion, functoriality; 1 hole in `isConnectedSPnX` |
| `SetSP` | ✓ \* | `SetSP2 A = Trunc0 (borelXn 2 A)` and `SetSP2 A = Trunc0 (naive SP2 A)` proven; `isSPSetSP` (universal property) still open. |
| `SPn` | ◯ | partition-pushout scaffolding only — main open piece |

**Headline results actually proved.**
- `Contr (SP³ Unit)` (in the pushout model `SP3` of `PushoutSP3.ard`).
- `SP² (Fin 2) = Fin 3` (in the HIT model `SP2` of `OrbitSP2.ard`).
- Uniqueness up to equivalence of any type satisfying `SPnAxiom`,
  `SPnAxiom`-singleton = Unit, inclusion `SPn → SP_{n+1}`, functoriality.
- `SetSP2 A = Trunc0 (borelXn 2 A)` for any `A : \Type` (`setTruncSP2`).
- `SetSP2 A = Trunc0 (naive SP2 A)` for any `A : \Type` (`setTruncNaiveSP2`),
  formalizing "SP²(Set) is the 0-truncation of the naive HIT".
- `Trunc0 A = A` for any set `A` (`Trunc0Eq` in `Utilities`).

**Headline results not yet proved.**
- That the HIT `OrbitSP2.SP2 A` satisfies `SPnAxiom {2} A` — i.e. that
  the concrete model is a symmetric product in the axiomatic sense
  (open goal A).
- Existence of any type satisfying `SPnAxiom` for general `n`, via the
  partition-indexed pushout construction in `SPn.ard` (open goal B).

---

## 5. Round of work — May 2026

Three goals closed in this round (`src/SetSP.ard` and `src/Utilities.ard`):

### 5.1 `Trunc0Eq` (Utilities.ard)

Statement: `Trunc0 A = A` whenever `A : isSet`.

Proof: an `iso` whose forward leg is a `\sfunc f` pattern-matching on
`Trunc0 A` with codomain annotated `\level pr` (`pr : isSet A`), and the
two round-trip equations chained through `\peval f (in0 a)`.

### 5.2 `setTruncNaiveSP2` (SetSP.ard)

Statement:

```
setTruncNaiveSP2 : Π {A : \Type}, SetSP2 A = Trunc0 (NaiveSP2 A)
```

where `NaiveSP2` is `SPnInductiveWrong.SP2` (the 4-constructor naive HIT).
This formalizes the slogan *"SP²(Set) is presented by 0-truncating the
naive symmetric-product HIT."*

The proof is structural: each constructor on one side maps to a same-shaped
constructor (or `idp` for `deltaEq`, since `delta a` and `inSP a a`
both collapse to `inSP2 a a` after truncation) on the other; the
path-constructor clauses in `sec`/`ret` are auto-filled by Arend because
both targets sit in a set.

### 5.3 `setTruncSP2` (SetSP.ard)

Statement:

```
setTruncSP2 : Π {A : \Type}, SetSP2 A = Trunc0 (borelXn 2 A)
```

— the *original* open goal. Decomposed into four parts:

- **`swapBorel a a'`** — the swap path
  `(BSnbase 2, recFin2 a a') = (BSnbase 2, recFin2 a' a)` in `borelXn 2 A`.
  Built as a `SigmaPath`: first component
  `BSnPath (BSnbase 2) (BSnbase 2) notBS2.notFin2Eq`, second component
  computed via `transport-proj1` (a local Jl-lemma reducing
  BSn-transport to `\Type`-transport on the underlying set) followed by
  `path-fun.transport-fun`, ending in a `funExt` case-split on `Fin 2`.

- **`borelToSetSP2 X f`** — the inverse map, defined via
  `TruncP.rec-set X.2` so the BSn-component is consumed by an
  equivalence-branch. The coherence is the four-way case split on
  `e2 (e1.ret 0), e2 (e1.ret 1)` in `Fin 2`: the two diagonal cases are
  absurd (contradicting injectivity of `e2`), the `(0,1)` case is `idp`,
  the `(1,0)` case applies `symSP2`.

- **`borelToSetSP2-base f`** — the beta-rule
  `borelToSetSP2 (BSnbase 2) f = inSP2 (f 0) (f 1)`. Since
  `TruncP.rec-set` is `\lemma`-opaque, the equality is proven by
  constructing a manual `Σ`-element `(inSP2 (f 0) (f 1), inP (idEquiv,
  idp))` and invoking `TruncP.rec-set.level` (the Prop-uniqueness of
  the existential-tagged `Σ`).

- The **iso assembly** itself: `to` uses `swapBorel` for the `symSP2`
  case; `sec` uses `borelToSetSP2-base`; `ret` uses `recPropBSn'` to
  prop-induct on `X` (the predicate `Π g, to (borelToSetSP2 Y g) =
  in0 (Y, g)` is propositional because `Trunc0 (borelXn 2 A)` is a set);
  the basepoint case `retBorelBase` composes `borelToSetSP2-base` with
  `elimBS2.recFin2BetaSimp` to recover the original `f`.

The proof uses no machinery beyond what `BSn.ard`, `Borel.ard`,
arend-lib's `Logic` (`TruncP.rec-set`), and arend-lib's `Equiv.Univalence`
already provide.

### 5.4 Notes

- The local `Join.ard` is obsolete; arend-lib now ships
  `Homotopy.Join`. `SP2OfSet.ard` still consumes the local file
  (encode-decode and `joinEqLeft`/`joinContrSet`/`joinSet` are not in
  the upstream version); migrating it is its own project.
- Two scratch goals (`lol`, `lol2`) at the top of `SPnInductiveWrong.ard`
  are unrelated experimental code; they error because `nil` is not
  imported as a constructor.
