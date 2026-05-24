# Symmetric Products in HoTT — Repository Report

A formalization of *symmetric products* SP^n(A) in HoTT-style synthetic
algebraic topology, written in [Arend](https://arend-lang.github.io/). The
project explores an axiomatic, BSn-indexed definition of SP^n that avoids
explicit set quotients in favor of the classifying space of the symmetric
group.

Source: `src/*.ard` (15 modules, ~3100 lines). Compiled with `arend.yaml`
against `arend-lib`. As of this report **14 open `{?}` goals remain across
3 modules**: `SPn` (10), `HomotopyGroup` (3), `SPnAxioms` (1).

---

## 1. The central idea

The classical (topological) symmetric product is SP^n(X) = X^n / Σ_n. Naively
transcribing this to HoTT — e.g. as a HIT on pairs with explicit symmetry
constructors — does not give the intended homotopy type. The repository even
contains an explicit counterexample (`SPnInductiveWrong.ard`): the natural HIT
for SP² satisfies `SP² (Unit) = S¹` instead of `Unit`.

The chosen synthetic definition uses the connected groupoid

```
BSn n := Σ(X : Set), ‖ X ≃ Fin n ‖
```

i.e. *finite sets merely-equivalent to `Fin n`*. Any map `X.1 → A` out of an
element `X : BSn n` represents an unordered n-tuple in `A`. This is packaged
as the *commutative-function structure* (`Commutative.ard`):

```
commstr n A B := Π (X : BSn n) → (X.1 → A) → B
```

Because `BSn n` is connected, a `commstr` is automatically symmetric. The
axiomatic definition (`SPnAxioms.ard`) is then:

```
SPnAxiom A SPnA :=
  Σ (inj : commstr n A SPnA)
    Π (T : Type) (g : commstr n A T)
       ∃! h : SPnA → T  such that  ∀ x : Fin n → A, h (inj x) = g x
```

---

## 2. Status overview

| Module | Status | Notes |
|---|---|---|
| `BSn` | ✓ | Path char., contractible total, `JBS2`, `elimBS2`, `setRecBS2` + new universal `setRecBS2.beta` |
| `Borel` | ✓ | `Connected0`, `borelXn 1 = id`, pointed Borel |
| `Commutative` | ✓ | `commstr` and arity-2 symmetry |
| `LEMConnectedness` | ✓ | reusable connectedness lemma |
| `Utilities` | ✓ | sigma paths, well-founded poset class, `Trunc0Eq` |
| `OrbitSP2` | ✓ \* | SP² HIT, recursor, `SP² Unit ≃ pointedBorelXn 2 Unit`. \* Universal property is for `dcommf2`, not `commstr 2`; SP^2-axiom for `SP2 A` is **not stated/proved**. |
| `SP2OfBool` | ✓ \* | **`SP² (Fin 2) = Fin 3`** for the HIT model; depends on the dcommf2↔commstr2 bridge for an axiomatic reading. |
| `PushoutSP3` | ✓ | **`Contr (SP³ Unit)`** |
| `AlternativeCommf` | ✓ | equivalent axiomatization (commstr ↔ commfunc) |
| `SPnInductiveWrong` | ✓ | counterexample: naive HIT yields `S¹` |
| `SetSP` | ✓ | `SetSP2 A = Trunc0 (borelXn 2 A)` and `SetSP2 A = Trunc0 (naive SP2 A)`. Now uses `setSP2Inj` + `setSP2Inj.base` instead of the separate `borelToSetSP2` helper. |
| `SPnAxioms` | ◯ | uniqueness, singleton, inclusion, functoriality; 1 hole in `isConnectedSPnX` (choice-over-non-set) |
| `SPn` | ◯ | partition-pushout scaffolding. `wfPartitions` instance now closed; 10 holes remain in the extension/pushout machinery. |
| `HomotopyGroup` | ◯ | π_n + functoriality + Eckmann-Hilton complete. `GroupPushout` HIT with hom constructors + universal property (`recHom`) proved. Van Kampen back-direction (`vanKampen-back`) closed, including `pushoutVanKampen-coh` / `loop-bridge` / `rhs-to-canonical` / `pgrg-cancel`. Remaining: 3 holes, all on the forward (encode-decode) side. |
| ~~`Join`~~ | removed | retired in §3.6; uses arend-lib's `Homotopy.Join` now. |

**Headline results actually proved.**
- `Contr (SP³ Unit)` (in the pushout model `SP3` of `PushoutSP3.ard`).
- `SP² (Fin 2) = Fin 3` (in the HIT model `SP2` of `OrbitSP2.ard`).
- Uniqueness up to equivalence of any type satisfying `SPnAxiom`,
  `SPnAxiom`-singleton = Unit, inclusion `SPn → SP_{n+1}`, functoriality.
- `SetSP2 A = Trunc0 (borelXn 2 A)` for any `A : \Set` (`setTruncSP2`).
- `SetSP2 A = Trunc0 (naive SP2 A)` for any `A : \Set` (`setTruncNaiveSP2`).
- **`wfPartitions n`** — `partitions n` is a well-founded poset under the
  "refinement makes you smaller" order (new this round).
- **Universal property of `GroupPushout`** — case-by-case eliminator into any
  group given a coherent pair of homs.
- **Van Kampen back-direction** — `vanKampen-back f g : GroupHom (GroupPushout (pi_functor-hom f) (pi_functor-hom g)) (pi_group 0 (PushoutPointed f g))`, fully closed including its A-agreement coherence `pushoutVanKampen-coh` (new this round).

**Headline results not yet proved.**
- Bridge `dcommf2 ↔ commstr 2`, hence `SPnAxiom {2} A (SP2 A)`.
- Existence of any type satisfying `SPnAxiom` for general `n` (the
  partition-pushout in `SPn.ard`).
- The Seifert–van Kampen theorem `pi_group 0 (PushoutPointed f g) = GroupPushout (...) (...)`.

---

## 3. Recent rounds of work

### 3.1 May 2026 — `SetSP` and `Trunc0Eq` (earlier)

- **`Trunc0Eq` (`Utilities.ard`)**: `Trunc0 A = A` whenever `A : isSet`.
- **`setTruncNaiveSP2`**: `SetSP2 A = Trunc0 (NaiveSP2 A)`.
- **`setTruncSP2`**: `SetSP2 A = Trunc0 (borelXn 2 A)` for `A : \Set`.

### 3.2 May 2026 — `setSP2Inj.base` and the `setRecBS2` beta (this session, part 1)

The earlier proof of `setTruncSP2` shipped a standalone `borelToSetSP2` map
with bespoke equivalence-branch / coherence proofs. That map computes the
same value as `setSP2Inj` (the canonical `commstr 2 A (SetSP2 A)`), but it
was used because no beta rule for `setSP2Inj`'s underlying `setRecBS2`
existed.

This round added:

- **`setRecBS2.beta`** (`BSn.ard`): for any `X : BSn 2` and any chosen
  witness `x : X.1`, `setRecBS2 X f h = f x`. Proved via
  `TruncP.rec-set.level`-uniqueness on the manual `(b, inP (x, idp))`
  candidate.
- **`setSP2Inj.base`** (`SetSP.ard`): `setSP2Inj (BSnbase 2) f = inSP2 (f 0) (f 1)`,
  derived from the new beta plus `notFin2isNot 0 : notBS2 0 = 1`.
- **`setTruncSP2` refactor**: replaced every call of `borelToSetSP2` /
  `borelToSetSP2-base` with `setSP2Inj` / `setSP2Inj.base`. Net change:
  −54 lines, no regressions. Signature tightened from `{A : \Type}` to
  `{A : \Set}` (now required by `setRecBS2`); the only consumer
  (`setSP2IsSP2`) already used `{A : \Set}`.

### 3.3 May 2026 — `wfPartitions` and `GroupPushout` foundations (this session, part 2)

Two **stepping stones** that don't close major theorems on their own but
unblock substantial chunks of the remaining `SPn.ard` and `HomotopyGroup.ard`
work.

**SPn side:**

- **`partitionInto` tightened**: `idPart` now requires `0 < n` and `compPart`
  requires `0 < r1`. Degenerate "partitions" with zero-sized parts are
  forbidden, which restores the invariant `k ≤ n` for any partition of n
  into k parts.
- **`partitionInto_k<=n`**: proves `k ≤ n` by induction, supported by a small
  conversion lemma `<_to_<= : 0 < n → 1 <= n` (NatOrder constructor → Preorder
  encoding).
- **`monus-strict-monotone-right`**: `a ≤ n → b < a → n -' a < n -' b`.
- **`wfPartitions n`** is now a complete `WellFoundedPoset (partitions n)`:
  - `λ < μ := μ.1 < λ.1` (λ has strictly more parts than μ).
  - `potential λ := n -' λ.1`.
  - `<-irreflexive` / `<-transitive` directly from `NatSemiring`.
  - `potentialMonotone` from `monus-strict-monotone-right`.

  Refining a partition makes it strictly smaller in the order, with the
  maximally-refined partition (k = n, all 1s) at the bottom. This is exactly
  the order needed by `contrSpace`'s `WellFoundedPoset.elim` recursion.

**HomotopyGroup side:**

- **`GroupPushout.E` augmented**: added four missing HIT constructors —
  `gpinl-*`, `gpinl-ide`, `gpinr-*`, `gpinr-ide` — that force the carrier
  inclusions to be group homomorphisms. Without these, the original HIT
  presented the *free group on |B|+|C| with one extra relation*, not the
  categorical pushout `B *_A C` in Group.
- **`recE`**: the recursor on the 13-constructor HIT. Given any `G : Group`
  and a coherent pair of homs `h_B : B → G`, `h_C : C → G` (agreeing on `A`),
  returns the case-by-case map `E → G`. Each path constructor maps to the
  corresponding group-law path in `G`.
- **`recHom`**: wraps `recE` as a `GroupHom (GroupPushout f g) G`. The
  `func-*` equation holds by `idp` since the `*` constructor of `E` matches
  by definition.

  This is the *existence* half of the universal property. Uniqueness (every
  hom factoring through agrees with `recHom`) is not yet stated.

### 3.9 May 2026 — Van Kampen back-direction fully closed (this session)

The Tier 1.3 hole (`pushoutVanKampen-coh`) and its dependency chain are now
closed. The back-direction of van Kampen typechecks end-to-end.

**Closed goals (2):**

- **`pi_functor-hom-id`** at `n = 0` (T2): proved
  `pi_functor-hom {0} (id-pointed X) = GroupHom.id {pi_group 0 X}` via
  `exts (\lam e => \case \elim e \with { in0 loop => pmap in0 (idp_*> loop) })`.
  The case-elim on `Trunc0` exposes the underlying `Omega` element; the loop
  itself reduces to its identity-prefixed form via `idp_*>`. (The general-n
  version would need induction on n; restricted to n=0 since van Kampen only
  needs that.)

- **`loop-bridge`** (T1): closes the path-algebra residual inside
  `pushoutVanKampen-coh`. The proof factors into three pieces:

  1. **`pgrg-cancel`**: small abstract path-algebra helper —
     ```arend
     ((inv p1 *> p2) *> p3) *> (inv p3 *> q *> p3) *> inv p3 *> inv p2 *> p1
       = inv p1 *> (p2 *> q *> inv p2) *> p1
     ```
     proved by simultaneous `\elim p1, p2, p3 \| idp, idp, idp => idp`. All
     three path variables reduce to `idp` in one match; both sides collapse
     to `q`.

  2. **`rhs-to-canonical`**: rewrites the RHS of `loop-bridge` to canonical
     form via 8 `rewrite` steps (3× `pmap_inv-comm`, 2× `pmap_*>-comm`, 2×
     `*>_inv-comm`, 2× `inv_inv`) then a single `pgrg-cancel` application
     with the concrete paths `pmap pinl f.2`, `path (pglue A.base)`,
     `pmap pinr g.2`, `pmap pinr (pmap g.1 loop)`.

  3. **`loop-bridge`** body: 5 `pmap_*>-comm` / `pmap_inv-comm` chain steps
     distributing the LHS to canonical, then `inv (rhs-to-canonical f g loop)`
     to land on RHS.

  Key trick: bare partial-applied constructors (`pinr {A.E} {C.E} {B.E} {f.1} {g.1}`)
  rather than lambdas — `\lam b => pinr {...} b` doesn't unify with the bare
  form in the goal, so `rewrite` patterns require the bare-constructor shape.

**Project state:** 14 goals (SPn 10, HomotopyGroup 3, SPnAxioms 1) — down
from 16 at the start of the session. HomotopyGroup's remaining 3 goals are
all on the forward (encode-decode) side; the back-direction is complete.

### 3.8 May 2026 — HomotopyGroup Tier 1+3 (van Kampen scaffolding)

Built the back-direction half of van Kampen and refactored `pushoutVanKampen`
into 4 clearly-named pieces.

**Tier 1 (back direction):**
- **`pinl-pointed`, `pinr-pointed`**: pointed map inclusions
  `C/B ->* PushoutPointed f g`. The `pinr` pointedness threads through `g.2`,
  `inv (pglue A.base)`, and `f.2`.
- **`pi-pinl-hom`, `pi-pinr-hom`**: `pi_functor-hom` of the above, giving
  group homs `π₁(C)/π₁(B) → π₁(PushoutPointed f g)`.
- **`pushoutVanKampen-coh`** (Tier 1.3 — TODO `{?}`): A-agreement proved
  pointwise after destructuring `Trunc0`. The path between the inner loops
  is left as a hole pending the pi_functor-hom-pointed-htpy auxiliary.
- **`vanKampen-back`**: the back-direction `GroupHom GroupPushout → π₁(pushout)`,
  built via `GroupPushout.recHom` from the three above.

**Tier 3 (refactor):**
- **`vanKampen-forward`** (TODO `{?}`): the encode-decode side, multi-week.
- **`vanKampen-sec`, `vanKampen-ret`** (TODO `{?}`): iso section/retraction.
- **`vanKampen-iso`**: assembles forward + back + sec + ret into an
  `Iso {GroupCat}`.
- **`pushoutVanKampen` body**: now `Cat.isotoid {GroupCat} vanKampen-iso`,
  routing through arend-lib's group univalence.

**Net effect:** HomotopyGroup's goal count went from 1 (opaque) to 4 (named
and structured). The hard part — `vanKampen-forward` encode-decode — is now
isolated; everything else around it is mechanical scaffolding waiting for
that piece. Total project state: 15 goals across 3 modules (SPn 10,
HomotopyGroup 4, SPnAxioms 1).

### 3.7 May 2026 — `partitionSize=n` resolved + Arend quirk understood

The earlier "blocked" claim around `partitionSize=n` was a misdiagnosis. The
real rule (per user guidance + experimental verification):

> When a function `f` is defined by multi-pattern `\elim k, x` over an
> indexed data type, the reduction `f (C … rest) → body` does NOT fire in
> a downstream lemma if `rest` is a sub-component bound by destructuring an
> *outer* parameter. The lemma must `\elim` `rest` as a parameter itself.

The fix is mechanical: factor the computation step into a separate lemma
whose recursive arg is a parameter, then chain through it.

```arend
-- Computation rule, with rest as a parameter.
\lemma partitionSize-step ... (rest : partitionInto r2 k)
  : partitionSize (compPart r1 r2 _ _ rest) = r1 + partitionSize rest
  \elim k, rest
  | 1, idPart _ => idp
  | suc k, compPart _ _ _ _ _ => idp

-- Main induction chains through it.
\lemma partitionSize=n ... \elim k, lambda
  | suc k, compPart r1 r2 _ n_split rest =>
    partitionSize-step rest
    *> pmap (r1 Nat.+) (partitionSize=n rest)
    *> inv n_split
```

Documented in `~/.claude/skills/arend-quirks/SKILL.md` §3 (the "subtler
case" subsection). This unblocks the `powerPartition.extend` keystone for
SPn.

### 3.6 May 2026 — Tier 1 closest-reachable pass

Three concrete next-action items targeted; one closed cleanly, two
investigated and revealed deeper Arend limitations.

- **`Join.ard` retired (closed)**. The local `Join` module was migrated to
  arend-lib's `Homotopy.Join`. Only `Join_Contr` was used externally (in
  `SP2OfSet.ard`) — the rest of the local `Join.ard` (`joinEqLeft`,
  `joinContrSet`) was inlined into `SP2OfSet.ard` as local helpers, since
  arend-lib doesn't ship them. The encode-decode-related `joinEq`/`joinSet`
  defs (which carried the 2 open goals) were dropped — they had no external
  consumers. Net: −129 lines, project-wide goal count drops from 14 to 12.

- **`partitionSize=n` (resolved)**. Initially diagnosed as an Arend reducer
  limitation; further investigation revealed the actual rule: for `f (C …
  rest)` to reduce inside a lemma, the lemma must `\elim` `rest` as a
  parameter (not just destructure it as part of an outer `\elim`). The fix
  is to factor the reduction step into a separate `partitionSize-step`
  lemma that takes `rest : partitionInto r2 k` and uses `\elim k, rest`;
  the main induction proof then chains through it. Documented in
  `arend-quirks` §3.

- **`liftSP2-fromSet.uniqDcommf` (blocked on levels)**. The level-inference
  chain `liftSP2-fromSet → liftSP2 → dcommf2 → injSP2/fromCommstrSet`
  introduces level constraints (`0 <= \lh`, `??h1` between `dcommf2`'s
  `p1` and `p2`) that Arend's solver doesn't resolve, even with explicit
  `\plevels p1 <= p2` and `\levels (p1, p2) \lh` annotations. Reverted;
  needs a deeper engagement with Arend's level system.

### 3.5 May 2026 — low-hanging fruit pass

Four small adds that close concrete next-action items from §4 without
touching the hard cores (`pushoutVanKampen`, `powerPartition.extend`,
contractibility of `contrSpace`).

- **`SPnAxiomSet`** (`SPnAxioms.ard`): set-restricted variant of `SPnAxiom`
  (T : Set instead of oo-Type). Plus the trivial implication `SPnAxiom →
  SPnAxiomSet`. Useful as a target for the `commstr 2 → dcommf2` bridge,
  which is set-canonical but not general.
- **`gpinlHom` / `gpinrHom` / `gpglue-comm`** (`HomotopyGroup.ard`):
  `gpinl` and `gpinr` wrapped as `GroupHom B/C → GroupPushout f g`, using
  the new HIT constructors for `func-*` and `func-ide`. `gpglue-comm`
  packages the gpglue path as `gpinlHom (f a) = gpinrHom (g a)`.
- **`partitionSize`** (`SPn.ard`): recursive sum of parts of a partition.
  Companion lemma `partitionSize=n` *resolved* in §3.7 below.
- **`liftSP2-fromSet.uniqDcommf`** attempted but reverted: the
  level-inference chain between `dcommf2`'s `\plevels` and `injSP2`'s
  implicits needs a careful annotation pass that's beyond a low-hanging fruit.

### 3.4 May 2026 — `commstr 2 → dcommf2` bridge for sets (this session, part 3)

Closing the §4.5 next-action partially: when `T` is a set, the dcommf2
coherence path is unique (set-pi), so it can be picked canonically without
extra data.

- **`dcommf2.fromCommstrSet`** (`OrbitSP2.ard`): for any `f : commstr 2 A T`
  with `T : \Set`, produces `dcommf2 A T`. Uses `recPropBSn` with the
  predicate `f (BSnbase 2) c = f Y c` (a Prop because `T` is a set).
- **`dcommf2.fromCommstrSet.base`**: the coherence path is definitionally
  `idp` at the basepoint — the beta rule for the recPropBSn-based
  construction.
- **`liftSP2-fromSet`**: combines `fromCommstrSet` with `liftSP2`, exposing
  a clean `SP2 A → T` constructor for set-valued targets that takes only a
  `commstr 2`. Beta `liftSP2-fromSet g (injSP2.1 X x) = g X x` holds by `idp`
  via `liftSP2.coh`.

What's **still missing** to close §4.5:

1. The full bridge for **general `T : \Type`** (not just sets): for non-set
   targets the dcommf2 path is genuinely additional data, so any "bridge"
   must restrict the universal-property statement. One reasonable route is
   a *set-restricted* `SPnAxiom` variant.
2. **Uniqueness** of `liftSP2-fromSet g` against the SPnAxiom-shaped
   constraint (only the basepoint compatibility `h (sigma (BSnbase 2, x)) = g (BSnbase 2) x`).
   The `liftSP2.uniqExt` lemma asks for the strictly stronger
   `dcommf2.compose injSP2 h = fromCommstrSet g`. The level inference for
   stitching these together is fiddly (initial attempt hit level-equation
   solving errors at `\lh`) — solvable but it would need a careful pass.

---

## 4. Open goals and next actions

**Current state: 14 open `{?}` goals across 3 modules** (SPn 10,
HomotopyGroup 3, SPnAxioms 1).

### 4.1 `SPn.ard` (10 goals) — partition-pushout construction

With `wfPartitions` AND `partitionSize=n` closed, the remaining holes form
a coherent chain:

```
powerPartition.extend            (line 89)   ← keystone, now reachable
partExtensionsType               (line 105)
partExtension                    (line 107)
classTypeExtension               (line 111)
iOnExtension                     (line 137)
SP-step                          (line 158)  ← partial; uses contrF / contrG
contrF                           (line 167)
contrG                           (line 175)
pointInclusion                   (line 181)  ← propagated from contrF
contrInclusion                   (line 185)  ← lambda.1 < n precondition (~30 min fix)
```

**Recommended next action**: prove `powerPartition.extend`.
With `partitionSize=n` in hand, the construction is now genuinely
achievable: assemble the underlying set as
`\Sigma (m : Nat) (\Sigma (lab : (p.1 m).1) ((p.2 m lab).1.1))`, then
prove `TruncP (Equiv {Y.1} {Fin n})` by induction on `partitionInto`,
threading through `partitionSize=n` to track cardinality. The X-coloring
is `(p.2 m lab).2`. ~1 day.

After `extend`, the next 4 holes (`partExtensionsType` / `partExtension` /
`classTypeExtension` / `iOnExtension`) are combinatorial bookkeeping that
should each land in ~2–3 days (~1 week total). `contrInclusion`'s
`lambda.1 < n` precondition is a 30-minute fix (just add it as an extra
parameter, derive at the call sites via `partitionInto_k<=n`).

The harder pieces — `contrSpace` contractibility, `contrF`/`contrG`, and
the actual `SPnAxiom`-satisfaction proof — remain multi-day to multi-week
items.

After `extend` is closed, `partExtensionsType` / `partExtension` /
`classTypeExtension` are routine bookkeeping (~1 week total). Then
`contrSpace`'s contractibility — the hardest piece — is the real obstacle
(~1–2 weeks). Finally, the actual `SPnAxiom`-satisfaction proof is its own
multi-week project not yet stated in the file.

### 4.2 `HomotopyGroup.ard` (3 goals) — forward direction of van Kampen

The back-direction of `pushoutVanKampen` is now fully proved end-to-end:
`vanKampen-back` consumes `pi-pinl-hom`, `pi-pinr-hom`, and
`pushoutVanKampen-coh` (closed via `loop-bridge` → `rhs-to-canonical` →
`pgrg-cancel`) through `GroupPushout.recHom`. The three remaining goals are
all on the **forward / encode-decode** side:

```
vanKampen-forward  : GroupHom (pi_group 0 (PushoutPointed f g))
                              (GroupPushout (pi_functor-hom f) (pi_functor-hom g))
vanKampen-sec      : vanKampen-back ∘ vanKampen-forward = id
vanKampen-ret      : vanKampen-forward ∘ vanKampen-back = id
```

`vanKampen-forward` is the keystone — the other two follow once the forward
map is concrete enough to compute against.

The mathematical content of `vanKampen-forward`: given a loop
`p : Trunc0 (pinl C.base = pinl C.base)` in `PushoutPointed f g`, decode it
into an alternating word in `pi_1(B)` and `pi_1(C)` connected by `gpglue`
transitions. This is the encode-decode argument for the pushout HIT:
either build a "code" type fibered over `PushoutData f g` whose total space
is contractible (Licata-Brunerie style), or work with the explicit free
product structure of `GroupPushout` and decompose paths.

**Recommended next actions** (in increasing difficulty):

1. **`π_1(S^1) = ℤ`** as a warmup (encode-decode on a single HIT) — ~1 week.
2. **Special case of van Kampen with `A` contractible**: reduces to
   `π_1(B ∨ C) = π_1(B) * π_1(C)`. Lets you debug the encode-decode argument
   without the `gpglue` complication. ~1–2 weeks.
3. **Full `vanKampen-forward`**: encode-decode of `paths in PushoutData`
   against the carrier of `GroupPushout`, then promotion through `Trunc0`
   and group univalence. ~3–5 weeks. `vanKampen-sec`/`vanKampen-ret` follow
   directly afterward (~1–2 weeks each).

(1) and (2) are independently valuable mathematics and should land in
arend-lib eventually.

**Auxiliary lemma that may be needed:**
`pi_functor-hom-comp` and `pi_functor-hom-pointed-htpy` are still unproved
(currently not stated; `pi_functor-hom-id` is proved at n=0 only). These
become relevant for proving `vanKampen-sec` and `vanKampen-ret` where one
needs to identify `pi_functor-hom (id-pointed _) = GroupHom.id` along a
non-trivial pointed-homotopy chain.

### 4.3 `SPnAxioms.ard` (1 goal) — connectedness preservation

`isConnectedSPnX` (line 53) is stuck on what the author labeled "axiom of
choice through Π over a non-set". The proof uses `connectedLem` (a
`Bool`-valued classifier argument) which requires picking a coherent witness
on each fiber.

**Recommended next action**: replace `connectedLem` with a direct
connectedness argument on the `Borel`-style cofibers. Specifically, show
that `SPX` inherits connectedness from `borelXn n X` directly via the
pushout structure of any `SPnAxiom`-witnessing model, rather than going
through `Bool` classifiers. This is ~1 week of HoTT work, mostly independent
of the rest of the project.

### 4.4 ~~`Join.ard`~~ (closed §3.6)

Migrated to arend-lib's `Homotopy.Join` (see §3.6). The two locally-needed
helpers (`joinEqLeft`, `joinContrSet`) were inlined into `SP2OfSet.ard`;
the broken encode-decode lemmas were dropped along with the module.

### 4.5 Bridging `dcommf2 ↔ commstr 2`

**Partial progress, this session.** `dcommf2.fromCommstrSet` and
`liftSP2-fromSet` now exist for **set-valued T**; see §3.4.

What remains:

- **General-T bridge**: for `T : \oo-Type` (non-set), the dcommf2 coherence
  is genuine extra data and cannot be canonically picked. The right move is
  probably to *restrict* `SPnAxiom`'s `T : \oo-Type` to `T : \Set` (giving a
  set-truncated SPnAxiom variant) — then `SP2 A` satisfies it canonically
  via the existing bridge.
- **Uniqueness** for `liftSP2-fromSet`. The level-inference issues blocked
  the initial attempt; resolution likely involves explicit `\levels`
  annotations on `dcommf2`-typed expressions.

Estimated remaining effort: 2–4 days for the set-restricted axiom statement
+ uniqueness; harder if the general-T story is pursued.

---

## 5. File-by-file size

```
AlternativeCommf.ard   49 lines
BSn.ard               467 lines
Borel.ard             120 lines
Commutative.ard        54 lines
HomotopyGroup.ard     169 lines (+58 across this session)
LEMConnectedness.ard   35 lines
OrbitSP2.ard          164 lines (+33)
PushoutSP3.ard         84 lines
SP2OfBool.ard         383 lines
SP2OfSet.ard          377 lines (+22 from Join migration)
SPn.ard               192 lines (+58)
SPnAxioms.ard         137 lines (+17)
SPnInductiveWrong.ard  36 lines
SetSP.ard             169 lines (-46 from Join migration)
Utilities.ard         520 lines
```

Total: ~2950 lines (down from ~3260 — Join.ard's 129 lines gone, the rest
of the project gained ≈200 lines across this session of stepping stones).
Roughly **170 lines is unfinished scaffolding** (the remaining 10
partition-pushout `{?}`s in `SPn.ard`).
