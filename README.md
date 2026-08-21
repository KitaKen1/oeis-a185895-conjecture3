# OEIS A185895 `conjecture3`: Gauss congruence in Lean

This repository gives an admission-free Lean proof of the exact Formal Conjectures target
[`OeisA185895.conjecture3`](https://github.com/google-deepmind/formal-conjectures/blob/e13dd7284e72012a1616806d09cb6b8025e387af/FormalConjectures/OEIS/185895.lean#L121-L129).

Try it in Lean4Web: [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Foeis-a185895-conjecture3%2Frefs%2Fheads%2Fmain%2Flean4web%2FOeisA185895Conjecture3Lean4Web.lean)

> **Status:** both local proof files build with Lean `v4.27.0`. The main theorem uses only
> `propext`, `Classical.choice`, and `Quot.sound`; it has no admission or custom axiom. The
> upstream declaration remains `research open` until a solve PR is reviewed and merged.

## Formal Conjectures target

```lean
theorem conjecture3_solved (p : ℕ) (hp : p.Prime) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    OeisA185895.a (n * p ^ k) ≡
      OeisA185895.a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]
```

The Formal Conjectures version imports the pinned definition of `OeisA185895.a`. It does not
use the admitted upstream theorem `OeisA185895.conjecture3`.

## Mathematical Explanation (AI generated)

For a finite set `s` of distinct positive block sizes, write

```text
M(s) = (sum s)! / product (j in s) j!.
```

Expanding the defining polynomial and removing the integer `floor` proves

```text
a(N) = sum_{s ⊆ {1,...,N}, sum s = N} (-1)^|s| M(s).
```

The congruence is then proved coefficientwise in a multivariate polynomial ring over
`ZMod (p^k)`. If `p^k ∣ p m`, the formalized freshman's-dream calculation gives

```text
(sum X_i)^(p m) = expand_p ((sum X_i)^m).
```

Taking a monomial coefficient shows:

- if every multiplicity is divisible by `p`, its multinomial coefficient reduces to the
  divided multiplicities;
- otherwise that multinomial coefficient is `0` modulo `p^k`.

The remaining terms are reindexed by the bijection `s ↔ p·s`. Cardinality, hence the sign
`(-1)^|s|`, is preserved. Setting `m = n p^(k-1)` proves the target.

This is an algebraic formalization of the same prime-power Gauss/Dold mechanism; the proof does
not require an unformalized appeal to cyclic orbits.

## Files

| Directory | Purpose |
|---|---|
| `lean/` | Imports Formal Conjectures at commit `e13dd728...` and proves the exact target |
| `lean4web/` | Mathlib-only standalone copy of the definitions and the same proof |

Each directory has its own `lakefile.toml`, `lean-toolchain`, and pinned
`lake-manifest.json`.

## Build

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

The end of each Lean file contains `#print axioms conjecture3_solved`. The expected result is:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

This artifact solves only the mathematical statement of `OeisA185895.conjecture3`.

- `conjecture1` and `conjecture2` are separate sign-change conjectures and remain open.
- A007837 is the unsigned companion, but it is not currently a Formal Conjectures target.
- Local kernel verification is distinct from an upstream status change; that requires review and
  merge by the Formal Conjectures maintainers.

## Sources

- [Formal Conjectures: `OEIS/185895.lean`](https://github.com/google-deepmind/formal-conjectures/blob/e13dd7284e72012a1616806d09cb6b8025e387af/FormalConjectures/OEIS/185895.lean)
- [OEIS A185895](https://oeis.org/A185895)
- [OEIS A007837](https://oeis.org/A007837)
- [Gossow, *Polynomial and combinatorial analogues of Gauss congruence*](https://arxiv.org/abs/2410.05678)

## AI usage disclosure

The proof and repository were developed with assistance from OpenAI Codex.
