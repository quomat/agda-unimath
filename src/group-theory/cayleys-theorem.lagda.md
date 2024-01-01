# Cayley's theorem

```agda
module group-theory.cayleys-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-extensionality
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import group-theory.embeddings-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

## Theorem

### Direct proof of Cayley's theorem

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem = {!!}

  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem = {!!}

  hom-Cayleys-theorem : hom-Group G (symmetric-Group (set-Group G))
  pr1 hom-Cayleys-theorem = {!!}

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p = {!!}

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem = {!!}

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  pr1 Cayleys-theorem = {!!}
```

### Cayley's theorem as a corollary of the Yoneda lemma

This is Corollary 2.2.10 of _Category theory in context_, and remains to be
formalized.

## References

1. Emily Riehl, _Category Theory in Context_, 2016
   ([PDF](https://math.jhu.edu/~eriehl/context.pdf))

## External links

- [Cayley's Theorem](https://1lab.dev/Algebra.Group.Cayley.html) at 1lab
- [Cayley's theorem](https://ncatlab.org/nlab/show/Cayley%27s+theorem) at $n$Lab
- [Cayley's theorem](https://en.wikipedia.org/wiki/Cayley%27s_theorem) at
  Wikipedia
- [Cayley's theorem](https://www.wikidata.org/wiki/Q179208) at Wikidata
