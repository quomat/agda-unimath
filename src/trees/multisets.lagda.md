# Multisets

```agda
module trees.multisets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.w-types
```

</details>

## Idea

The type of **multisets** of universe level `l` is the W-type of the universal
family over the universe `UU l`.

## Definitions

### The type of small multisets

```agda
𝕍 : (l : Level) → UU (lsuc l)
𝕍 l = {!!}
```

### The large type of all multisets

```agda
data
  Large-𝕍 : UUω
  where
  tree-Large-𝕍 : {l : Level} (X : UU l) → (X → Large-𝕍) → Large-𝕍
```

### The elementhood relation on multisets

```agda
infix 6 _∈-𝕍_ _∉-𝕍_

_∈-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∈-𝕍 Y = {!!}

_∉-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∉-𝕍 Y = {!!}
```

### Comprehension for multisets

```agda
comprehension-𝕍 :
  {l : Level} (X : 𝕍 l) (P : shape-𝕎 X → UU l) → 𝕍 l
comprehension-𝕍 = {!!}
```
