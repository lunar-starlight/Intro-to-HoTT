```agda
{-# OPTIONS --allow-unsolved-metas #-}
module 04-InductiveTypes where

open import Level using (_⊔_; Level) renaming (suc to lsuc)
open import Function.Base using (_∘_; id; _|>_)

open import 00-Common
open import 03-Naturals using (ℕ; zero; succ; succ²; one) renaming (ind to ℕ-ind; _+_ to _+ℕ_)


private
  variable
    o ℓ m n : Level
```

# Unit type

```agda
data 𝟙 : Set where
  * : 𝟙

𝟙-ind : {P  : 𝟙 → Set o}
      → (p* : P *)
      → ((x : 𝟙) → P x)
𝟙-ind p* * = p*

pt : {A : Set o}
   → (a : A)
   → (𝟙 → A)
pt = 𝟙-ind
```

# Empty type

```agda
data 𝟘 : Set where

𝟘-ind : {P  : 𝟘 → Set o}
      → ((x : 𝟘) → P x)
𝟘-ind ()

ex-falso : {P : Set o}
         → (𝟘 → P)
ex-falso = 𝟘-ind
```

## Negation
```agda
¬_ : Set o → Set o
¬ A = A → 𝟘

is-empty : Set o → Set o
is-empty A = A → 𝟘

prop434 : {P : Set o} {Q : Set ℓ} → (P → Q) → (¬ Q → ¬ P)
prop434 f nq p = p |> f |> nq
```

# Coproducts

```agda
data _+_ (A : Set o) (B : Set ℓ) : Set (o ⊔ ℓ) where
  inl : A → A + B
  inr : B → A + B

+-ind : {A : Set o} {B : Set ℓ}
      → {P  : A + B → Set m}
      → (pₗ : (a : A) → P (inl a))
      → (pᵣ : (b : B) → P (inr b))
      → ((z : A + B) → P z)
+-ind pₗ pᵣ (inl a) = pₗ a
+-ind pₗ pᵣ (inr b) = pᵣ b
```

# Integers

```agda
ℤ : Set
ℤ = ℕ + (𝟙 + ℕ)
in-pos : ℕ → ℤ
in-zer : 𝟙 → ℤ
in-neg : ℕ → ℤ
in-pos = inr ∘ inr
in-zer = inr ∘ inl
in-neg = inl
-1ℤ = in-neg zero
0ℤ = in-zer *
1ℤ = in-pos zero

ℤ-ind : {P   : ℤ → Set o}
      → (p₀  : P  0ℤ)
      → (p₁  : P  1ℤ)
      → (p₋₁ : P -1ℤ)
      → (pₛ  : (n : ℕ) → P (in-pos n) → P (in-pos (succ n)))
      → (p₋ₛ : (n : ℕ) → P (in-neg n) → P (in-neg (succ n)))
      → ((k : ℤ) → P k)
ℤ-ind p₀ p₁ p₋₁ pₛ p₋ₛ (inl n)       = ℕ-ind p₋₁ p₋ₛ n
ℤ-ind p₀ p₁ p₋₁ pₛ p₋ₛ (inr (inl *)) = p₀
ℤ-ind p₀ p₁ p₋₁ pₛ p₋ₛ (inr (inr n)) = ℕ-ind p₁  pₛ  n

succℤ : ℤ → ℤ
succℤ = ℤ-ind 1ℤ (in-pos one) 0ℤ (λ n _ → in-pos (succ² n)) (λ n _ → in-neg n)
```

# Dependent pair type

```agda
data Σ (A : Set ℓ) (B : A → Set o) : Set (ℓ ⊔ o) where
  _,_ : (x : A) → B x → Σ A B

infixr 4 _,_
infix 2 Σ-syntax

Σ-syntax : (A : Set o) → (A → Set ℓ) → Set (o ⊔ ℓ)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

module _ {A : Set m} {B : A → Set n} where 
  Σ-ind : {P  : Σ A B → Set o}
        → (pₚ : (a : A) → (b : B a) → P (a , b))
        → ((z : Σ A B) → P z)
  Σ-ind pₚ (a , b) = pₚ a b

  pr₁ : Σ A B → A
  pr₁ = Σ-ind (λ a _ → a)

  pr₂ : (z : Σ A B) → B (pr₁ z)
  pr₂ = Σ-ind (λ _ b → b)

  ev-pair : {P  : Σ A B → Set o}
          → ((z : Σ A B) → P z)
          → ((a : A) → (b : B a) → P (a , b))
  ev-pair p a b = p (a , b)
```

## Product type
```agda
_×_ : (A : Set o) → (B : Set ℓ) → Set (o ⊔ ℓ)
A × B = Σ A (λ _ → B)

×-ind : {A : Set o} → {B : Set ℓ}
      → {P  : A × B → Set m}
      → (pₚ : (a : A) → (b : B) → P (a , b))
      → ((z : A × B) → P z)
×-ind = Σ-ind
```

# Exercises

## 4.1 Integer operations
### (a) Integer predecessor
```agda
predℤ : ℤ → ℤ
predℤ = {!   !}
```
### (b) Integer addition and negation
```agda
_+ℤ_ : Bin ℤ
_+ℤ_ = {!   !}

-ℤ_ : ℤ → ℤ
-ℤ_ = {!   !}
```
### (c) Integer multiplication
```agda
_⋅ℤ_ : Bin ℤ
_⋅ℤ_ = {!   !}
```

## 4.2 Boolean operations
```agda
data bool : Set where
  false : bool
  true  : bool

bool-ind : {P  : bool → Set o}
         → (p⊥ : P false)
         → (p⊤ : P true)
         → ((b : bool) → P b)
bool-ind p⊥ p⊤ false = p⊥
bool-ind p⊥ p⊤ true  = p⊤
```
### (a) Boolean negation
```agda
¬₂ : bool → bool
¬₂ = {!   !}
```
### (b) Boolean conjunction
```agda
_∧_ : Bin bool
_∧_ = {!   !}
```
### (c) Boolean disjunction
```agda
_∨_ : Bin bool
_∨_ = {!   !}
```

## 4.3 FOL
```agda
_↔_ : (P : Set m) → (Q : Set n) → Set (m ⊔ n)
P ↔ Q = (P → Q) × (Q → P)
```
### (a) Noncontradiction
(i)
```agda
module _ {P : Set m}where
  non-contra : ¬ (P × (¬ P))
  non-contra = {!   !}
```
(ii)
```agda
  non-contra₂ : ¬ (P ↔ (¬ P))
  non-contra₂ = {!   !}
```
### (b) Double negation monad
(i) Unit law
```agda
  ¬¬-unit : P → ¬ ¬ P
  ¬¬-unit = {!   !}
```
(ii) Functoriality
```agda
module _ {P : Set m} {Q : Set n} where
  ¬¬-functor : (P → Q) → (¬ ¬ P → ¬ ¬ Q)
  ¬¬-functor = {!   !}
```
(iii) Bind
```agda
  ¬¬-bind : (P → ¬ ¬ Q) → (¬ ¬ P → ¬ ¬ Q)
  ¬¬-bind = {!   !}
```
### (c) Double negation is the monad of classical computation
(i) Double negation elimination
```agda
module _ {P : Set m} where
  ¬¬|¬¬-elim : ¬ ¬ (¬ ¬ P → P)
  ¬¬|¬¬-elim = {!   !}
```
(ii) Pierce's law
```agda
module _ {P : Set m} {Q : Set n} where
  ¬¬|pierce : ¬ ¬ (((P → Q) → P) → P)
  ¬¬|pierce = {!   !}
```
(iii)
```agda
  ¬¬|coimplication : ¬ ¬ ((P → Q) + (Q → P))
  ¬¬|coimplication = {!   !}
```
(iv) LEM
```agda
module _ {P : Set m} where
  ¬¬|LEM : ¬ ¬ (P + (¬ P))
  ¬¬|LEM = {!   !}
```
### (d)
(i)
```agda
  LEM→¬¬elim : (P + (¬ P)) → (¬ ¬ P → P)
  LEM→¬¬elim = {!   !}
```
(ii)
```agda
module _ {P : Set m} {Q : Set n} where
  ¬¬impl↔LEM→impl : (¬ ¬ (P → Q)) ↔ ((P + (¬ P)) → (P → Q))
  ¬¬impl↔LEM→impl = {!   !}
```
### (e) Double negation stable propositions
(i)
```agda
module _ {P : Set m} where
  ¬¬¬→¬ : ¬ ¬ ¬ P → ¬ P
  ¬¬¬→¬ = {!   !}
```
(ii)
```agda
module _ {P : Set m} {Q : Set n} where
  ¬¬-elim-negated-antecedent : ¬ ¬ (P → ¬ Q) → (P → ¬ Q)
  ¬¬-elim-negated-antecedent = {!   !}
```
(iii)
```agda
  ¬¬-elim-¬¬-product : ¬ ¬ ((¬ ¬ P) × (¬ ¬ Q)) → ((¬ ¬ P) × (¬ ¬ Q))
  ¬¬-elim-¬¬-product = {!   !}
```
### (f)
(i)
```agda
  demorgan₁² : (¬ ¬ (P × Q)) ↔ ((¬ ¬ P) × (¬ ¬ Q))
  demorgan₁² = {!   !}
```
(ii)
```agda
  ¬|demorgan₂ : (¬ ¬ (P + Q)) ↔ (¬ ((¬ P) × (¬ Q)))
  ¬|demorgan₂ = {!   !}
```
(iii)
```agda
  contrapositive² : (¬ ¬ (P → Q)) ↔ (¬ ¬ P → ¬ ¬ Q)
  contrapositive² = {!   !}
```

## 4.4 Lists
```agda
data list (A : Set o) : Set o where
  nil  : list A
  cons : A → list A → list A
```
### (a) Induction principle
```agda
list-ind : {!   !}
list-ind = {!   !}
```
### (b) Fold
```agda
list-fold : {A : Set o} {B : Set ℓ}
          → B → (μ : A → B → B) → list A → B
list-fold b μ = {!   !}
```
### (c) Map
```agda
list-map : {A : Set o} {B : Set ℓ}
         → (A → B) → list A → list B
list-map = {!   !}
```
### (d) Length
```agda
list-len : {A : Set o} → list A → ℕ
list-len = {!   !}
```
### (e) Sums and Products
```agda
list-sum : list ℕ → ℕ
list-sum = {!   !}
list-product : list ℕ → ℕ
list-product = {!   !}
```
### (f) Concat
```agda
list-concat : {A : Set o} → list A → list A → list A
list-concat = {!   !}
```
### (g) Flatten
```agda
list-flatten : {A : Set o} → list (list A) → list A
list-flatten = {!   !}
```
### (h) Reverse
```agda
list-reverse : {A : Set o} → list A → list A
list-reverse = {!   !}
```
