```agda
{-# OPTIONS --allow-unsolved-metas #-}
module 03-Naturals where

open import Level using (_⊔_; Level) renaming (suc to lsuc)
open import Function.Base using (_∘_; id)

open import 00-Common

private
  variable
    o : Level
```

# Definition of natural numbers

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
one : ℕ
one = succ zero
succ² : ℕ → ℕ
succ² = succ ∘ succ
-- For converting nat literals (0, 1, 2…) to elements of ℕ
-- {-# BUILTIN NATURAL ℕ #-}

-- Need this for builtin lists etc
-- open import Agda.Builtin.Nat using (Nat)

-- toℕ : Nat → ℕ
-- toℕ Agda.Builtin.Nat.zero = zero
-- toℕ (Agda.Builtin.Nat.suc n) = succ (toℕ n)

-- toNat : ℕ → Nat
-- toNat zero = Agda.Builtin.Nat.zero
-- toNat (succ n) = Agda.Builtin.Nat.suc (toNat n)
-- {-# BUILTIN FROMNAT toℕ #-}
```

## Induction principle
```agda
ind : {P  : ℕ → Set o}
    → (p₀ : P zero)
    → (pₛ : (n : ℕ) → P n → P (succ n))
    → ((n : ℕ) → P n)
ind         p₀ pₛ zero = p₀
ind {o} {P} p₀ pₛ (succ n) = ind {o} {P ∘ succ} (pₛ zero p₀) (pₛ ∘ succ) n
```

## Addition
```agda
_+_ : Bin ℕ
_+_ m = ind m (λ _ m+n → succ m+n)
```

# Exercises

## 3.1
### (a) Multiplication
```agda
_⋅_ : Bin ℕ
_⋅_ = {!   !}
```
### (b) Exponentiation
```agda
_^_ : Bin ℕ
_^_ = {!   !}
```

## 3.2
```agda
_∧_ : Bin ℕ
_∨_ : Bin ℕ
_∧_ = {!   !}
_∨_ = {!   !}
```

## 3.3
### (a) Triangular numbers
```agda
tri : ℕ → ℕ
tri = {!   !}
```
### (b) Factorial
```agda
fact : ℕ → ℕ
fact = {!   !}
```

## 3.4 Binomial
Binomial symbol with bin k n meaning "chose k from n".
```agda
bin : Bin ℕ
bin = {!   !}
```

## 3.5 Fibonacci
This uses the two-step induction principle, which I couldn't prove using regular induction.
```agda
ind₂ : {P  : ℕ → Set o}
     → (p₀ : P zero)
     → (p₁ : P one)
     → (pₛ : (n : ℕ) → P n → P (succ n) → P (succ² n))
     → ((n : ℕ) → P n)
ind₂ {o} {Q} p₀ p₁ pₛ = {!   !}

fib : ℕ → ℕ
fib = {!   !}

-- This tests the function above on a few values if you normalize `fibl`
-- -- 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ []
-- fib' = toNat ∘ fib
-- open import Data.List using (List; []; _∷_)
-- fibl : List Nat
-- fibl = fib' 0 ∷ fib' 1 ∷ fib' 2 ∷ fib' 3 ∷ fib' 4 ∷ fib' 5 ∷ fib' 6 ∷ fib' 7 ∷ fib' 8 ∷ fib' 9 ∷ []
```

## 3.6 Division by two
```agda
div₂ : ℕ → ℕ
div₂ = {!   !}
```

