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

```agda
pred : ℕ → ℕ
pred = ind zero λ n _ → n
```

```agda
_-_ : Bin ℕ
_-_ m = ind m (λ _ m-n → pred m-n)
```

# Exercises

## 3.1
### (a) Multiplication
```agda
_⋅_ : Bin ℕ
_⋅_ m = ind zero (λ n m⋅n → m⋅n + m)
```
### (b) Exponentiation
```agda
_^_ : Bin ℕ
_^_ m = ind one (λ n m^n → m^n ⋅ m)
```
## 3.2
```agda
_∧_ : Bin ℕ
_∨_ : Bin ℕ
_∧_ = ind (λ _ → zero) (λ _ m∧ → ind  zero    (λ n _ → succ (m∧ n)))
_∨_ = ind (λ n →    n) (λ m m∨ → ind (succ m) (λ n _ → succ (m∨ n)))
```

## 3.3
### (a) Triangular numbers
```agda
tri : ℕ → ℕ
tri = ind zero (λ n triₙ → succ n + triₙ)
```
### (b) Factorial
```agda
fact : ℕ → ℕ
fact = ind one (λ n factₙ → succ n ⋅ factₙ)
```

## 3.4 Binomial
Binomial symbol with bin k n meaning "chose k from n".
```agda
bin : Bin ℕ
bin = ind (λ _ → one) (λ _ binₖ → ind zero (λ n x → binₖ n + x))
```

## 3.5 Fibonacci
This uses the two-step induction principle, which I couldn't prove using regular induction.
```agda
ind₂ : {P  : ℕ → Set o}
     → (p₀ : P zero)
     → (p₁ : P one)
     → (pₛ : (n : ℕ) → P n → P (succ n) → P (succ² n))
     → ((n : ℕ) → P n)
-- ind₂ {o} {Q} p₀ p₁ pₛ = ind p₀ (λ n → ind {P = λ n → Q n → Q (succ n)} (λ _ → p₁) (λ m f x → {!   !}) {!   !})
ind₂         p₀ p₁ pₛ zero = p₀
ind₂         p₀ p₁ pₛ (succ zero) = p₁
ind₂ {o} {P} p₀ p₁ pₛ (succ (succ n)) = ind₂ p₁ (pₛ zero p₀ p₁) (λ n → pₛ (succ n)) (succ n)

-- {-# TERMINATING #-}
fib : ℕ → ℕ
fib = ind₂ zero one (λ _ fibₙ fibₛₙ → fibₛₙ + fibₙ)
-- fib = ind one (ind (λ _ → one) (λ n f x → f n + fib n))

-- -- 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ []
-- -- 0 ∷ 1 ∷ 2 ∷ 4 ∷ 8 ∷ 15 ∷ 26 ∷ 42 ∷ 64 ∷ 93 ∷ []
-- -- 0 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 5 ∷ 11 ∷ 21 ∷ 36 ∷ 57 ∷ []
-- fib' = toNat ∘ fib
-- open import Data.List using (List; []; _∷_)
-- fibl : List Nat
-- fibl = fib' 0 ∷ fib' 1 ∷ fib' 2 ∷ fib' 3 ∷ fib' 4 ∷ fib' 5 ∷ fib' 6 ∷ fib' 7 ∷ fib' 8 ∷ fib' 9 ∷ []
```

## 3.6 Division by two
```agda
-- {-# TERMINATING #-}
div₂ : ℕ → ℕ
div₂ = ind₂ zero zero (λ _ div₂n _ → succ div₂n)
-- div₂ = ind zero (ind (λ _ → zero) (λ n f x → {!   !}))
```

