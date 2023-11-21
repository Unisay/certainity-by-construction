module Chapter2 where

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat 
    using (ℕ; zero; suc)

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three

  open import Chapter1 using (Bool; true; false)

  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false

  module Sandbox-Usable where
    postulate 
      Usable : Set
      Unusable : Set
    
    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)
 
  data IsOdd : ℕ → Set where
    one-odd : IsOdd one
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  data IsOdd′ : ℕ → Set where
    is-odd : {n : ℕ} → IsEven n → IsOdd′ (suc n)

  oddSuccEven : {n : ℕ} → IsEven n → IsOdd (suc n)
  oddSuccEven zero-even = one-odd
  oddSuccEven (suc-suc-even even) = suc-suc-odd (oddSuccEven even)

  evenSucOdd : {n : ℕ} → IsOdd n → IsEven (suc n)
  evenSucOdd one-odd = suc-suc-even zero-even 
  evenSucOdd (suc-suc-odd odd) = suc-suc-even (evenSucOdd odd)

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | nothing = nothing
  ... | just x = just (suc-suc-even x)
