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

  five : ℕ
  five = suc four

  six : ℕ
  six = suc five

  seven : ℕ
  seven = suc six

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

  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = a + suc b

  infixl 6 _+_

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ : two + three ≡ five
  _ = refl

  _ : four + three ≡ seven
  _ = refl

  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = b + (a * b)

  infixl 7 _*_

  _ : two * three ≡ six
  _ = refl

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = one
  a ^ suc b = a * (a ^ b)

  infixr 8 _^_

  _ : two ^ two ≡ four
  _ = refl

  _∸_ : ℕ → ℕ → ℕ
  a ∸ zero = a
  zero ∸ suc a = zero
  suc a ∸ suc b = a ∸ b

  _ : three ∸ two ≡ one
  _ = refl

  _ : three ∸ five ≡ zero
  _ = refl

module Misstep-Integers₁ where
  data ℤ : Set where
    zero : ℤ
    succ : ℤ → ℤ
    pred : ℤ → ℤ

module Misstep-Integers₂ where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ


  normalize : ℤ → ℤ
  normalize (mkℤ zero neg) = mkℤ zero neg
  normalize (mkℤ (suc pos) zero) = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg)) = mkℤ pos neg

  _+_ : ℤ → ℤ → ℤ
  mkℤ a b + mkℤ c d = normalize (mkℤ (a ℕ.+ c) (b ℕ.+ d))

  infixl 5 _+_

  _-_ : ℤ → ℤ → ℤ
  mkℤ a b - mkℤ c d = normalize (mkℤ (a ℕ.+ d) (b ℕ.+ c))

  infixl 5 _-_

  _*_ : ℤ → ℤ → ℤ
  mkℤ a b * mkℤ c d = normalize (mkℤ (a ℕ.* c ℕ.+ b ℕ.* d) (a ℕ.* d ℕ.+ b ℕ.* c))

  infixl 6 _*_

  one : ℤ
  one = mkℤ (suc zero) zero

  two : ℤ
  two = mkℤ (suc (suc zero)) zero

  -one : ℤ
  -one = mkℤ zero (suc zero)

  -two : ℤ
  -two = mkℤ zero (suc (suc zero))

  -four : ℤ
  -four = mkℤ zero (suc (suc (suc (suc zero))))

  _ : two * -two ≡ -four
  _ = refl
