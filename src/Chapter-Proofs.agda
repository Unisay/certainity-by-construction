module Chapter-Proofs where

  open import Data.Nat 
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  +-identityˡ : (x : ℕ) → 0 + x ≡ x
  +-identityˡ _ = refl

  +-identityʳ : (x : ℕ) → x + 0 ≡ x
  +-identityʳ zero = refl
  +-identityʳ (suc x) = cong suc (+-identityʳ x)

  *-identityˡ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (+-identityʳ x)

  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  *-zeroʳ : (x : ℕ) → x * 0 ≡ 0
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)

  open import Data.Bool

  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ _ = refl

  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ true = refl
  ∨-identityʳ false = refl

  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ _ = refl

  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ true = refl
  ∧-identityʳ false = refl

  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ _ = refl

  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ true = refl
  ∧-zeroʳ false = refl

  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

  trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl 

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + (b * 0)
  a^1≡a+b*0 a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (a +_) (sym (*-zeroʳ b )))
    )

  module ≡-Reasoning where

    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin_ x=y = x=y

    infix 1 begin_

    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ _ = refl

    infix 3 _∎

    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
    _ ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _ : 4 ≡ suc (1 + 2)
    _ = 
      4           ≡⟨⟩
      2 + 2       ≡⟨⟩
      suc 1 + 2   ≡⟨⟩
      suc (1 + 2) ∎

    _≡⟨_⟩_
      : {A : Set}
      → (x : A)
      → {y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ j ⟩ p = trans j p

    infixr 2 _≡⟨_⟩_

  a^1≡a+b*0' : (a b : ℕ) → a ^ 1 ≡ a + (b * 0)
  a^1≡a+b*0' a b =
    begin
      a ^ 1
    ≡⟨ ^-identityʳ a ⟩
      a
    ≡⟨ sym (+-identityʳ a) ⟩
      a + 0
    ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
      a + b * 0
    ∎
    where open ≡-Reasoning
 