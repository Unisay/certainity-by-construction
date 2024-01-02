{-# OPTIONS --allow-unsolved-metas #-}

module Chapter3-Proofs where

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

  *-zeroˡ : (x : ℕ) → 0 * x ≡ 0
  *-zeroˡ x = refl

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

  open ≡-Reasoning

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

  ∨-assoc : (x y z : Bool) → (x ∨ y) ∨ z ≡ x ∨ (y ∨ z)
  ∨-assoc false y z = refl
  ∨-assoc true y z = refl

  ∧-assoc : (x y z : Bool) → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
  ∧-assoc false y z = refl
  ∧-assoc true y z = refl

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc w) y z =
    begin
      suc w + y + z
    ≡⟨⟩
      suc (w + y + z)
    ≡⟨ cong suc (+-assoc w y z) ⟩
      suc (w + (y + z))
    ≡⟨⟩
      suc w + (y + z)
    ∎

  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc w) y = begin
    suc w + y      ≡⟨ cong suc (+-comm w y) ⟩ 
    suc (y + w)    ≡⟨ sym (+-suc y w) ⟩ 
    y + suc w      ∎

  +-suc' : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc' x 0 =  begin
    x + 1       ≡⟨ +-comm x 1 ⟩ 
    1 + x       ≡⟨⟩ 
    suc (0 + x) ≡⟨ cong suc (sym (+-identityʳ x)) ⟩ 
    suc (x + 0) ∎
  +-suc' x (suc y) = begin
    x + suc (suc y)  ≡⟨ +-comm x (suc (suc y)) ⟩ 
    suc (suc y) + x  ≡⟨⟩ 
    suc (suc y + x)  ≡⟨ cong suc (+-comm (suc y) x) ⟩ 
    suc (x + suc y)  ∎

  suc-injective : (x y : ℕ) → suc x ≡ suc y → x ≡ y
  suc-injective x y refl = refl

  *-succ : (x y : ℕ) → x * suc y ≡ x + (x * y)
  *-succ 0 y = refl 
  *-succ (suc w) y = begin
      suc w * suc y
    ≡⟨⟩ 
      suc y + w * suc y
    ≡⟨ cong (λ φ → suc y + φ) (*-succ w y) ⟩ 
      suc y + (w + w * y)
    ≡⟨⟩ 
      suc (y + (w + (w * y)))
    ≡⟨ cong suc (sym (+-assoc y w (w * y))) ⟩ 
      suc ((y + w) + w * y)
    ≡⟨ cong (λ φ → suc φ + (w * y)) (+-comm y w) ⟩ 
      suc ((w + y) + w * y)
    ≡⟨ cong suc (+-assoc w y (w * y)) ⟩ 
      suc (w + (y + w * y))
    ≡⟨⟩ 
      suc w + (y + w * y)
    ≡⟨⟩ 
      suc w + (suc w * y)
    ∎

  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc w) y = begin
      suc w * y
    ≡⟨⟩ 
      y + w * y
    ≡⟨ cong (λ φ → y + φ) (*-comm w y) ⟩ 
      y + y * w 
    ≡⟨ sym (*-succ y w) ⟩ 
      y * suc w
    ∎

  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
  *-distribˡ-+ zero y z = refl
  *-distribˡ-+ (suc w) y z =
    begin
      suc w * (y + z)
    ≡⟨⟩ 
      (y + z) + (w * (y + z))
    ≡⟨ cong (λ φ → y + z + φ) (*-distribˡ-+ w y z) ⟩ 
      (y + z) + (w * y + w * z)
    ≡⟨ sym (+-assoc (y + z) (w * y) (w * z)) ⟩ 
      ((y + z) + w * y) + w * z
    ≡⟨ cong (λ φ → (φ + (w * y)) + (w * z)) (+-comm y z) ⟩
      ((z + y) + w * y) + w * z
    ≡⟨ cong (λ φ → (φ + w * z)) (+-assoc z y (w * y)) ⟩
      z + (y + w * y) + w * z
    ≡⟨ cong (λ φ → (φ + w * z)) (+-comm z (y + w * y)) ⟩ 
      y + w * y + z + w * z
    ≡⟨ +-assoc (y + w * y) z (w * z) ⟩ 
      (y + w * y) + (z + w * z)
    ≡⟨⟩ 
      suc w * y + suc w * z
    ∎

  *-distribʳ-+ : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
  *-distribʳ-+ zero y z = refl
  *-distribʳ-+ (suc w) y z = 
    begin
      (suc w + y) * z
    ≡⟨⟩ 
      suc (w + y) * z 
    ≡⟨⟩ 
      z + (w + y) * z
    ≡⟨ {!   !} ⟩ 
      suc w * z + y * z
    ∎


  -- *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  -- *-assoc zero y z = refl
  -- *-assoc (suc w) y z =
  --   begin
  --     (suc w * y) * z
  --   ≡⟨⟩
  --     (y + w * y) * z
  --   ≡⟨ *-distribˡ-+ {!   !} {!   !} {!   !} ⟩ 
  --     y * z + w * y * z
  --   ≡⟨ {!   !} ⟩
  --     suc w * (y * z)
  --   ∎
