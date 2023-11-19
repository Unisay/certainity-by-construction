module Chapter1 where

module Booleans where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

open import Relation.Binary.PropositionalEquality

_ : not (not true) ≡ true 
_ = refl

_ : not (not false) ≡ false
_ = refl

_∨_ : Bool -> Bool -> Bool
true ∨ x₁ = true
false ∨ x₁ = x₁

_v₂_ : Bool -> Bool -> Bool
_v₂_ true true = true
_v₂_ true false = true
_v₂_ false true = true
_v₂_ false false = false

_∧_ : Bool -> Bool -> Bool
true ∧ other = other
false ∧ other = false

module Example-Employees where
  open Booleans
  open import Data.String using (String)

  data Department : Set where
    sales : Department
    development : Department
    marketing : Department

  record Employee : Set where
    field
      name : String
      department : Department
      is-new-hire : Bool

  tillman : Employee
  tillman = record
    { name = "Tillman"
    ; department = sales
    ; is-new-hire = true
    }

module Sandbox-Tuple where
  record _×_ (A B : Set) : Set where
    constructor _,_
    field proj₁ : A
    field proj₂ : B
  infixr 4 _,_

  data _⊎_ (A B : Set) : Set where
    inj₁ : A -> A ⊎ B
    inj₂ : B -> A ⊎ B
  infixr 1 _⊎_


  open _×_
  open _⊎_
  open Booleans

  my-tuple : Bool × Bool
  my-tuple = record { proj₁ = true ; proj₂ = true }

  first : {A : Set} {B : Set} -> A × B -> A
  first record { proj₁ = ₁ } = ₁


  second : {A : Set} {B : Set} -> A × B -> B
  second a×b = a×b .proj₂

  second₂ : {A : Set} {B : Set} -> A × B -> B
  second₂ a×b = proj₂ a×b

  my-copattern : Bool × (Bool × Bool)
  proj₁ my-copattern = true
  proj₁ (proj₂ my-copattern) = false
  proj₂ (proj₂ my-copattern) = not true

  curry : {A B C : Set} -> (A × B -> C) -> A -> B -> C
  curry f a b = f (a , b)

  uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
  uncurry f (a , b) = f a b

  _v₃_ : Bool × Bool → Bool
  _v₃_ = uncurry _∨_

module Sandbox-Implicits where

  open import Data.Bool
    using (Bool; true; false; not; _∨_; _∧_)
  open import Data.Product 
    renaming ( _,′_     to _,_
             ; curry′   to curry
             ; uncurry′ to uncurry
             ) 
