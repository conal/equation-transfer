{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Transfer {i} {I : Set i} where

open import Level using (_⊔_)
open import Algebra.Core using (Op₁; Op₂)

-- Try monoid operations first

infixl 7 _`∙_
data Expr : Set i where
  _`∙_ : Op₂ Expr
  `ε : Expr
  var : I → Expr

module Interp {a} {A : Set a} {ℓ} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) (ε : A) where

  ⟦_⟧ : Expr → (I → A) → A
  ⟦ x ⟧ ρ = go x
   where
     go : Expr → A
     go (x `∙ y) = go x ∙ go y
     go `ε = ε
     go (var i) = ρ i

  infix 4 _∼_
  _∼_ : Rel Expr (i ⊔ a ⊔ ℓ)
  x ∼ y = ∀ ρ → ⟦ x ⟧ ρ ≈ ⟦ y ⟧ ρ

open import Relation.Binary.Structures
open import Relation.Binary.Bundles

open import Algebra.Definitions
import Algebra.Morphism.Definitions as MD
open import Function.Base using (_on_; _∘_)
-- open import Relation.Binary.Construct.On

module _
  {a₂ ℓ₂} (S₂ : Setoid a₂ ℓ₂) (let open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_))
          {_∙₂_ : Op₂ A₂} {ε₂ : A₂}
          (∙₂-cong : Congruent₂ _≈₂_ _∙₂_)
  {a₁   } {A₁ : Set a₁} {_∙₁_ : Op₂ A₁} {ε₁ : A₁} {h : A₁ → A₂}
  (let infix 4 _≈₁_; _≈₁_ = _≈₂_ on h)
  (let open MD A₁ A₂ _≈₂_)
  (∙-hom : Homomorphic₂ h _∙₁_ _∙₂_) (ε-hom : Homomorphic₀ h ε₁ ε₂)
  where

  open Interp _≈₁_ _∙₁_ ε₁ renaming (⟦_⟧ to ⟦_⟧₁; _∼_ to _∼₁_)
  open Interp _≈₂_ _∙₂_ ε₂ renaming (⟦_⟧ to ⟦_⟧₂; _∼_ to _∼₂_)

  open import Relation.Binary.Reasoning.Setoid S₂

  reduce : (u : Expr) (ρ : I → A₁) → h (⟦ u ⟧₁ ρ) ≈₂ ⟦ u ⟧₂ (h ∘ ρ)
  reduce (u `∙ v) ρ =
    begin
      h (⟦ u `∙ v ⟧₁ ρ)
    ≡⟨⟩
      h (⟦ u ⟧₁ ρ ∙₁ ⟦ v ⟧₁ ρ)
    ≈⟨ ∙-hom (⟦ u ⟧₁ ρ) (⟦ v ⟧₁ ρ) ⟩
      h (⟦ u ⟧₁ ρ) ∙₂ h (⟦ v ⟧₁ ρ)
    ≈⟨ ∙₂-cong (reduce u ρ) (reduce v ρ) ⟩
      (⟦ u ⟧₂ (h ∘ ρ) ∙₂ ⟦ v ⟧₂ (h ∘ ρ))
    ≡⟨⟩
      ⟦ u `∙ v ⟧₂ (h ∘ ρ)
    ∎
  reduce `ε ρ = ε-hom
  reduce (var x) ρ = refl

  transfer : (u v : Expr) → u ∼₂ v → u ∼₁ v
  transfer u v u∼₂v ρ =
    begin
      h (⟦ u ⟧₁ ρ)
    ≈⟨ reduce u ρ ⟩
      ⟦ u ⟧₂ (h ∘ ρ)
    ≈⟨ u∼₂v (h ∘ ρ) ⟩
      ⟦ v ⟧₂ (h ∘ ρ)
    ≈˘⟨ reduce v ρ ⟩
      h (⟦ v ⟧₁ ρ)
    ∎

  -- The environments can be inferred in reduce and transfer, so consider
  -- implicit ρ in _∼_, reduce, and transfer.
