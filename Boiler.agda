module Boiler where

  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Data.List using (List ; [] ; _∷_ ; _++_ ; map ; [_]) public
  open import Data.Vec using (Vec) public
  open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂) public
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′) public
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no) public
  open import Relation.Nullary.Negation using (contradiction ; contraposition) public
  open import Data.Empty using (⊥ ; ⊥-elim) public
  open import Data.Unit using (⊤ ; tt) public
  open import Function using (id ; _∘_ ; flip) public


  _↔_ : Set → Set → Set
  A ↔ B = (A → B) × (B → A)

  ¬¬-intro : {A : Set} → A → ¬ ¬ A
  ¬¬-intro a = λ ¬a → ¬a a

  _⊎?_ : {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
  (yes a) ⊎? _ = yes (inj₁ a)
  (no ¬a) ⊎? (yes b) = yes (inj₂ b)
  (no ¬a) ⊎? (no ¬b) = no [ ¬a , ¬b ]′

  _×?_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
  (yes a) ×? (yes b) = yes (a , b)
  (yes a) ×? (no ¬b) = no (¬b ∘ proj₂)
  (no ¬a) ×? _ = no (¬a ∘ proj₁)

  _→?_ : {A B : Set} → Dec A → Dec B → Dec (A → B)
  _       →? (yes b) = yes (λ _ → b)
  (yes a) →? (no ¬b) = no (λ f → ¬b (f a))
  (no ¬a) →? (no ¬b) = yes (λ a → contradiction a ¬a)

  ¬? : {A : Set} → Dec A → Dec (¬ A)
  ¬? (yes a) = no (λ f → f a)
  ¬? (no ¬a) = yes ¬a





  data _∈_ {A : Set} (a : A) : List A → Set where
    here : (as : List A) → a ∈ (a ∷ as)
    there : {as : List A} (b : A) → a ∈ as → a ∈ (b ∷ as)

  allP : {A : Set} → (A → Set) → List A → Set
  allP P [] = ⊤
  allP P (a ∷ as) = P a × allP P as

  mapAllP : {A : Set} {P Q : A → Set} → ({a : A} → P a → Q a) → (as : List A) → allP P as → allP Q as
  mapAllP _ [] _ = tt
  mapAllP f (a ∷ as) (a! , as!) = (f a! , mapAllP f as as!)

  mapWithP : {A B : Set} {P : A → Set} (f : (a : A) → P a → B) (as : List A) → allP P as → List B
  mapWithP f [] _ = []
  mapWithP f (a ∷ as) (pa , pas) = f a pa ∷ mapWithP f as pas

  -- For a decidable property P, it is true for something in the list or nothing in the list.
  first : {A : Set} (P : A → Set) → ((a : A) → Dec (P a)) → (as : List A)
    → (Σ A (λ a → (P a × a ∈ as))) ⊎ (allP (¬_ ∘ P) as)
  first P P? [] = inj₂ tt
  first P P? (a ∷ as) with P? a
  ... | yes Pa = inj₁ (a , Pa , here as)
  ... | no ¬Pa with first P P? as
  ... | inj₁ (a' , Pa' , a'∈as) = inj₁ (a' , Pa' , there a a'∈as)
  ... | inj₂ ¬Pas = inj₂ (¬Pa , ¬Pas)

  ∈-++₁ : {A : Set} {a : A} (xs ys : List A) → a ∈ xs → a ∈ (xs ++ ys)
  ∈-++₁ (a ∷ .xs) ys (here xs) = here (xs ++ ys)
  ∈-++₁ (.x ∷ xs) ys (there x a∈xs) = there x (∈-++₁ xs ys a∈xs)

  ∈-++₂ : {A : Set} {a : A} (xs ys : List A) → a ∈ ys → a ∈ (xs ++ ys)
  ∈-++₂ [] ys a∈ys = a∈ys
  ∈-++₂ (x ∷ xs) ys a∈ys = there x (∈-++₂ xs ys a∈ys)

  either-way : {A B : Set}
    → (  A → B)
    → (¬ A → B)
    → Dec A
    → B
  either-way f g (yes a) = f a
  either-way f g (no ¬a) = g ¬a
