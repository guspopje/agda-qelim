open import Boiler
open import Data.Vec
import Data.Sum
import Data.Product
module Sum = Data.Sum
module Product = Data.Product

module QElim where

  -- (Decidable) Atom and friends
  record DecAtom : Set₁ where
    field
      Atom : ℕ → Set                                               -- atoms, indexed by DeBruijn depth
      Y : Set                                                      -- value type (e.g. ℕ)
      ⟦_⟧ₐ : {n : ℕ} → Atom n → Vec Y n → Set                      -- semantics of atoms
      ⟦_⟧ₐ? : {n : ℕ} (a : Atom n) (e : Vec Y n) → Dec (⟦ a ⟧ₐ e)  -- decidability thereof


  -- Prerequisite I: decidable atoms
  module WithDecAtom (da : DecAtom) where
    open DecAtom da

    -- Propositions
    data Prop (n : ℕ) : Set where
      atom : Atom n → Prop n
      ⊥⊥   : Prop n
      _∨_  : Prop n → Prop n → Prop n
      _∧_  : Prop n → Prop n → Prop n
      _⇒_  : Prop n → Prop n → Prop n
      E_   : Prop (suc n) → Prop n
      A_   : Prop (suc n) → Prop n

    ~_ : {n : ℕ} → Prop n → Prop n
    ~ φ = φ ⇒ ⊥⊥

    -- Constructive semantics of Prop
    ⟦_⟧ : {n : ℕ} → Prop n → Vec Y n → Set
    ⟦ ⊥⊥ ⟧      ys = ⊥
    ⟦ atom a ⟧  ys = ⟦ a ⟧ₐ ys
    ⟦ φ₁ ∨ φ₂ ⟧ ys = (⟦ φ₁ ⟧ ys) ⊎ (⟦ φ₂ ⟧ ys)
    ⟦ φ₁ ∧ φ₂ ⟧ ys = (⟦ φ₁ ⟧ ys) × (⟦ φ₂ ⟧ ys)
    ⟦ φ₁ ⇒ φ₂ ⟧ ys = (⟦ φ₁ ⟧ ys) → (⟦ φ₂ ⟧ ys)
    ⟦ E φ ⟧     ys = Σ Y (λ y → ⟦ φ ⟧ (y ∷ ys))
    ⟦ A φ ⟧     ys = (y : Y) → (⟦ φ ⟧ (y ∷ ys))

    -- Quantifier free propositions
    data QFree {n : ℕ} : Prop n → Set where
      ⊥⊥  : QFree ⊥⊥
      atom : (a : Atom n) → QFree (atom a)
      _∨_ :  {φ₁ φ₂ : Prop n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ ∨ φ₂)
      _∧_ :  {φ₁ φ₂ : Prop n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ ∧ φ₂)
      _⇒_ :  {φ₁ φ₂ : Prop n} → QFree φ₁ → QFree φ₂ → QFree (φ₁ ⇒ φ₂)

    ~-qf_ : {n : ℕ} {φ : Prop n} → QFree φ → QFree (~ φ)
    ~-qf qf = qf ⇒ ⊥⊥

    -- Abstract single-step ∃ elimination procedure
    record QE : Set where
      field
        elim  : {n : ℕ} (φ : Prop (suc n)) → QFree φ → Prop n
        qfree : {n : ℕ} (φ : Prop (suc n)) (qf : QFree φ) → QFree (elim φ qf)
        equiv : {n : ℕ} (φ : Prop (suc n)) (qf : QFree φ) (e : Vec Y n) → ⟦ E φ ⟧ e ↔ ⟦ elim φ qf ⟧ e


    qfree-dec : {n : ℕ} → (φ : Prop n) → QFree φ → (e : Vec Y n) → Dec (⟦ φ ⟧ e)
    qfree-dec _ ⊥⊥ e = no (λ ())
    qfree-dec _ (atom a) e = ⟦ a ⟧ₐ? e
    qfree-dec (φ₁ ∨ φ₂) (qf₁ ∨ qf₂) e = (qfree-dec φ₁ qf₁ e) ⊎? (qfree-dec φ₂ qf₂ e)
    qfree-dec (φ₁ ∧ φ₂) (qf₁ ∧ qf₂) e = (qfree-dec φ₁ qf₁ e) ×? (qfree-dec φ₂ qf₂ e)
    qfree-dec (φ₁ ⇒ φ₂) (qf₁ ⇒ qf₂) e = (qfree-dec φ₁ qf₁ e) →? (qfree-dec φ₂ qf₂ e)

    qfree-¬¬ : {n : ℕ} (φ : Prop n) (qf : QFree φ) (e : Vec Y n) → ¬ ¬ (⟦ φ ⟧ e) → ⟦ φ ⟧ e
    qfree-¬¬ φ qf e ¬¬⟦φ⟧ with qfree-dec φ qf e
    ... | yes ⟦φ⟧ = ⟦φ⟧
    ... | no ¬⟦φ⟧ = contradiction ¬⟦φ⟧ ¬¬⟦φ⟧


    ∀-duality-fwd : {A : Set} {B : A → Set} → ((a : A) → B a) → ¬ Σ A (¬_ ∘ B)
    ∀-duality-fwd all-true (a , is-false) = is-false (all-true a)

    ∀-duality-bwd : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → ¬ Σ A (¬_ ∘ B) → ((a : A) → B a)
    ∀-duality-bwd decide none-false a with decide a
    ... | yes a-true = a-true
    ... | no a-false = ⊥-elim (none-false (a , a-false))

    Σ-map : {A : Set} {B C : A → Set} → ((a : A) → B a → C a) → Σ A B → Σ A C
    Σ-map f (a , b) = (a , f a b)

    Π-map : {A : Set} {B C : A → Set} → ((a : A) → B a → C a) → ((a : A) → B a) → ((a : A) → C a)
    Π-map f g a = f a (g a)


    -- General quantifier elimination
    lift-qe : {n : ℕ} → QE → Prop n → Prop n
    lift-qe-qfree : {n : ℕ} (qe : QE) (φ : Prop n) → QFree (lift-qe qe φ)
    lift-qe _ ⊥⊥ = ⊥⊥
    lift-qe _ (atom a) = atom a
    lift-qe qe (φ₁ ∨ φ₂) = (lift-qe qe φ₁) ∨ (lift-qe qe φ₂)
    lift-qe qe (φ₁ ∧ φ₂) = (lift-qe qe φ₁) ∧ (lift-qe qe φ₂)
    lift-qe qe (φ₁ ⇒ φ₂) = (lift-qe qe φ₁) ⇒ (lift-qe qe φ₂)
    lift-qe qe (E φ) = QE.elim qe (lift-qe qe φ) (lift-qe-qfree qe φ)
    lift-qe qe (A φ) = ~ (QE.elim qe (~ lift-qe qe φ) (~-qf lift-qe-qfree qe φ))

    lift-qe-qfree _ ⊥⊥ = ⊥⊥
    lift-qe-qfree _ (atom a) = atom a
    lift-qe-qfree qe (φ₁ ∨ φ₂) = (lift-qe-qfree qe φ₁) ∨ (lift-qe-qfree qe φ₂)
    lift-qe-qfree qe (φ₁ ∧ φ₂) = (lift-qe-qfree qe φ₁) ∧ (lift-qe-qfree qe φ₂)
    lift-qe-qfree qe (φ₁ ⇒ φ₂) = (lift-qe-qfree qe φ₁) ⇒ (lift-qe-qfree qe φ₂)
    lift-qe-qfree qe (E φ) = QE.qfree qe (lift-qe qe φ) (lift-qe-qfree qe φ)
    lift-qe-qfree qe (A φ) = ~-qf QE.qfree qe (~ lift-qe qe φ) (~-qf lift-qe-qfree qe φ)

    -- Correctness of general quantifier elimination
    lift-qe-fwd : {n : ℕ} (qe : QE) (φ : Prop n) (e : Vec Y n) → ⟦ φ ⟧ e → ⟦ lift-qe qe φ ⟧ e
    lift-qe-bwd : {n : ℕ} (qe : QE) (φ : Prop n) (e : Vec Y n) → ⟦ lift-qe qe φ ⟧ e → ⟦ φ ⟧ e

    lift-qe-fwd qe ⊥⊥ e = λ ()
    lift-qe-fwd qe (atom a) e  = id
    lift-qe-fwd qe (φ₁ ∨ φ₂) e = Sum.map (lift-qe-fwd qe φ₁ e) (lift-qe-fwd qe φ₂ e)
    lift-qe-fwd qe (φ₁ ∧ φ₂) e = Product.map (lift-qe-fwd qe φ₁ e) (lift-qe-fwd qe φ₂ e)
    lift-qe-fwd qe (φ₁ ⇒ φ₂) e = λ f → lift-qe-fwd qe φ₂ e ∘ f ∘ lift-qe-bwd qe φ₁ e
    lift-qe-fwd qe (E φ) e     = proj₁ (QE.equiv qe (lift-qe qe φ) (lift-qe-qfree qe φ) e)
                                 ∘ Σ-map (λ y → lift-qe-fwd qe φ (y ∷ e))
    lift-qe-fwd qe (A φ) e     =
      contraposition (proj₂ (QE.equiv qe (~ lift-qe qe φ) (~-qf lift-qe-qfree qe φ) e))
      ∘ ∀-duality-fwd
      ∘ Π-map (λ y → lift-qe-fwd qe φ (y ∷ e))

    lift-qe-bwd qe ⊥⊥ e = λ ()
    lift-qe-bwd qe (atom a) e = id
    lift-qe-bwd qe (φ₁ ∨ φ₂) e = Sum.map (lift-qe-bwd qe φ₁ e) (lift-qe-bwd qe φ₂ e)
    lift-qe-bwd qe (φ₁ ∧ φ₂) e = Product.map (lift-qe-bwd qe φ₁ e) (lift-qe-bwd qe φ₂ e)
    lift-qe-bwd qe (φ₁ ⇒ φ₂) e = λ f → lift-qe-bwd qe φ₂ e ∘ f ∘ lift-qe-fwd qe φ₁ e
    lift-qe-bwd qe (E φ) e     =
      Σ-map (λ y → lift-qe-bwd qe φ (y ∷ e))
      ∘ proj₂ (QE.equiv qe (lift-qe qe φ) (lift-qe-qfree qe φ) e)
    lift-qe-bwd qe (A φ) e     =
      Π-map (λ y → lift-qe-bwd qe φ (y ∷ e))
      ∘ ∀-duality-bwd (λ y → qfree-dec (lift-qe qe φ) (lift-qe-qfree qe φ) (y ∷ e))
      ∘ contraposition (proj₁ (QE.equiv qe (~ lift-qe qe φ) (~-qf lift-qe-qfree qe φ) e))


    -- Prerequisite II: a single-step QE
    module WithQE (qe : QE) where

      -- Constructive semantics are decidable
      ⟦_⟧? : {n : ℕ} → (φ : Prop n) → (e : Vec Y n) → Dec (⟦ φ ⟧ e)
      ⟦ φ ⟧? e with qfree-dec (lift-qe qe φ) (lift-qe-qfree qe φ) e
      ... | yes ⟦ψ⟧ = yes (lift-qe-bwd qe φ e ⟦ψ⟧)
      ... | no ¬⟦ψ⟧ = no (¬⟦ψ⟧ ∘ lift-qe-fwd qe φ e)

      LEM : {n : ℕ} (φ : Prop n) (e : Vec Y n) → ⟦ φ ∨ (~ φ) ⟧ e
      LEM φ e with ⟦ φ ⟧? e
      ... | yes ⟦φ⟧ = inj₁ ⟦φ⟧
      ... | no ¬⟦φ⟧ = inj₂ ¬⟦φ⟧

      ∃-or-∀¬ : {n : ℕ} (φ : Prop (suc n)) (e : Vec Y n) → ⟦ (E φ) ∨ (A ~ φ) ⟧ e
      ∃-or-∀¬ φ e with ⟦ E φ ⟧? e
      ... | yes ⟦Eφ⟧ = inj₁ ⟦Eφ⟧
      ... | no ¬⟦Eφ⟧ = inj₂ (λ y → λ ⟦φ⟧ → contradiction (y , ⟦φ⟧) ¬⟦Eφ⟧)

      ∀-or-∃¬ : {n : ℕ} (φ : Prop (suc n)) (e : Vec Y n) → ⟦ (A φ) ∨ (E ~ φ) ⟧ e
      ∀-or-∃¬ φ e with ⟦ E (~ φ) ⟧? e
      ... | yes ⟦E~φ⟧ = inj₂ ⟦E~φ⟧
      ... | no ¬⟦E~φ⟧ = inj₁ (λ y → [ id , (λ ¬⟦φ⟧ → contradiction (y , ¬⟦φ⟧) ¬⟦E~φ⟧) ]′ (LEM φ (y ∷ e)))
