module SN where

  open import Boiler
  open import Data.Fin using (Fin ; zero ; suc)
  open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
  import Data.Sum
  import Data.Product
  import Data.List
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open ≡-Reasoning

  open import Data.Nat using (_≟_ ; decTotalOrder)
  open import Data.Nat.Properties.Simple

  open import QElim
  import QEDNF

  data Base (n : ℕ) : Set where
    ∅ : Base n
    var : Fin n → Base n

  data Term (n : ℕ) : Set where
    S : ℕ → Base n → Term n


  data Atom (n : ℕ) : Set where
    _==_ : Term n → Term n → Atom n

  ⟦_⟧b : {n : ℕ} → Base n → Vec ℕ n → ℕ
  ⟦ ∅ ⟧b _ = zero
  ⟦ var k ⟧b e = lookup k e

  ⟦_⟧ₜ : {n : ℕ} → Term n → Vec ℕ n → ℕ
  ⟦ S k b ⟧ₜ e = k + ⟦ b ⟧b e

  ⟦_⟧ₐ : {n : ℕ} → Atom n → Vec ℕ n → Set
  ⟦ t₁ == t₂ ⟧ₐ e = ⟦ t₁ ⟧ₜ e ≡ ⟦ t₂ ⟧ₜ e

  ⟦_⟧ₐ? : {n : ℕ} (a : Atom n) (e : Vec ℕ n) → Dec (⟦ a ⟧ₐ e)
  ⟦ t₁ == t₂ ⟧ₐ? e = ⟦ t₁ ⟧ₜ e ≟ ⟦ t₂ ⟧ₜ e

  sn-da : DecAtom
  sn-da = record
    { Y = ℕ
    ; Atom = Atom
    ; ⟦_⟧ₐ = ⟦_⟧ₐ
    ; ⟦_⟧ₐ? = ⟦_⟧ₐ?
    }

  open QEDNF sn-da
  open WithDecAtom sn-da

  trueₐ : {n : ℕ} → Atom n
  trueₐ = (S zero ∅ == S zero ∅)

  ⟦trueₐ⟧ : {n : ℕ} (e : Vec ℕ n) → ⟦ trueₐ ⟧ₐ e
  ⟦trueₐ⟧ _ = refl

  open WithTrue trueₐ ⟦trueₐ⟧

  -- And now the goal is to create a ProdQE object.

  -- Namespace for Base operations
  module B where
    dep₀ : {n : ℕ} → Base n → Set
    dep₀ ∅ = ⊥
    dep₀ (var zero) = ⊤
    dep₀ (var (suc _)) = ⊥
    dep₀? : {n : ℕ} (b : Base n) → Dec (dep₀ b)
    dep₀? ∅ = no (λ ())
    dep₀? (var zero) = yes tt
    dep₀? (var (suc _)) = no (λ ())
    ξ : {n : ℕ} → Base n → Base (suc n)
    ξ ∅ = ∅
    ξ (var i) = var (suc i)
    ξ⁻¹ : {n : ℕ} (b : Base (suc n)) → ¬ dep₀ b → Base n
    ξ⁻¹ ∅ _ = ∅
    ξ⁻¹ (var zero) x = contradiction tt x
    ξ⁻¹ (var (suc i)) _ = var i

  -- Namespace for Term operations
  module T where
    dep₀ : {n : ℕ} → Term n → Set
    dep₀ (S _ b) = B.dep₀ b
    dep₀? : {n : ℕ} (t : Term n) → Dec (dep₀ t)
    dep₀? (S _ b) = B.dep₀? b
    ξ : {n : ℕ} → Term n → Term (suc n)
    ξ (S k b) = S k (B.ξ b)
    ξ⁻¹ : {n : ℕ} (t : Term (suc n)) → ¬ dep₀ t → Term n
    ξ⁻¹ (S k b) 0∉b = S k (B.ξ⁻¹ b 0∉b)
    add : {n : ℕ} → ℕ → Term n → Term n
    add j (S k b) = S (j + k) b

  -- Namespace for Atom operations
  module A where
    

  -- A factor suitable for deriving a substitution. Must be equality (not inequality),
  -- and *either* the LHS *or* the RHS (but not both) must depend on index 0.
  SubFactor : {n : ℕ} → Factor n → Set
  SubFactor (+ (t₁ == t₂)) = (T.dep₀ t₁ × ¬ T.dep₀ t₂) ⊎ ((¬ T.dep₀ t₁) × T.dep₀ t₂)
  SubFactor (- _) = ⊥

  SubFactor? : {n : ℕ} (f : Factor n) → Dec (SubFactor f)
  SubFactor? (+ (t₁ == t₂)) with T.dep₀? t₁ | T.dep₀? t₂
  ... | yes 0∈t₁ | yes 0∈t₂ = no [ (λ s → proj₂ s 0∈t₂) , (λ s → proj₁ s 0∈t₁) ]′
  ... | yes 0∈t₁ | no  0∉t₂ = yes (inj₁ (0∈t₁ , 0∉t₂))
  ... | no  0∉t₁ | yes 0∈t₂ = yes (inj₂ (0∉t₁ , 0∈t₂))
  ... | no  0∉t₁ | no  0∉t₂ = no [ 0∉t₁ ∘ proj₁ , 0∉t₂ ∘ proj₂ ]′
  SubFactor? (- _) = no (λ ())

  -- A substitution for variable 0. Carries the meaning k + var0 = ξ term. See iSub.
  record Sub (n : ℕ) : Set where
    constructor Subst
    field
      k : ℕ
      term : Term n

  -- Interpret a Sub to the underlying equality it represents: k + var0 = ξ term.
  iSub : {n : ℕ} → Sub n → Atom (suc n)
  iSub sub = S (Sub.k sub) (var zero) == T.ξ (Sub.term sub)

  -- Extract a substitution from a factor bearing one.
  getSub : {n : ℕ} (f : Factor (suc n)) → SubFactor f → Sub n
  getSub (+ (S k x == S j y)) (inj₁ (_ , 0∉t₂)) = Subst k (T.ξ⁻¹ (S j y) 0∉t₂)
  getSub (+ (S j y == S k x)) (inj₂ (0∉t₁ , _)) = Subst k (T.ξ⁻¹ (S j y) 0∉t₁)
  getSub (- _) ()


  -- Eliminate var0 from an atom by way of a substitution.
  reduce-atom-sub : {n : ℕ} → Sub n → Atom (suc n) → Atom n
  reduce-atom-sub (Subst k term) (S a x == S b y) with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = S a ∅ == S b ∅
  ... | yes x0 | no ¬y0 = T.add a term == S (k + b) (B.ξ⁻¹ y ¬y0)
  ... | no ¬x0 | yes y0 = S (k + a) (B.ξ⁻¹ x ¬x0) == T.add b term
  ... | no ¬x0 | no ¬y0 = S a (B.ξ⁻¹ x ¬x0) ==  S b (B.ξ⁻¹ y ¬y0)

  -- Eliminate var0 from a factor by way of a substitution.
  reduce-factor-sub : {n : ℕ} → Sub n → Factor (suc n) → Factor n
  reduce-factor-sub sub (+ a) = + (reduce-atom-sub sub a)
  reduce-factor-sub sub (- a) = - (reduce-atom-sub sub a)

  -- Eliminate var0 from a factor that is not a substitution, under the assumption that
  -- no other factors in the product are substitutions either.
  reduce-factor-nosubs : {n : ℕ} (f : Factor (suc n)) → ¬ SubFactor f → Factor n
  reduce-factor-nosubs (+ (S a x == S b y)) ¬sub with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = + (S a ∅ == S b ∅)
  ... | yes x0 | no ¬y0 = contradiction (inj₁ (x0 , ¬y0)) ¬sub
  ... | no ¬x0 | yes y0 = contradiction (inj₂ (¬x0 , y0)) ¬sub
  ... | no ¬x0 | no ¬y0 = + (S a (B.ξ⁻¹ x ¬x0) == S b (B.ξ⁻¹ y ¬y0))
  reduce-factor-nosubs (- (S a x == S b y)) _ with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = - (S a ∅ == S b ∅)
  ... | yes x0 | no ¬y0 = + trueₐ
  ... | no ¬x0 | yes y0 = + trueₐ
  ... | no ¬x0 | no ¬y0 = - (S a (B.ξ⁻¹ x ¬x0) == S b (B.ξ⁻¹ y ¬y0))

  ineqs′ : {n : ℕ} → ℕ → Term n → List (Factor n)
  ineqs′ zero _ = []
  ineqs′ (suc m) term = (- (term == S m ∅)) ∷ (ineqs′ m term)

  ineqs : {n : ℕ} → Sub n → List (Factor n)
  ineqs (Subst k term) = ineqs′ k term

  elim-with-sub : {n : ℕ} → Sub n → List (Factor (suc n)) → List (Factor n)
  elim-with-sub sub fs = (ineqs sub) ++ (map (reduce-factor-sub sub) fs)

  elim-prod : {n : ℕ} → List (Factor (suc n)) → List (Factor n)
  elim-prod fs with first SubFactor SubFactor? fs
  elim-prod fs | inj₁ (f , fsub , _) = elim-with-sub (getSub f fsub) fs
  elim-prod fs | inj₂ none-sub = mapWithP reduce-factor-nosubs fs none-sub



  -- And now we prove correctness :<

  pred* : {a b : ℕ} (k : ℕ) → k + a ≡ k + b → a ≡ b
  pred* zero eq = eq
  pred* (suc m) eq = pred* m (cong pred eq)

  pred*′ : {a b : ℕ} (k : ℕ) → a + k ≡ b + k → a ≡ b
  pred*′ {a} {b} k eq = pred* k (trans (trans (+-comm k a) eq) (+-comm b k))

  suc* : {a b : ℕ} (k : ℕ) → a ≡ b → k + a ≡ k + b
  suc* k = cong (_+_ k)

  suc*′ : {a b : ℕ} (k : ℕ) → a ≡ b → a + k ≡ b + k
  suc*′ {a} {b} k eq = trans (trans (+-comm a k) (suc* k eq)) (+-comm k b)

  shift : {a b : ℕ} (k₁ k₂ : ℕ) → k₁ + a ≡ k₁ + b → k₂ + a ≡ k₂ + b
  shift k₁ k₂ = suc* k₂ ∘ pred* k₁

  shift′ : {a b : ℕ} (k₁ k₂ : ℕ) → a + k₁ ≡ b + k₁ → a + k₂ ≡ b + k₂
  shift′ {a} {b} k₁ k₂ = suc*′ {a} {b} k₂ ∘ pred*′ {a} {b} k₁

  sandwich : {A : Set} {a b c d : A} → b ≡ a → c ≡ d → b ≡ c → a ≡ d
  sandwich left′ right middle = trans (trans (sym left′) middle) right

  dep₀-base-eval : {n : ℕ} (x : Base (suc n)) → B.dep₀ x → (v : ℕ) (e : Vec ℕ n) → ⟦ x ⟧b (v ∷ e) ≡ v
  dep₀-base-eval ∅ ()
  dep₀-base-eval (var zero) _ v _ = refl
  dep₀-base-eval (var (suc m)) ()

  dep₀-term-eval : {n : ℕ} (a : ℕ) (x : Base (suc n)) → B.dep₀ x → (v : ℕ) (e : Vec ℕ n) → ⟦ S a x ⟧ₜ (v ∷ e) ≡ a + v
  dep₀-term-eval a x x0 v e = suc* a (dep₀-base-eval x x0 v e)

  ξ⁻¹-⟦⟧b : {n : ℕ} (x : Base (suc n)) (¬x0 : ¬ B.dep₀ x) → (v : ℕ) (e : Vec ℕ n) → ⟦ x ⟧b (v ∷ e) ≡ ⟦ B.ξ⁻¹ x ¬x0 ⟧b e
  ξ⁻¹-⟦⟧b ∅ _ _ _ = refl
  ξ⁻¹-⟦⟧b (var zero) ¬0 = contradiction tt ¬0
  ξ⁻¹-⟦⟧b (var (suc i)) _ v e = refl


  ξ⁻¹-⟦⟧ₜ : {n : ℕ} (t : Term (suc n)) (¬t0 : ¬ T.dep₀ t) → (v : ℕ) (e : Vec ℕ n) → ⟦ t ⟧ₜ (v ∷ e) ≡ ⟦ T.ξ⁻¹ t ¬t0 ⟧ₜ e
  ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 v e = cong (_+_ a) (ξ⁻¹-⟦⟧b x ¬x0 v e)


  ξ-⟦⟧ₜ : {n : ℕ} (t : Term n) (v : ℕ) (e : Vec ℕ n) → ⟦ t ⟧ₜ e ≡ ⟦ T.ξ t ⟧ₜ (v ∷ e)
  ξ-⟦⟧ₜ (S a ∅) _ _ = refl
  ξ-⟦⟧ₜ (S a (var i)) v e = suc* a refl

  ξ-ξ⁻¹-⟦⟧ₜ : {n : ℕ} → (t : Term (suc n)) (¬t0 : ¬ T.dep₀ t) (e : Vec ℕ (suc n))
    → ⟦ t ⟧ₜ e ≡ ⟦ T.ξ (T.ξ⁻¹ t ¬t0) ⟧ₜ e
  ξ-ξ⁻¹-⟦⟧ₜ t ¬t0 (v ∷ e) = 
    begin
      ⟦ t ⟧ₜ (v ∷ e)
    ≡⟨ ξ⁻¹-⟦⟧ₜ t ¬t0 v e ⟩
      ⟦ T.ξ⁻¹ t ¬t0 ⟧ₜ e
    ≡⟨ ξ-⟦⟧ₜ (T.ξ⁻¹ t ¬t0) v e ⟩
      ⟦ T.ξ (T.ξ⁻¹ t ¬t0) ⟧ₜ (v ∷ e)
    ∎

  Tadd-⟦⟧ₜ : {n : ℕ} (k : ℕ) (t : Term n) (e : Vec ℕ n) → ⟦ T.add k t ⟧ₜ e ≡ k + ⟦ t ⟧ₜ e
  Tadd-⟦⟧ₜ k (S a x) e = +-assoc k a (⟦ x ⟧b e)

  sub-fwd : {n : ℕ} (k : ℕ) (term : Term n) (a b : ℕ) (x y : Base (suc n)) → B.dep₀ x → (¬y0 : ¬ B.dep₀ y)
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub (Subst k term) ⟧ₐ (v ∷ e)
    → ⟦ S a x == S b y ⟧ₐ (v ∷ e)
    → ⟦ T.add a term == S (k + b) (B.ξ⁻¹ y ¬y0) ⟧ₐ e
  sub-fwd k term a b x y x0 ¬y0 v e sub! atm! = 
    begin
      ⟦ T.add a term ⟧ₜ e
    ≡⟨ Tadd-⟦⟧ₜ a term e ⟩
      a + ⟦ term ⟧ₜ e
    ≡⟨ suc* a (ξ-⟦⟧ₜ term v e) ⟩
      a + ⟦ T.ξ term ⟧ₜ (v ∷ e)
    ≡⟨ suc* a (sym sub!) ⟩
      a + (k + v)
    ≡⟨ sym (+-assoc a k v) ⟩
      (a + k) + v
    ≡⟨ suc*′ v (+-comm a k) ⟩
      (k + a) + v
    ≡⟨ suc* (k + a) (sym (dep₀-base-eval x x0 v e)) ⟩
      (k + a) + ⟦ x ⟧b (v ∷ e)
    ≡⟨ +-assoc k a (⟦ x ⟧b (v ∷ e)) ⟩
      k + (a + ⟦ x ⟧b (v ∷ e))
    ≡⟨ suc* k atm! ⟩
      k + (b + ⟦ y ⟧b (v ∷ e))
    ≡⟨ sym (+-assoc k b (⟦ y ⟧b (v ∷ e))) ⟩
      (k + b) + ⟦ y ⟧b (v ∷ e)
    ≡⟨ suc* (k + b) (ξ⁻¹-⟦⟧b y ¬y0 v e) ⟩
      (k + b) + ⟦ B.ξ⁻¹ y ¬y0 ⟧b e
    ∎

  sub-bwd : {n : ℕ} (k : ℕ) (term : Term n) (a b : ℕ) (x y : Base (suc n)) → B.dep₀ x → (¬y0 : ¬ B.dep₀ y)
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub (Subst k term) ⟧ₐ (v ∷ e)
    → ⟦ T.add a term == S (k + b) (B.ξ⁻¹ y ¬y0) ⟧ₐ e
    → ⟦ S a x == S b y ⟧ₐ (v ∷ e)
  sub-bwd k term a b x y x0 ¬y0 v e sub! atm! = pred* k (
    begin
      k + ⟦ S a x ⟧ₜ (v ∷ e)
    ≡⟨ suc* k (dep₀-term-eval a x x0 v e) ⟩
      k + (a + v)
    ≡⟨ sym (+-assoc k a v) ⟩
      (k + a) + v
    ≡⟨ suc*′ v (+-comm k a) ⟩
      (a + k) + v
    ≡⟨ +-assoc a k v ⟩
      a + (k + v)
    ≡⟨ cong (_+_ a) sub! ⟩
      a + ⟦ T.ξ term ⟧ₜ (v ∷ e)
    ≡⟨ suc* a (sym (ξ-⟦⟧ₜ term v e)) ⟩
      a + ⟦ term ⟧ₜ e
    ≡⟨ sym (Tadd-⟦⟧ₜ a term e) ⟩
      ⟦ T.add a term ⟧ₜ e
    ≡⟨ atm! ⟩
      ⟦ S (k + b) (B.ξ⁻¹ y ¬y0) ⟧ₜ e
    ≡⟨ sym (ξ⁻¹-⟦⟧ₜ (S (k + b) y) ¬y0 v e) ⟩
      ⟦ S (k + b) y ⟧ₜ (v ∷ e)
    ≡⟨ refl ⟩
      (k + b) + ⟦ y ⟧b (v ∷ e)
    ≡⟨ +-assoc k b (⟦ y ⟧b (v ∷ e)) ⟩
      k + (b + ⟦ y ⟧b (v ∷ e))
    ≡⟨ refl ⟩
      k + ⟦ S b y ⟧ₜ (v ∷ e)
    ∎)

  reduce-atom-sub-fwd : {n : ℕ} → (sub : Sub n) → (atm : Atom (suc n))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ atm ⟧ₐ (v ∷ e)
    → ⟦ reduce-atom-sub sub atm ⟧ₐ e
  reduce-atom-sub-fwd (Subst k term) (S a x == S b y) v e sub! atm! with B.dep₀? x | B.dep₀? y
  reduce-atom-sub-fwd (Subst k term) (S a x == S b y) v e sub! atm! | yes x0 | yes y0 = shift′ {a} {b} v zero (sandwich (dep₀-term-eval a x x0 v e) (dep₀-term-eval b y y0 v e) atm!)
  reduce-atom-sub-fwd (Subst k term) (S a x == S b y) v e sub! atm! | yes x0 | no ¬y0 = sub-fwd k term a b x y x0 ¬y0 v e sub! atm!
  reduce-atom-sub-fwd (Subst k term) (S a x == S b y) v e sub! atm! | no ¬x0 | yes y0 = sym (sub-fwd k term b a y x y0 ¬x0 v e sub! (sym atm!))
  reduce-atom-sub-fwd (Subst k term) (S a x == S b y) v e sub! atm! | no ¬x0 | no ¬y0 = sandwich (suc* a (ξ⁻¹-⟦⟧b x ¬x0 v e)) (suc* b (ξ⁻¹-⟦⟧b y ¬y0 v e)) atm!

  reduce-atom-sub-bwd : {n : ℕ} → (sub : Sub n) → (atm : Atom (suc n))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ reduce-atom-sub sub atm ⟧ₐ e
    → ⟦ atm ⟧ₐ (v ∷ e)
  reduce-atom-sub-bwd (Subst k term) (S a x == S b y) v e sub! atm! with B.dep₀? x | B.dep₀? y
  reduce-atom-sub-bwd (Subst k term) (S a x == S b y) v e sub! atm! | yes x0 | yes y0 = sandwich (sym (dep₀-term-eval a x x0 v e)) (sym (dep₀-term-eval b y y0 v e)) (shift′ {a} {b} zero v atm!)
  reduce-atom-sub-bwd (Subst k term) (S a x == S b y) v e sub! atm! | yes x0 | no ¬y0 = sub-bwd k term a b x y x0 ¬y0 v e sub! atm!
  reduce-atom-sub-bwd (Subst k term) (S a x == S b y) v e sub! atm! | no ¬x0 | yes y0 = sym (sub-bwd k term b a y x y0 ¬x0 v e sub! (sym atm!))
  reduce-atom-sub-bwd (Subst k term) (S a x == S b y) v e sub! atm! | no ¬x0 | no ¬y0 = sandwich (sym (suc* a (ξ⁻¹-⟦⟧b x ¬x0 v e))) (sym (suc* b (ξ⁻¹-⟦⟧b y ¬y0 v e))) atm!

  reduce-factor-sub-fwd : {n : ℕ} → (sub : Sub n) (f : Factor (suc n))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ F.i f ⟧ (v ∷ e)
    → ⟦ F.i (reduce-factor-sub sub f) ⟧ e
  reduce-factor-sub-fwd sub (+ a) v e sub! f! = reduce-atom-sub-fwd sub a v e sub! f!
  reduce-factor-sub-fwd sub (- a) v e sub! f! = f! ∘ (reduce-atom-sub-bwd sub a v e sub!)

  reduce-factor-sub-bwd : {n : ℕ} → (sub : Sub n) (f : Factor (suc n))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ F.i (reduce-factor-sub sub f) ⟧ e
    → ⟦ F.i f ⟧ (v ∷ e)
  reduce-factor-sub-bwd sub (+ a) v e sub! f! = reduce-atom-sub-bwd sub a v e sub! f!
  reduce-factor-sub-bwd sub (- a) v e sub! f! = f! ∘ (reduce-atom-sub-fwd sub a v e sub!)

  stepup : {a b : ℕ} → a ≤ b → a ≤ suc b
  stepup z≤n = z≤n
  stepup (s≤s a≤b) = s≤s (stepup a≤b)

  stepdown : {a b : ℕ} → a ≤ b → pred a ≤ b
  stepdown z≤n = z≤n
  stepdown (s≤s a≤b) = stepup a≤b

  <-≢ : {a b : ℕ} → a < b → ¬ a ≡ b
  <-≢ {zero} {suc b} (s≤s 0≤b) ()
  <-≢ {suc a} {suc b} (s≤s 1+a≤b) eq = <-≢ 1+a≤b (cong pred eq)

  ≤-refl : {a : ℕ} → a ≤ a
  ≤-refl {zero} = z≤n
  ≤-refl {suc a} = s≤s ≤-refl

  ≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

  k+a≤b⇒a≤b : {k a b : ℕ} → k + a ≤ b → a ≤ b
  k+a≤b⇒a≤b {zero} a≤b = a≤b
  k+a≤b⇒a≤b {suc k} (1+k+a≤b) = k+a≤b⇒a≤b {k} (stepdown 1+k+a≤b)

  a+k≤b⇒a≤b : {k a b : ℕ} → a + k ≤ b → a ≤ b
  a+k≤b⇒a≤b {k} {a} {b} = k+a≤b⇒a≤b {k} ∘ subst (λ x → x ≤ b) (+-comm a k)

  ≤-lemma : {a b : ℕ} → a ≤ b → a ≡ b ⊎ suc a ≤ b
  ≤-lemma {zero} {zero} _  = inj₁ refl
  ≤-lemma {zero} {suc b} _ = inj₂ (s≤s z≤n)
  ≤-lemma {suc a} {zero} ()
  ≤-lemma {suc a} {suc b} (s≤s a≤b) = Data.Sum.map (cong suc) s≤s (≤-lemma a≤b)

  ≤-∸ : {a b : ℕ} → a ≤ b → a + (b ∸ a) ≡ b
  ≤-∸ z≤n = refl
  ≤-∸ {suc a} {suc b} (s≤s a≤b) = cong suc (≤-∸ a≤b)

  ineqs′-fwd : {n : ℕ} (k : ℕ) (term : Term n) (e : Vec ℕ n)
    → k ≤ ⟦ term ⟧ₜ e
    → ⟦ P.i (ineqs′ k term) ⟧ e
  ineqs′-fwd zero _ e _ = ⟦true⟧ e
  ineqs′-fwd (suc m) term e k≤term = ( <-≢ k≤term ∘ trans (+-comm zero m) ∘ sym , ineqs′-fwd m term e (stepdown k≤term) )

  ineqs′-bwd : {n : ℕ} (k : ℕ) (term : Term n) (e : Vec ℕ n)
    → ⟦ P.i (ineqs′ k term) ⟧ e
    → k ≤ ⟦ term ⟧ₜ e
  ineqs′-bwd zero _ _ _ = z≤n
  ineqs′-bwd (suc k) term e (term≠k+0 , rest) = [ ⊥-elim ∘ term≠k+0 ∘ sym ∘ trans (+-comm k zero) , id ]′ (≤-lemma (ineqs′-bwd k term e rest))

  ineqs-fwd : {n : ℕ} (sub : Sub n) (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ P.i (ineqs sub) ⟧ e
  ineqs-fwd (Subst k term) v e sub! = ineqs′-fwd k term e (a+k≤b⇒a≤b {v} (subst (_≤_ (k + v)) (trans sub! (sym (ξ-⟦⟧ₜ term v e))) ≤-refl))

  ineqs-bwd : {n : ℕ} (sub : Sub n) (e : Vec ℕ n)
    → ⟦ P.i (ineqs sub) ⟧ e
    → Σ ℕ (λ v → ⟦ iSub sub ⟧ₐ (v ∷ e))
  ineqs-bwd (Subst k term) e ineqs! = (⟦ term ⟧ₜ e ∸ k , trans (≤-∸ (ineqs′-bwd k term e ineqs!)) (ξ-⟦⟧ₜ term (⟦ term ⟧ₜ e ∸ k) e))

  map-fwd : {n n′ : ℕ} (e : Vec ℕ n) (e′ : Vec ℕ n′)
    → (h : Factor n → Factor n′)
    → ((f : Factor n) → ⟦ F.i f ⟧ e → ⟦ F.i (h f) ⟧ e′)
    → (fs : List (Factor n))
    → ⟦ P.i fs ⟧ e
    → ⟦ P.i (map h fs) ⟧ e′
  map-fwd e e′ h h! [] _ = ⟦true⟧ e′
  map-fwd e e′ h h! (f ∷ fs) (f! , fs!) = (h! f f! , map-fwd e e′ h h! fs fs!)

  map-bwd : {n n′ : ℕ} (e : Vec ℕ n) (e′ : Vec ℕ n′)
    → (h : Factor n → Factor n′)
    → ((f : Factor n) → ⟦ F.i (h f) ⟧ e′ → ⟦ F.i f ⟧ e)
    → (fs : List (Factor n))
    → ⟦ P.i (map h fs) ⟧ e′
    → ⟦ P.i fs ⟧ e
  map-bwd e e′ h h! [] _ = ⟦true⟧ e
  map-bwd e e′ h h! (f ∷ fs) (f! , fs!) = (h! f f! , map-bwd e e′ h h! fs fs!)

  ∈-true : {n : ℕ} {f : Factor n} {fs : List (Factor n)} (e : Vec ℕ n) → f ∈ fs → ⟦ P.i fs ⟧ e → ⟦ F.i f ⟧ e
  ∈-true e (here fs) (f! , fs!) = f!
  ∈-true e (there f′ f∈fs) (f′! , fs!) = ∈-true e f∈fs fs!

  iSub-getSub : {n : ℕ} (f : Factor (suc n)) (fsub : SubFactor f) (e : Vec ℕ (suc n))
    → ⟦ F.i f ⟧ e
    → ⟦ iSub (getSub f fsub) ⟧ₐ e
  iSub-getSub (+ (S a (var zero) == S b y)) (inj₁ (x0 , ¬y0)) (v ∷ e) f! = trans f! (ξ-ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 (v ∷ e))
  iSub-getSub (+ (S _ ∅ == _)) (inj₁ (() , _))
  iSub-getSub (+ (S _ (var (suc _)) == _)) (inj₁ (() , _))
  iSub-getSub (+ (S a x == S b (var zero))) (inj₂ (¬x0 , y0)) (v ∷ e) f! = trans (sym f!) ((ξ-ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 (v ∷ e)))
  iSub-getSub (+ (_ == S _ ∅)) (inj₂ (_ , ()))
  iSub-getSub (+ (_ == S _ (var (suc _)))) (inj₂ (_ , ()))
  iSub-getSub (- _) ()

  elim-with-sub-fwd : {n : ℕ} (sub : Sub n) (fs : List (Factor (suc n)))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ P.i fs ⟧ (v ∷ e)
    → ⟦ P.i (elim-with-sub sub fs) ⟧ e
  elim-with-sub-fwd sub fs v e sub! fs! = P.++-fwd (ineqs sub) (map (reduce-factor-sub sub) fs) e
    ( ineqs-fwd sub v e sub!
    , map-fwd (v ∷ e) e (reduce-factor-sub sub) (λ f f! → reduce-factor-sub-fwd sub f v e sub! f!) fs fs!)

  elim-with-sub-bwd : {n : ℕ} (sub : Sub n) (fs : List (Factor (suc n)))
    → (v : ℕ) (e : Vec ℕ n)
    → ⟦ iSub sub ⟧ₐ (v ∷ e)
    → ⟦ P.i (elim-with-sub sub fs) ⟧ e
    → ⟦ P.i fs ⟧ (v ∷ e)
  elim-with-sub-bwd sub fs v e sub! fs′! = map-bwd (v ∷ e) e (reduce-factor-sub sub) (λ f f! → reduce-factor-sub-bwd sub f v e sub! f!)
    fs (proj₂ (P.++-bwd (ineqs sub) (map (reduce-factor-sub sub) fs) e fs′!))



  reduce-factor-nosubs-fwd : {n : ℕ} (f : Factor (suc n)) (¬fsub : ¬ SubFactor f)
    (v : ℕ) (e : Vec ℕ n)
    → ⟦ F.i f ⟧ (v ∷ e)
    → ⟦ F.i (reduce-factor-nosubs f ¬fsub) ⟧ e
  reduce-factor-nosubs-fwd (+ (S a x == S b y)) ¬sub v e f! with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = shift′ {a} {b} v zero (sandwich (dep₀-term-eval a x x0 v e) (dep₀-term-eval b y y0 v e) f!)
  ... | yes x0 | no ¬y0 = contradiction (inj₁ (x0 , ¬y0)) ¬sub
  ... | no ¬x0 | yes y0 = contradiction (inj₂ (¬x0 , y0)) ¬sub
  ... | no ¬x0 | no ¬y0 = sandwich (ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 v e) ((ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 v e)) f!
  reduce-factor-nosubs-fwd (- (S a x == S b y)) ¬sub v e f! with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = f! ∘ sandwich (sym (dep₀-term-eval a x x0 v e)) (sym (dep₀-term-eval b y y0 v e)) ∘ shift′ {a} {b} zero v
  ... | yes x0 | no ¬y0 = refl
  ... | no ¬x0 | yes y0 = refl
  ... | no ¬x0 | no ¬y0 = f! ∘ sandwich (sym (ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 v e)) (sym (ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 v e))


  ≡-≤ : {a b : ℕ} → a ≡ b → a ≤ b
  ≡-≤ {a} eq = subst (_≤_ a) eq ≤-refl

  a+b∸a=b : (a b : ℕ) → a + b ∸ a ≡ b
  a+b∸a=b zero b = refl
  a+b∸a=b (suc a) b = a+b∸a=b a b

  subtr-helper : ℕ → ℕ → List ℕ
  subtr-helper b a with a ≤? b
  ... | yes _ = [ b ∸ a ]
  ... | no  _ = []

  forbidden-helper : {n : ℕ} → Vec ℕ n → ℕ → (t : Term (suc n)) → ¬ T.dep₀ t → List ℕ
  forbidden-helper e a (S b y) ¬y0 = subtr-helper (⟦ T.ξ⁻¹ (S b y) ¬y0 ⟧ₜ e) a

  -- We could also define this only for non-subfactors.
  forbidden : {n : ℕ} → Vec ℕ n → Factor (suc n) → List ℕ
  forbidden e (+ _) = []
  forbidden e (- (S a x == S b y)) with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = []
  ... | yes x0 | no ¬y0 = forbidden-helper e a (S b y) ¬y0
  ... | no ¬x0 | yes y0 = forbidden-helper e b (S a x) ¬x0
  ... | no ¬x0 | no ¬y0 = []

  forbidden-lemma : {n : ℕ} (a b : ℕ) (y : Base (suc n)) (¬y0 : ¬ B.dep₀ y)
    (v : ℕ) (e : Vec ℕ n)
    → (a + v ≡ b + ⟦ y ⟧b (v ∷ e))
    → v ∈ forbidden-helper e a (S b y) ¬y0
  forbidden-lemma a b y ¬y0 v e eq with a ≤? (b + ⟦ B.ξ⁻¹ y ¬y0 ⟧b e)
  ... | yes a≤b+y = subst (λ z → z ∈ [ (b + ⟦ B.ξ⁻¹ y ¬y0 ⟧b e) ∸ a ])
    (begin
      b + ⟦ B.ξ⁻¹ y ¬y0 ⟧b e ∸ a
    ≡⟨ cong (λ z → b + z ∸ a) (sym (ξ⁻¹-⟦⟧b y ¬y0 v e)) ⟩
      b + ⟦ y ⟧b (v ∷ e) ∸ a
    ≡⟨ cong (λ z → z ∸ a) (sym eq) ⟩
      a + v ∸ a
    ≡⟨ a+b∸a=b a v ⟩
      v
    ∎ )(here [])
  ... | no  a≰b+y = contradiction (a+k≤b⇒a≤b {v} {a} {⟦ T.ξ⁻¹ (S b y) ¬y0 ⟧ₜ e} (≡-≤ (trans eq (ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 v e)))) a≰b+y


  reduce-factor-nosubs-bwd : {n : ℕ} (f : Factor (suc n)) (¬fsub : ¬ SubFactor f)
    (v : ℕ) (e : Vec ℕ n)
    → ⟦ F.i (reduce-factor-nosubs f ¬fsub) ⟧ e
    → (⟦ F.i f ⟧ (v ∷ e)) ⊎ (v ∈ forbidden e f)
  reduce-factor-nosubs-bwd (+ (S a x == S b y)) ¬sub v e f! with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = inj₁ ((sandwich (sym (dep₀-term-eval a x x0 v e)) (sym (dep₀-term-eval b y y0 v e)) ∘ shift′ {a} {b} zero v) f!)
  ... | yes x0 | no ¬y0 = contradiction (inj₁ (x0 , ¬y0)) ¬sub
  ... | no ¬x0 | yes y0 = contradiction (inj₂ (¬x0 , y0)) ¬sub
  ... | no ¬x0 | no ¬y0 = inj₁ (sandwich (sym (ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 v e)) (sym ((ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 v e))) f!)
  reduce-factor-nosubs-bwd (- (S a x == S b y)) ¬sub v e f! with B.dep₀? x | B.dep₀? y
  ... | yes x0 | yes y0 = inj₁ (f! ∘ shift′ {a} {b} v zero ∘ sandwich (dep₀-term-eval a x x0 v e) (dep₀-term-eval b y y0 v e))
  ... | yes x0 | no ¬y0 = either-way
    (inj₂ ∘ forbidden-lemma a b y ¬y0 v e)
    (λ f → inj₁ (f ∘ trans (cong (_+_ a) (sym (dep₀-base-eval x x0 v e)))))
    (a + v ≟ b + ⟦ y ⟧b (v ∷ e))
  ... | no ¬x0 | yes y0 = either-way
    (inj₂ ∘ forbidden-lemma b a x ¬x0 v e)
    (λ f → inj₁ (f ∘ trans (cong (_+_ b)  (sym (dep₀-base-eval y y0 v e))) ∘ sym))
    (b + v ≟ a + ⟦ x ⟧b (v ∷ e))
  ... | no ¬x0 | no ¬y0 = inj₁ (f! ∘ sandwich (ξ⁻¹-⟦⟧ₜ (S a x) ¬x0 v e) (ξ⁻¹-⟦⟧ₜ (S b y) ¬y0 v e))

  elim-nosubs-fwd : {n : ℕ} (fs : List (Factor (suc n))) (¬subs : allP (¬_ ∘ SubFactor) fs)
    (v : ℕ) (e : Vec ℕ n)
    → ⟦ P.i fs ⟧ (v ∷ e)
    → ⟦ P.i (mapWithP reduce-factor-nosubs fs ¬subs) ⟧ e
  elim-nosubs-fwd [] _ _ _ = id
  elim-nosubs-fwd (f ∷ fs) (¬fsub , ¬subs) v e = Data.Product.map (reduce-factor-nosubs-fwd f ¬fsub v e) (elim-nosubs-fwd fs ¬subs v e)

  forbiddens : {n : ℕ} → Vec ℕ n → List (Factor (suc n)) → List ℕ
  forbiddens e [] = []
  forbiddens e (f ∷ fs) = forbidden e f ++ forbiddens e fs

  elim-nosubs-bwd : {n : ℕ} (fs : List (Factor (suc n))) (¬subs : allP (¬_ ∘ SubFactor) fs)
    (v : ℕ) (e : Vec ℕ n)
    → ¬ v ∈ forbiddens e fs
    → ⟦ P.i (mapWithP reduce-factor-nosubs fs ¬subs) ⟧ e
    → ⟦ P.i fs ⟧ (v ∷ e)
  elim-nosubs-bwd [] _ _ _ _ []! = []!
  elim-nosubs-bwd (f ∷ fs) (¬fsub , ¬subs) v e v∉evil (f! , fs!) =
    ( [ id , ⊥-elim ∘ v∉evil ∘ ∈-++₁ (forbidden e f) (forbiddens e fs) ]′ (reduce-factor-nosubs-bwd f ¬fsub v e f!)
    , elim-nosubs-bwd fs ¬subs v e (v∉evil ∘ ∈-++₂ (forbidden e f) (forbiddens e fs)) fs!)

  fresh : List ℕ → ℕ
  fresh = Data.List.foldr (λ x y → either-way (λ _ → suc x) (λ _ → y) (y ≤? x)) zero

  fresh-limit : (xs : List ℕ) → allP (λ y → y < fresh xs) xs
  fresh-limit [] = tt
  fresh-limit (x ∷ xs) with fresh xs ≤? x
  ... | yes fr≤x = (≤-refl , mapAllP (stepup ∘ flip ≤-trans fr≤x) xs (fresh-limit xs))
  ... | no  fr≰x = ( ≰⇒> fr≰x , fresh-limit xs )

  limit-∉ : (z : ℕ) (xs : List ℕ) → allP (λ y → y < z) xs → ¬ z ∈ xs
  limit-∉ _ [] _ ()
  limit-∉ z (.z ∷ .xs) (z<z , _) (here xs) = contradiction refl (<-≢ z<z)
  limit-∉ z (.x ∷ xs) (_ , xs<z) (there x z∈xs) = limit-∉ z xs xs<z z∈xs

  fresh-∉ : (xs : List ℕ) → ¬ (fresh xs) ∈ xs
  fresh-∉ xs = limit-∉ (fresh xs) xs (fresh-limit xs)




  elim-prod-fwd : {n : ℕ} (φ : Prod (suc n))
    → (e : Vec ℕ n)
    → ⟦ E (P.i φ) ⟧ e
    → ⟦ P.i (elim-prod φ) ⟧ e
  elim-prod-fwd fs e (v , fs!) with first SubFactor SubFactor? fs
  ... | inj₁ (f , fsub , f∈fs) = elim-with-sub-fwd (getSub f fsub) fs v e (iSub-getSub f fsub (v ∷ e) (∈-true (v ∷ e) f∈fs fs!)) fs!
  ... | inj₂ none-sub = elim-nosubs-fwd fs none-sub v e fs!

  elim-prod-bwd : {n : ℕ} (φ : Prod (suc n))
    → (e : Vec ℕ n)
    → ⟦ P.i (elim-prod φ) ⟧ e
    → ⟦ E (P.i φ) ⟧ e
  elim-prod-bwd fs e fs′! with first SubFactor SubFactor? fs
  elim-prod-bwd fs e fs′! | inj₁ (f , fsub , f∈fs) with P.++-bwd (ineqs (getSub f fsub)) (map (reduce-factor-sub (getSub f fsub)) fs) e fs′!
  elim-prod-bwd fs e fs′! | inj₁ (f , fsub , f∈fs) | (ineqs! , rest!) with ineqs-bwd (getSub f fsub) e ineqs!
  elim-prod-bwd fs e fs′! | inj₁ (f , fsub , f∈fs) | (ineqs! , rest!) | (v , sub!) = (v , elim-with-sub-bwd (getSub f fsub) fs v e sub! fs′!)
  elim-prod-bwd fs e fs′! | inj₂ none-sub = 
    ( fresh (forbiddens e fs)
    , elim-nosubs-bwd fs none-sub (fresh (forbiddens e fs)) e (fresh-∉ (forbiddens e fs)) fs′! )


  sn-prod-qe : ProdQE
  sn-prod-qe = record
    { elim  = P.i ∘ elim-prod
    ; qfree = P.qf ∘ elim-prod
    ; equiv = λ φ e → (elim-prod-fwd φ e , elim-prod-bwd φ e)
    }

  sn-qe : QE
  sn-qe = lift-prod-qe sn-prod-qe

  open WithQE sn-qe public
