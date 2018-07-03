open import QElim
open import Boiler
open import Data.Vec using (Vec ; [] ; _∷_)
import Data.Sum
import Data.Product
module Sum = Data.Sum
module Product = Data.Product


-- Warning: Ugly code

module QEDNF (da : DecAtom) where

  open WithDecAtom da
  open DecAtom da

  ⇒-disj-fwd : {n : ℕ} (p₁ p₂ : Prop n) (qf₁ : QFree p₁) (e : Vec Y n) → ⟦ p₁ ⇒ p₂ ⟧ e → ⟦ (~ p₁) ∨ p₂ ⟧ e
  ⇒-disj-fwd p₁ p₂ qf₁ e f with qfree-dec p₁ qf₁ e
  ... | yes ⟦p₁⟧ = inj₂ (f ⟦p₁⟧)
  ... | no ¬⟦p₁⟧ = inj₁ ¬⟦p₁⟧

  ⇒-disj-bwd : {n : ℕ} (p₁ p₂ : Prop n) (e : Vec Y n) → ⟦ (~ p₁) ∨ p₂ ⟧ e → ⟦ p₁ ⇒ p₂ ⟧ e
  ⇒-disj-bwd p₁ p₂ e (inj₁ ¬⟦p₁⟧) = λ ⟦p₁⟧ → contradiction ⟦p₁⟧ ¬⟦p₁⟧
  ⇒-disj-bwd p₁ p₂ e (inj₂ ⟦p₂⟧) = λ _ → ⟦p₂⟧
  

  module WithTrue (trueₐ : {n : ℕ} → Atom n) (⟦trueₐ⟧ : {n : ℕ} (e : Vec Y n) → ⟦ trueₐ ⟧ₐ e) where

    true : {n : ℕ} → Prop n
    true = ⊥⊥ ⇒ ⊥⊥

    ⟦true⟧ : {n : ℕ} (e : Vec Y n) → ⟦ true ⟧ e
    ⟦true⟧ e = id

    false : {n : ℕ} → Prop n
    false = ⊥⊥

    ¬⟦false⟧ : {n : ℕ} (e : Vec Y n) → ¬ ⟦ false ⟧ e
    ¬⟦false⟧ e = λ ()

    data Factor : ℕ → Set where
      +_ : {n : ℕ} → Atom n → Factor n
      -_ : {n : ℕ} → Atom n → Factor n

    -- Product of factors
    Prod : ℕ → Set
    Prod n = List (Factor n)

    -- Sum of factors
    Sum : ℕ → Set
    Sum n = List (Factor n)

    -- DNF
    DNF : ℕ → Set
    DNF n = List (Prod n)

    -- CNF
    CNF : ℕ → Set
    CNF n = List (Sum n)

    module F where
      i : {n : ℕ} → Factor n → Prop n
      i (+ a) = atom a
      i (- a) = ~ (atom a)
      neg : {n : ℕ} → Factor n → Factor n
      neg (+ a) = (- a)
      neg (- a) = (+ a)
      qf : {n : ℕ} (f : Factor n) → QFree (i f)
      qf (+ a) = atom a
      qf (- a) = ~-qf (atom a)
      
    module P where
      i : {n : ℕ} → Prod n → Prop n
      i [] = true
      i (f ∷ fs) = (F.i f) ∧ (i fs)
      qf : {n : ℕ} (p : Prod n) → QFree (i p)
      qf [] = ⊥⊥ ⇒ ⊥⊥
      qf (f ∷ fs) = (F.qf f) ∧ (qf fs)
      ++-fwd : {n : ℕ} (p₁ p₂ : Prod n) (e : Vec Y n) → ⟦ (i p₁) ∧ (i p₂) ⟧ e → ⟦ i (p₁ ++ p₂) ⟧ e
      ++-fwd [] p₂ e (_ , ⟦p₂⟧) = ⟦p₂⟧
      ++-fwd (f ∷ fs) p₂ e ((⟦f⟧ , ⟦fs⟧) , ⟦p₂⟧) = (⟦f⟧ , ++-fwd fs p₂ e (⟦fs⟧ , ⟦p₂⟧))
      ++-bwd : {n : ℕ} (p₁ p₂ : Prod n) (e : Vec Y n) → ⟦ i (p₁ ++ p₂) ⟧ e → ⟦ (i p₁) ∧ (i p₂) ⟧ e
      ++-bwd [] p₂ e ⟦p₂⟧ = (⟦true⟧ e , ⟦p₂⟧)
      ++-bwd (f ∷ fs) p₂ e (⟦f⟧ , ⟦rest⟧) = Product.map (λ ⟦fs⟧ → (⟦f⟧ , ⟦fs⟧)) id (++-bwd fs p₂ e ⟦rest⟧)

    module S where
      i : {n : ℕ} → Sum n → Prop n
      i [] = false
      i (f ∷ fs) = (F.i f) ∨ (i fs)
      qf : {n : ℕ} (s : Sum n) → QFree (i s)
      qf [] = ⊥⊥
      qf (f ∷ fs) = (F.qf f) ∨ (qf fs)
      ++-fwd : {n : ℕ} (p₁ p₂ : Prod n) (e : Vec Y n) → ⟦ (i p₁) ∨ (i p₂) ⟧ e → ⟦ i (p₁ ++ p₂) ⟧ e
      ++-fwd [] p₂ e (inj₁ false) = contradiction false (¬⟦false⟧ e)
      ++-fwd [] p₂ e (inj₂ ⟦p₂⟧) = ⟦p₂⟧
      ++-fwd (f ∷ fs) p₂ e (inj₁ (inj₁ ⟦f⟧)) = inj₁ ⟦f⟧
      ++-fwd (f ∷ fs) p₂ e (inj₁ (inj₂ ⟦fs⟧)) = inj₂ (++-fwd fs p₂ e (inj₁ ⟦fs⟧))
      ++-fwd (f ∷ fs) p₂ e (inj₂ ⟦p₂⟧) = inj₂ (++-fwd fs p₂ e (inj₂ ⟦p₂⟧))
      ++-bwd : {n : ℕ} (p₁ p₂ : Prod n) (e : Vec Y n) → ⟦ i (p₁ ++ p₂) ⟧ e → ⟦ (i p₁) ∨ (i p₂) ⟧ e
      ++-bwd [] p₂ e ⟦p₂⟧ = inj₂ ⟦p₂⟧
      ++-bwd (f ∷ fs) p₂ e (inj₁ ⟦f⟧) = inj₁ (inj₁ ⟦f⟧)
      ++-bwd (f ∷ fs) p₂ e (inj₂ ⟦rest⟧) = Sum.map inj₂ id (++-bwd fs p₂ e ⟦rest⟧)

    module D where
      i : {n : ℕ} → DNF n → Prop n
      i [] = false
      i (p ∷ ps) = (P.i p) ∨ (i ps)
      qf : {n : ℕ} (d : DNF n) → QFree (i d)
      qf [] = ⊥⊥
      qf (p ∷ ps) = (P.qf p) ∨ (qf ps)

    module C where
      i : {n : ℕ} → CNF n → Prop n
      i [] = true
      i (s ∷ ss) = (S.i s) ∧ (i ss)
      qf : {n : ℕ} (c : CNF n) → QFree (i c)
      qf [] = ⊥⊥ ⇒ ⊥⊥
      qf (s ∷ ss) = (S.qf s) ∧ (qf ss)


    module NFMess where
    
      -- Negates a Sum/Prod into a Prod/Sum
      -- Ex: A ∧ B ---> ¬A ∨ ¬B
      -- Ex: A ∨ B ---> ¬A ∧ ¬B
      dual₁ : {n : ℕ} → List (Factor n) → List (Factor n)
      dual₁ = map F.neg

      -- Negates a DNF/CNF into a CNF/DNF.
      -- Ex: (A ∧ B) v (C ∧ D) --->  (¬A v ¬B) ∧ (¬C v ¬D)
      -- Ex: (A v B) ∧ (C v D) --->  (¬A ∧ ¬B) v (¬C ∧ ¬D)
      dual₂ : {n : ℕ} → List (List (Factor n)) → List (List (Factor n))
      dual₂ = map dual₁

      -- Lemma about ++ on DNF/CNF
      dnf-++-fwd : {n : ℕ} (x y : DNF n) (e : Vec Y n) → ⟦ (D.i x) ∨ (D.i y) ⟧ e → ⟦ D.i (x ++ y) ⟧ e
      dnf-++-fwd [] y e (inj₁ ⟦f⟧) = contradiction ⟦f⟧ (¬⟦false⟧ e)
      dnf-++-fwd [] y e (inj₂ ⟦y⟧) = ⟦y⟧
      dnf-++-fwd (x ∷ xs) y e (inj₁ (inj₁ ⟦x⟧)) = inj₁ ⟦x⟧
      dnf-++-fwd (x ∷ xs) y e (inj₁ (inj₂ ⟦xs⟧)) = inj₂ (dnf-++-fwd xs y e (inj₁ ⟦xs⟧))
      dnf-++-fwd (x ∷ xs) y e (inj₂ ⟦y⟧) = inj₂ (dnf-++-fwd xs y e (inj₂ ⟦y⟧))

      cnf-++-fwd : {n : ℕ} (x y : CNF n) (e : Vec Y n) → ⟦ (C.i x) ∧ (C.i y) ⟧ e → ⟦ C.i (x ++ y) ⟧ e
      cnf-++-fwd [] y e (_ , ⟦y⟧) = ⟦y⟧
      cnf-++-fwd (x ∷ xs) y e ((⟦x⟧ , ⟦xs⟧) , ⟦y⟧) = ⟦x⟧ , cnf-++-fwd xs y e (⟦xs⟧ , ⟦y⟧)

      dnf-++-bwd : {n : ℕ} (x y : DNF n) (e : Vec Y n) → ⟦ D.i (x ++ y) ⟧ e → ⟦ (D.i x) ∨ (D.i y) ⟧ e
      dnf-++-bwd [] y e ⟦y⟧ = inj₂ ⟦y⟧
      dnf-++-bwd (x ∷ xs) y e (inj₁ ⟦x⟧) = inj₁ (inj₁ ⟦x⟧)
      dnf-++-bwd (x ∷ xs) y e (inj₂ s) = Sum.map inj₂ id (dnf-++-bwd xs y e s)

      cnf-++-bwd : {n : ℕ} (x y : CNF n) (e : Vec Y n) → ⟦ C.i (x ++ y) ⟧ e → ⟦ (C.i x) ∧ (C.i y) ⟧ e
      cnf-++-bwd [] y e ⟦y⟧ = (⟦true⟧ e , ⟦y⟧)
      cnf-++-bwd (x ∷ xs) y e (⟦x⟧ , ⟦rest⟧) = Product.map (λ ⟦xs⟧ → (⟦x⟧ , ⟦xs⟧)) id (cnf-++-bwd xs y e ⟦rest⟧)


      -- Lemma about F.neg
      neg-fwd : {n : ℕ} (x : Factor n) (e : Vec Y n) → ¬ ⟦ F.i x ⟧ e → ⟦ F.i (F.neg x) ⟧ e
      neg-fwd (+ a) e ¬⟦a⟧ = ¬⟦a⟧
      neg-fwd (- a) e ¬¬⟦a⟧ = qfree-¬¬ (atom a) (atom a) e ¬¬⟦a⟧

      neg-bwd : {n : ℕ} (x : Factor n) (e : Vec Y n) → ⟦ F.i (F.neg x) ⟧ e → ¬ ⟦ F.i x ⟧ e
      neg-bwd (+ a) e ¬⟦a⟧ = ¬⟦a⟧
      neg-bwd (- a) e ⟦a⟧ = ¬¬-intro ⟦a⟧


      -- As ∧ (Bs v Cs v ...) --> (As ∧ Bs) v (As ∧ Cs) v ...
      -- As v (Bs ∧ Cs ∧ ...) --> (As v Bs) ∧ (As v Cs) ∧ ...
      pairup : {A : Set} → List A → List (List A) → List (List A)
      pairup x [] = []
      pairup x (y ∷ ys) = (x ++ y) ∷ pairup x ys

      pairup-dnf-fwd : {n : ℕ} (p : Prod n) (xs : DNF n) (e : Vec Y n) → ⟦ (P.i p) ∧ (D.i xs) ⟧ e → ⟦ D.i (pairup p xs) ⟧ e
      pairup-dnf-fwd p [] e (_ , false) = contradiction false (¬⟦false⟧ e)
      pairup-dnf-fwd p (x ∷ xs) e (⟦p⟧ , inj₁ ⟦x⟧) = inj₁ (P.++-fwd p x e (⟦p⟧ , ⟦x⟧))
      pairup-dnf-fwd p (x ∷ xs) e (⟦p⟧ , inj₂ ⟦xs⟧) = inj₂ (pairup-dnf-fwd p xs e (⟦p⟧ , ⟦xs⟧))

      pairup-dnf-bwd : {n : ℕ} (p : Prod n) (xs : DNF n) (e : Vec Y n) → ⟦ D.i (pairup p xs) ⟧ e → ⟦ (P.i p) ∧ (D.i xs) ⟧ e
      pairup-dnf-bwd p [] e false = contradiction false (¬⟦false⟧ e)
      pairup-dnf-bwd p (x ∷ xs) e (inj₁ ⟦p++x⟧) = Product.map id inj₁ (P.++-bwd p x e ⟦p++x⟧)
      pairup-dnf-bwd p (x ∷ xs) e (inj₂ ⟦rest⟧) = Product.map id inj₂ (pairup-dnf-bwd p xs e ⟦rest⟧)

      pairup-cnf-fwd : {n : ℕ} (s : Sum n) (xs : CNF n) (e : Vec Y n) → ⟦ (S.i s) ∨ (C.i xs) ⟧ e → ⟦ C.i (pairup s xs) ⟧ e
      pairup-cnf-fwd s [] e _ = ⟦true⟧ e
      pairup-cnf-fwd s (x ∷ xs) e (inj₁ ⟦s⟧) = (S.++-fwd s x e (inj₁ ⟦s⟧) , pairup-cnf-fwd s xs e (inj₁ ⟦s⟧))
      pairup-cnf-fwd s (x ∷ xs) e (inj₂ (⟦x⟧ , ⟦xs⟧)) = ( S.++-fwd s x e (inj₂ ⟦x⟧) , pairup-cnf-fwd s xs e (inj₂ ⟦xs⟧))

      pairup-cnf-bwd : {n : ℕ} (s : Sum n) (xs : CNF n) (e : Vec Y n) → ⟦ C.i (pairup s xs) ⟧ e → ⟦ (S.i s) ∨ (C.i xs) ⟧ e
      pairup-cnf-bwd s [] e _ = inj₂ (⟦true⟧ e)
      pairup-cnf-bwd s (x ∷ xs) e (⟦s++x⟧ , ⟦rest⟧) = [ inj₁ , (λ ⟦x⟧ → Sum.map id (λ ⟦xs⟧ → (⟦x⟧ , ⟦xs⟧)) (pairup-cnf-bwd s xs e ⟦rest⟧)) ]′ (S.++-bwd s x e ⟦s++x⟧)

      -- (As v Bs v Cs) ∧ (Ds v Es v Fs) --> (As ∧ Ds) v (As ∧ Es) v ... (Cs ∧ Fs)
      -- (As ∧ Bs ∧ Cs) v (Ds ∧ Es ∧ Fs) --> (As v Ds) ∧ (As v Es) ∧ ... (Cs v Fs)
      mix : {A : Set} → List (List A) → List (List A) → List (List A)
      mix [] _ = []
      mix (x ∷ xs) ys = (pairup x ys) ++ (mix xs ys)


      -- Lemma about mix
      mix-dnf-fwd : {n : ℕ} (xs ys : DNF n) (e : Vec Y n) → ⟦ (D.i xs) ∧ (D.i ys) ⟧ e → ⟦ D.i (mix xs ys) ⟧ e
      mix-dnf-fwd [] _ e (false , _) = contradiction false (¬⟦false⟧ e)
      mix-dnf-fwd (x ∷ xs) ys e (⟦x∷xs⟧ , ⟦ys⟧) = dnf-++-fwd (pairup x ys) (mix xs ys) e (Sum.map (λ ⟦x⟧ → pairup-dnf-fwd x ys e (⟦x⟧ , ⟦ys⟧)) (λ ⟦xs⟧ → mix-dnf-fwd xs ys e (⟦xs⟧ , ⟦ys⟧)) ⟦x∷xs⟧)

      mix-cnf-fwd : {n : ℕ} (xs ys : CNF n) (e : Vec Y n) → ⟦ (C.i xs) ∨ (C.i ys) ⟧ e → ⟦ C.i (mix xs ys) ⟧ e
      mix-cnf-fwd [] _ e _ = ⟦true⟧ e
      mix-cnf-fwd (x ∷ xs) ys e (inj₁ (⟦x⟧ , ⟦xs⟧)) = cnf-++-fwd (pairup x ys) (mix xs ys) e (pairup-cnf-fwd x ys e (inj₁ ⟦x⟧) , mix-cnf-fwd xs ys e (inj₁ ⟦xs⟧))
      mix-cnf-fwd (x ∷ xs) ys e (inj₂ ⟦ys⟧) =         cnf-++-fwd (pairup x ys) (mix xs ys) e (pairup-cnf-fwd x ys e (inj₂ ⟦ys⟧) , mix-cnf-fwd xs ys e (inj₂ ⟦ys⟧))

      mix-dnf-bwd : {n : ℕ} (xs ys : DNF n) (e : Vec Y n) → ⟦ D.i (mix xs ys) ⟧ e → ⟦ (D.i xs) ∧ (D.i ys) ⟧ e
      mix-dnf-bwd [] _ e false = contradiction false (¬⟦false⟧ e)
      mix-dnf-bwd (x ∷ xs) ys e ⟦⟧ = [ Product.map inj₁ id ∘ pairup-dnf-bwd x ys e , Product.map inj₂ id ∘ mix-dnf-bwd xs ys e ]′ (dnf-++-bwd (pairup x ys) (mix xs ys) e ⟦⟧)

      mix-cnf-bwd : {n : ℕ} (xs ys : CNF n) (e : Vec Y n) → ⟦ C.i (mix xs ys) ⟧ e → ⟦ (C.i xs) ∨ (C.i ys) ⟧ e
      mix-cnf-bwd [] _ e _ = inj₁ (⟦true⟧ e)
      mix-cnf-bwd (x ∷ xs) ys e ⟦⟧ = (λ pair → [ (λ ⟦x⟧ → Sum.map (λ ⟦xs⟧ → ⟦x⟧ , ⟦xs⟧) id (mix-cnf-bwd xs ys e (proj₂ pair))) , inj₂ ]′ (pairup-cnf-bwd x ys e (proj₁ pair))) (cnf-++-bwd (pairup x ys) (mix xs ys) e ⟦⟧)





      -- Lemma about dual₁
      dual₁-sum-fwd : {n : ℕ} (x : Sum n) (e : Vec Y n) → ¬ ⟦ S.i x ⟧ e → ⟦ P.i (dual₁ x) ⟧ e
      dual₁-sum-fwd [] e _ = ⟦true⟧ e
      dual₁-sum-fwd (x ∷ xs) e f with qfree-dec (F.i x) (F.qf x) e
      ... | yes ⟦x⟧ = contradiction (inj₁ ⟦x⟧) f
      ... | no ¬⟦x⟧ = (neg-fwd x e ¬⟦x⟧ , dual₁-sum-fwd xs e (f ∘ inj₂))

      dual₁-prod-fwd : {n : ℕ} (x : Prod n) (e : Vec Y n) → ¬ ⟦ P.i x ⟧ e → ⟦ S.i (dual₁ x) ⟧ e
      dual₁-prod-fwd [] e false = contradiction (⟦true⟧ e) false
      dual₁-prod-fwd (x ∷ xs) e f with qfree-dec (F.i x) (F.qf x) e
      ... | yes ⟦x⟧ = inj₂ (dual₁-prod-fwd xs e (λ ⟦xs⟧ → f (⟦x⟧ , ⟦xs⟧)))
      ... | no ¬⟦x⟧ = inj₁ (neg-fwd x e ¬⟦x⟧)

      dual₁-sum-bwd : {n : ℕ} (x : Sum n) (e : Vec Y n) → ⟦ P.i (dual₁ x) ⟧ e → ¬ ⟦ S.i x ⟧ e
      dual₁-sum-bwd [] e _ = ¬⟦false⟧ e
      dual₁-sum-bwd (x ∷ xs) e (⟦x'⟧ , ⟦xs'⟧) = [ neg-bwd x e ⟦x'⟧ , dual₁-sum-bwd xs e ⟦xs'⟧ ]′

      dual₁-prod-bwd : {n : ℕ} (x : Prod n) (e : Vec Y n) → ⟦ S.i (dual₁ x) ⟧ e → ¬ ⟦ P.i x ⟧ e
      dual₁-prod-bwd [] e false = contradiction false (¬⟦false⟧ e)
      dual₁-prod-bwd (x ∷ xs) e (inj₁ ⟦x'⟧) = neg-bwd x e ⟦x'⟧ ∘ proj₁
      dual₁-prod-bwd (x ∷ xs) e (inj₂ ⟦xs'⟧) = dual₁-prod-bwd xs e ⟦xs'⟧ ∘ proj₂

      -- Lemma about dual₂
      dual₂-cnf-fwd : {n : ℕ} (x : CNF n) (e : Vec Y n) → ¬ ⟦ C.i x ⟧ e → ⟦ D.i (dual₂ x) ⟧ e
      dual₂-cnf-fwd [] e ¬true = contradiction (⟦true⟧ e) ¬true
      dual₂-cnf-fwd (s ∷ ss) e ¬⟦x⟧ with qfree-dec (S.i s) (S.qf s) e
      ... | yes ⟦s⟧ = inj₂ (dual₂-cnf-fwd ss e (λ ⟦ss⟧ → ¬⟦x⟧ (⟦s⟧ , ⟦ss⟧)))
      ... | no ¬⟦s⟧ = inj₁ (dual₁-sum-fwd s e ¬⟦s⟧)

      dual₂-dnf-fwd : {n : ℕ} (x : DNF n) (e : Vec Y n) → ¬ ⟦ D.i x ⟧ e → ⟦ C.i (dual₂ x) ⟧ e
      dual₂-dnf-fwd [] e _ = ⟦true⟧ e
      dual₂-dnf-fwd (p ∷ ps) e ¬⟦x⟧ with qfree-dec (P.i p) (P.qf p) e
      ... | yes ⟦p⟧ = contradiction (inj₁ ⟦p⟧) ¬⟦x⟧
      ... | no ¬⟦p⟧ = (dual₁-prod-fwd p e ¬⟦p⟧ , dual₂-dnf-fwd ps e (¬⟦x⟧ ∘ inj₂))

      dual₂-cnf-bwd : {n : ℕ} (x : CNF n) (e : Vec Y n) → ⟦ D.i (dual₂ x) ⟧ e → ¬ ⟦ C.i x ⟧ e
      dual₂-cnf-bwd [] e false = contradiction false (¬⟦false⟧ e)
      dual₂-cnf-bwd (s ∷ ss) e (inj₁ ⟦s'⟧)  = dual₁-sum-bwd s e ⟦s'⟧ ∘ proj₁
      dual₂-cnf-bwd (s ∷ ss) e (inj₂ ⟦ss'⟧) = dual₂-cnf-bwd ss e ⟦ss'⟧ ∘ proj₂

      dual₂-dnf-bwd : {n : ℕ} (x : DNF n) (e : Vec Y n) → ⟦ C.i (dual₂ x) ⟧ e → ¬ ⟦ D.i x ⟧ e
      dual₂-dnf-bwd [] e _ = ¬⟦false⟧ e
      dual₂-dnf-bwd (p ∷ ps) e (⟦p'⟧ , ⟦ps'⟧) = [ dual₁-prod-bwd p e ⟦p'⟧ , dual₂-dnf-bwd ps e ⟦ps'⟧ ]′

    open NFMess

    -- DNF/CNF procedures
    dnf : {n : ℕ} (p : Prop n) (qf : QFree p) → DNF n
    cnf : {n : ℕ} (p : Prop n) (qf : QFree p) → CNF n
    
    dnf _ ⊥⊥ = []
    dnf .(atom a) (atom a) = [ [ + a ] ]
    dnf (p₁ ∨ p₂) (qf₁ ∨ qf₂) = dnf p₁ qf₁ ++ dnf p₂ qf₂
    dnf (p₁ ∧ p₂) (qf₁ ∧ qf₂) = mix (dnf p₁ qf₁) (dnf p₂ qf₂)
    dnf (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) = (dual₂ (cnf p₁ qf₁)) ++ (dnf p₂ qf₂)

    cnf _ ⊥⊥ = [ [] ]
    cnf .(atom a) (atom a) = [ [ + a ] ]
    cnf (p₁ ∨ p₂) (qf₁ ∨ qf₂) = mix (cnf p₁ qf₁) (cnf p₂ qf₂)
    cnf (p₁ ∧ p₂) (qf₁ ∧ qf₂) = cnf p₁ qf₁ ++ cnf p₂ qf₂
    cnf (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) = mix (dual₂ (dnf p₁ qf₁)) (cnf p₂ qf₂)


    -- DNF/CNF correctness
    dnf-fwd : {n : ℕ} (p : Prop n) (qf : QFree p) (e : Vec Y n) → ⟦ p ⟧ e → ⟦ D.i (dnf p qf) ⟧ e
    dnf-bwd : {n : ℕ} (p : Prop n) (qf : QFree p) (e : Vec Y n) → ⟦ D.i (dnf p qf) ⟧ e → ⟦ p ⟧ e
    cnf-fwd : {n : ℕ} (p : Prop n) (qf : QFree p) (e : Vec Y n) → ⟦ p ⟧ e → ⟦ C.i (cnf p qf) ⟧ e
    cnf-bwd : {n : ℕ} (p : Prop n) (qf : QFree p) (e : Vec Y n) → ⟦ C.i (cnf p qf) ⟧ e → ⟦ p ⟧ e

    dnf-fwd _ ⊥⊥ e = λ ()
    dnf-fwd .(atom a) (atom a) e = λ x → inj₁ (x , ⟦true⟧ e)
    dnf-fwd (p₁ ∨ p₂) (qf₁ ∨ qf₂) e = dnf-++-fwd (dnf p₁ qf₁) (dnf p₂ qf₂) e ∘ (Sum.map (dnf-fwd p₁ qf₁ e) (dnf-fwd p₂ qf₂ e))
    dnf-fwd (p₁ ∧ p₂) (qf₁ ∧ qf₂) e = mix-dnf-fwd (dnf p₁ qf₁) (dnf p₂ qf₂) e ∘ Product.map (dnf-fwd p₁ qf₁ e) (dnf-fwd p₂ qf₂ e)
    dnf-fwd (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) e = dnf-++-fwd (dual₂ (cnf p₁ qf₁)) (dnf p₂ qf₂) e ∘ Sum.map (dual₂-cnf-fwd (cnf p₁ qf₁) e ∘ contraposition (cnf-bwd p₁ qf₁ e)) (dnf-fwd p₂ qf₂ e) ∘ ⇒-disj-fwd p₁ p₂ qf₁ e

    cnf-fwd _ ⊥⊥ e = λ ()
    cnf-fwd .(atom a) (atom a) e = λ x → (inj₁ x , ⟦true⟧ e)
    cnf-fwd (p₁ ∨ p₂) (qf₁ ∨ qf₂) e = mix-cnf-fwd (cnf p₁ qf₁) (cnf p₂ qf₂) e ∘ Sum.map (cnf-fwd p₁ qf₁ e) (cnf-fwd p₂ qf₂ e)
    cnf-fwd (p₁ ∧ p₂) (qf₁ ∧ qf₂) e = cnf-++-fwd (cnf p₁ qf₁) (cnf p₂ qf₂) e ∘ (Product.map (cnf-fwd p₁ qf₁ e) (cnf-fwd p₂ qf₂ e))
    cnf-fwd (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) e = mix-cnf-fwd (dual₂ (dnf p₁ qf₁)) (cnf p₂ qf₂) e ∘ Sum.map (dual₂-dnf-fwd (dnf p₁ qf₁) e ∘ contraposition (dnf-bwd p₁ qf₁ e)) (cnf-fwd p₂ qf₂ e) ∘ ⇒-disj-fwd p₁ p₂ qf₁ e

    dnf-bwd .⊥⊥ ⊥⊥ e = λ ()
    dnf-bwd .(atom a) (atom a) e = [ proj₁ , ⊥-elim ∘ (¬⟦false⟧ e) ]′
    dnf-bwd (p₁ ∨ p₂) (qf₁ ∨ qf₂) e = (Sum.map (dnf-bwd p₁ qf₁ e) (dnf-bwd p₂ qf₂ e)) ∘ dnf-++-bwd (dnf p₁ qf₁) (dnf p₂ qf₂) e
    dnf-bwd (p₁ ∧ p₂) (qf₁ ∧ qf₂) e = Product.map (dnf-bwd p₁ qf₁ e) (dnf-bwd p₂ qf₂ e) ∘ mix-dnf-bwd (dnf p₁ qf₁) (dnf p₂ qf₂) e
    dnf-bwd (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) e = ⇒-disj-bwd p₁ p₂ e ∘ Sum.map (contraposition (cnf-fwd p₁ qf₁ e) ∘ dual₂-cnf-bwd (cnf p₁ qf₁) e) (dnf-bwd p₂ qf₂ e) ∘ dnf-++-bwd (dual₂ (cnf p₁ qf₁)) (dnf p₂ qf₂) e

    cnf-bwd .⊥⊥ ⊥⊥ e = ⊥-elim ∘ ¬⟦false⟧ e ∘ proj₁
    cnf-bwd .(atom a) (atom a) e = [ id , ⊥-elim ∘ (¬⟦false⟧ e) ]′ ∘ proj₁
    cnf-bwd (p₁ ∨ p₂) (qf₁ ∨ qf₂) e = Sum.map (cnf-bwd p₁ qf₁ e) (cnf-bwd p₂ qf₂ e) ∘ mix-cnf-bwd (cnf p₁ qf₁) (cnf p₂ qf₂) e
    cnf-bwd (p₁ ∧ p₂) (qf₁ ∧ qf₂) e = (Product.map (cnf-bwd p₁ qf₁ e) (cnf-bwd p₂ qf₂ e)) ∘ cnf-++-bwd (cnf p₁ qf₁) (cnf p₂ qf₂) e
    cnf-bwd (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) e = ⇒-disj-bwd p₁ p₂ e ∘ Sum.map (contraposition (dnf-fwd p₁ qf₁ e) ∘ dual₂-dnf-bwd (dnf p₁ qf₁) e) (cnf-bwd p₂ qf₂ e) ∘ mix-cnf-bwd (dual₂ (dnf p₁ qf₁)) (cnf p₂ qf₂) e

    -- Single-step ∃-elim on DNF
    record DNFQE : Set where
      field
        elim  : {n : ℕ} → DNF (suc n) → Prop n
        qfree : {n : ℕ} (φ : DNF (suc n)) → QFree (elim φ)
        equiv : {n : ℕ} (φ : DNF (suc n)) (e : Vec Y n) → ⟦ E (D.i φ) ⟧ e ↔ ⟦ elim φ ⟧ e

    -- Single-step ∃-elim on products of factors
    record ProdQE : Set where
      field
        elim  : {n : ℕ} → Prod (suc n) → Prop n
        qfree : {n : ℕ} (φ : Prod (suc n)) → QFree (elim φ)
        equiv : {n : ℕ} (φ : Prod (suc n)) (e : Vec Y n) → ⟦ E (P.i φ) ⟧ e ↔ ⟦ elim φ ⟧ e

    lift-dnf-qe : DNFQE → QE
    lift-dnf-qe qe = record
      { elim  = λ φ qf → DNFQE.elim qe (dnf φ qf)
      ; qfree = λ φ qf → DNFQE.qfree qe (dnf φ qf)
      ; equiv = λ φ qf e →
                  ( proj₁ (DNFQE.equiv qe (dnf φ qf) e) ∘ Σ-map (λ y → dnf-fwd φ qf (y ∷ e))
                  , Σ-map (λ y → dnf-bwd φ qf (y ∷ e)) ∘ proj₂ (DNFQE.equiv qe (dnf φ qf) e))
      }

    module Prod⇒DNF (qe : ProdQE) where

      elim : {n : ℕ} → DNF (suc n) → Prop n
      elim [] = ⊥⊥
      elim (p ∷ ps) = (ProdQE.elim qe p) ∨ (elim ps)

      qfree : {n : ℕ} (φ : DNF (suc n)) → QFree (elim φ)
      qfree [] = ⊥⊥
      qfree (p ∷ ps) = (ProdQE.qfree qe p) ∨ (qfree ps)

      fwd : {n : ℕ} (φ : DNF (suc n)) (e : Vec Y n) → ⟦ E (D.i φ) ⟧ e → ⟦ elim φ ⟧ e
      fwd [] e (_ , ())
      fwd (p ∷ ps) e (y , inj₁  ⟦p⟧) = inj₁ (proj₁ (ProdQE.equiv qe p e) (y , ⟦p⟧))
      fwd (p ∷ ps) e (y , inj₂ ⟦ps⟧) = inj₂ (fwd ps e (y , ⟦ps⟧))

      bwd : {n : ℕ} (φ : DNF (suc n)) (e : Vec Y n) → ⟦ elim φ ⟧ e → ⟦ E (D.i φ) ⟧ e
      bwd [] e ()
      bwd (p ∷ ps) e (inj₁ ⟦p'⟧)  = Σ-map (λ y → inj₁) (proj₂ (ProdQE.equiv qe p e) ⟦p'⟧)
      bwd (p ∷ ps) e (inj₂ ⟦ps'⟧) = Σ-map (λ y → inj₂) (bwd ps e ⟦ps'⟧)

      lift : DNFQE
      lift = record
        { elim = elim
        ; qfree = qfree
        ; equiv = λ φ e → (fwd φ e , bwd φ e)
        }

    -- ∃-elim on products → ∃-elim on any qfree
    lift-prod-qe : ProdQE → QE
    lift-prod-qe = lift-dnf-qe ∘ Prod⇒DNF.lift
