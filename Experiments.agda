module Experiments where

  open import Boiler
  open import QElim
  open import SN
  open import Data.Nat
  open import Data.Fin renaming (zero to fzero ; suc to fsuc)
  open import Data.Vec
  open import Relation.Nullary
  open import Relation.Nullary.Negation

  open WithDecAtom sn-da

  test₀ : Prop zero
  test₀ = E E (                                          -- ∃x.∃y.
      (atom (S 3 (var (fsuc fzero)) == S 1 (var fzero))) -- 3 + x = 1 + y
    ∧ (atom (S 8 ∅ == S 4 (var fzero)))                  -- 8 = 4 + y
    )

  ⟦test₀⟧? : Dec (⟦ test₀ ⟧ [])
  ⟦test₀⟧? = ⟦ test₀ ⟧? []


  -- ∀x.(x=0 ∨ ∃y.x=y+1)
  test₁ : Prop zero
  test₁ = A ((atom (S 0 (var fzero) == S 0 ∅)) ∨ (E (atom (S 0 (var (fsuc fzero)) == S 1 (var fzero)))))

  ⟦test₁⟧? : Dec (⟦ test₁ ⟧ [])
  ⟦test₁⟧? = ⟦ test₁ ⟧? []


  -- (x = 0) ∨ (∃y.x=y+2)
  test₂ : Prop 1
  test₂ = ((atom (S 0 (var fzero) == S 0 ∅)) ∨ (E (atom (S 0 (var (fsuc fzero)) == S 2 (var fzero)))))


  -- ∀z.(z+3≠x ∨ ∃y.(z=2+y))
  demo : Prop 1
  demo = A (
       (~ (atom (S 3 (var fzero) == S 0 (var (fsuc fzero)))))
       ∨ (E (atom (S 0 (var (fsuc fzero)) == S 2 (var fzero))))
    )

  demo-qe : Prop 1
  demo-qe = lift-qe sn-qe demo
  {-
  -- (  (x≠2 ∧ x≠1 ∧ x≠0 ∧ x+3=x+3 ∧ x=4 ∧ ⊥⇒⊥)
      ∨ (x≠2 ∧ x≠1 ∧ x≠0 ∧ x+3=x+3 ∧ x=3 ∧ ⊥⇒⊥)
      ∨ (x≠2 ∧ x≠1 ∧ x≠0 ∧ x+3=x+3 ∧ 2≠2 ∧ ⊥⇒⊥)
      ∨ ⊥
     ) ⇒ ⊥
  -}

  -- =)
