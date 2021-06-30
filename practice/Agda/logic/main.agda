module logic.main where

open import Data.Bool using (T; not; true; false; Bool; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning 


data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

data prop : Set where
  bot  : prop
  top  : prop
  atom : ℕ → prop
  lnot : prop → prop
  land : prop → prop → prop
  lor  : prop → prop → prop
  to   : prop → prop → prop

infix 9 _⇒_
data _⇒_ : List prop → List prop → Set where
  -- 公理
  LK⊥ : (bot ∷ []) ⇒ []
  LK⊤ : [] ⇒ (top ∷ [])
  LKinit : ∀ {p} → (p ∷ []) ⇒ (p ∷ [])
  -- 構造の推論規則
  LKweakeningL : ∀ {Γ Δ p} → Γ ⇒ Δ → ( p ∷ Γ ) ⇒ Δ
  LKweakeningR : ∀ {Γ Δ p} → Γ ⇒ Δ → Γ ⇒ (p ∷ Δ)
  LKcontractionL : ∀ {Γ Δ p} → (p ∷ p ∷ Γ) ⇒ Δ → (p ∷ Γ) ⇒ Δ
  LKcontractionR : ∀ {Γ Δ p} → Γ ⇒ (p ∷ p ∷ Δ) → Γ ⇒ (p ∷ Δ)
  LKexchangeL : ∀ {Γ Δ p q Π} → (Γ ++ p ∷ q ∷ Π) ⇒ Δ → (Γ ++ q ∷ p ∷ Π) ⇒ Δ
  LKexchangeR : ∀ {Γ Δ p q Π} → Γ ⇒ (Δ ++ p ∷ q ∷ Π) → Γ ⇒ (Δ ++ q ∷ p ∷ Π)
  -- 論理結合子の規則
  LK∧LL : ∀ {Γ Δ p q} → (p ∷ Γ) ⇒ Δ → ( (land p q) ∷ Γ) ⇒ Δ
  LK∧LR : ∀ {Γ Δ p q} → (p ∷ Γ) ⇒ Δ → ( (land q p) ∷ Γ) ⇒ Δ
  LK∧R  : ∀ {Γ Δ p q} → Γ ⇒ (p ∷ Δ) → Γ ⇒ (q ∷ Δ) → Γ ⇒ ((land p q) ∷ Δ)
  LK∨L  : ∀ {Γ Δ p q} → (p ∷ Γ) ⇒ Δ → (q ∷ Γ) ⇒ Δ → ((lor p q) ∷ Γ) ⇒ Δ
  LK∨RL : ∀ {Γ Δ p q} → Γ ⇒ (p ∷ Δ) → Γ ⇒ ((lor p q) ∷ Δ)
  LK∨RR : ∀ {Γ Δ p q} → Γ ⇒ (p ∷ Δ) → Γ ⇒ ((lor q p) ∷ Δ)
  LK→L : ∀ {Γ Δ p q Π Σ} → Γ ⇒ (p ∷ Δ) → (q ∷ Π) ⇒ Σ → ((to p q) ∷ Γ ++ Π) ⇒ (Δ ++ Σ)
  LK→R : ∀ {Γ Δ p q} → (p ∷ Γ) ⇒ (q ∷ Δ) → Γ ⇒ ((to p q) ∷ Δ)
  LK¬L : ∀ {Γ Δ p} → Γ ⇒ (p ∷ Δ) → ((lnot p) ∷ Γ) ⇒ Δ
  LK¬R : ∀ {Γ Δ p} → (p ∷ Γ) ⇒ Δ → Γ ⇒ ((lnot p) ∷ Δ)

_ : ∀ X → [] ⇒ ((lor X (lnot X)) ∷ [])
_ = λ x → LKcontractionR ( LK∨RR (LK¬R ( LK∨RL LKinit )) )


inlist : List ℕ → ℕ → Bool
inlist [] a = false
inlist (h ∷ t) a with h ≟ a
... | yes _ = true
... | no  _ = inlist t a


Bid : List ℕ → prop → Bool
Bid Γ top = true
Bid Γ bot = false
Bid Γ (atom n) = inlist Γ n
Bid Γ (land p q) = (Bid Γ p) ∧ (Bid Γ q)
Bid Γ (lor p q) = (Bid Γ p) ∨ (Bid Γ q)
Bid Γ (lnot p) = not (Bid Γ p)
Bid Γ (to p q) = not (Bid Γ p) ∨ (Bid Γ q)


andL : List prop → prop
andL [] = top
andL (h ∷ t) = land h (andL t)

orL : List prop → prop
orL [] = bot
orL (h ∷ t) = (lor h (orL t))

or_assoc : ∀ {x y z} → (x ∨ y) ∨ z ≡ x ∨ y ∨ z
or_assoc {false} {y} {z} = refl
or_assoc {true}  {y} {z} = refl

or_true_r : ∀ {x} → x ∨ true ≡ true
or_true_r {false} = refl
or_true_r {true} = refl

or_r_true : ∀ {x y} → y ≡ true → x ∨ y ≡ true
or_r_true h rewrite h = or_true_r

or_true_l : ∀ {x} → true ∨ x ≡ true
or_true_l {false} = refl
or_true_l {true} = refl

or_intro_l : ∀ {x y} → x ≡ true → x ∨ y ≡ true
or_intro_l h rewrite h = refl

or_false_r_true : ∀ {x} → x ∨ false ≡ true → x ≡ true
or_false_r_true {true} h = refl

or_false_r : ∀ {x} → x ∨ false ≡ x
or_false_r {false} = refl
or_false_r {true} = refl

or_true_l_false : ∀ {x y} → x ∨ y ≡ true → x ≡ false → y ≡ true
or_true_l_false h h1 rewrite h1 = h

and_false_r : ∀ p → p ∧ false ≡ false
and_false_r false = refl
and_false_r true  = refl

and_true_prop : ∀ {p q} → p ∧ q ≡ true → (p ≡ true) × (q ≡ true)
and_true_prop {true} {true} h = refl Data.Product., refl

and_prop_true : ∀ {p q} → (p ≡ true) × (q ≡ true) → p ∧ q ≡ true
and_prop_true {false} {q} = λ { ()}
and_prop_true {true} {q} = λ { (fst , snd) → snd}

and_true_elim_r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
and_true_elim_r {true} {true} h = refl

and_true_r : ∀ p → p ∧ true ≡ p
and_true_r false = refl
and_true_r true  = refl

not_not_elim : ∀ x → not (not x) ≡ x
not_not_elim false = refl
not_not_elim true  = refl


or_swap : ∀ {x y} → x ∨ y ≡ y ∨ x
or_swap {false} {false} = refl
or_swap {false} {true}  = refl
or_swap {true}  {false} = refl
or_swap {true}   {true} = refl

false_true_eq_bot : false ≡ true → ⊥
false_true_eq_bot ()

to_F_F_⊥ : ∀ {p q v} → Bid v (to p q) ≡ true → Bid v p ≡ true → Bid v q ≡ false → ⊥
to_F_F_⊥ {p} {q} {v} h h1 h2 rewrite h1 | h2 = ⊥-elim (false_true_eq_bot h)

T_not_F : ∀ {x} → x ≡ true → not x ≡ false
T_not_F h rewrite h = refl

not_x_T_x_T_⊥ : ∀ {x} → x ≡ true → not x ≡ true → ⊥
not_x_T_x_T_⊥ h1 h2 rewrite h1 = false_true_eq_bot h2


infix 9 _∈_
data _∈_ : {A : Set} → A → List A → Set where
  ineq : ∀ {A : Set} {a : A} {Γ : List A} → a ∈ (a ∷ Γ)
  incons : ∀ {A : Set} {a b : A} {Γ : List A} → a ∈ Γ → a ∈ (b ∷ Γ)

inandLBidiff : ∀ {Γ a v} → a ∈ Γ → Bid v (andL Γ) ≡ true → Bid v a ≡ true
inandLBidiff {x ∷ G} {.x} {v} ineq h1 = (and_true_prop h1).proj₁
inandLBidiff {x ∷ G} {a} {v} (incons h) h1 = (inandLBidiff {G} {a} {v} h (and_true_elim_r {Bid v x} {_} h1 ) )

andL_exchange_Bid : ∀ {Γ Π v p q} → Bid v (andL (Γ ++ p ∷ q ∷ Π)) ≡ Bid v (andL (Γ ++ q ∷ p ∷ Π))
andL_exchange_Bid {[]} {Π} {v} {p} {q} with (Bid v p) | (Bid v q)
...              | true  | true  = refl
...              | true  | false = refl
...              | false | true  = refl
...              | false | false = refl
andL_exchange_Bid {x ∷ Γ} {Π} {v} {p} {q} rewrite andL_exchange_Bid {Γ} {Π} {v} {p} {q} = refl

orL_exchange_Bid : ∀ {Γ Π v p q} → Bid v (orL (Γ ++ p ∷ q ∷ Π)) ≡ Bid v (orL (Γ ++ q ∷ p ∷ Π))
orL_exchange_Bid {[]} {Π} {v} {p} {q} with (Bid v p) | (Bid v q)
...              | true  | true  = refl
...              | true  | false = refl
...              | false | true  = refl
...              | false | false = refl
orL_exchange_Bid {x ∷ Γ} {Π} {v} {p} {q} rewrite orL_exchange_Bid {Γ} {Π} {v} {p} {q} = refl

contra_semantic : ∀ {p v Γ Δ} → not (Bid v p ∧ Bid v (andL Γ)) ∨ Bid v (orL Δ) ≡ not (Bid v p ∧ Bid v p ∧ Bid v (andL Γ)) ∨ Bid v (orL Δ) 
contra_semantic {p} {v} with (Bid v p)
...             | true  = refl
...             | false = refl


contra_semantic_or : ∀ {p v Γ Δ} → not (Bid v (andL Γ)) ∨ Bid v p ∨ Bid v (orL Δ) ≡ not (Bid v (andL Γ)) ∨ Bid v p ∨ Bid v p ∨ Bid v (orL Δ)
contra_semantic_or {p} {v} with (Bid v p)
...             | true  = refl
...             | false = refl

cons_true_l : ∀ {p v Γ Δ} → Bid v p ≡ true → not (Bid v (andL (p ∷ Γ))) ∨ Bid v (orL Δ) ≡ not (Bid v (andL Γ)) ∨ Bid v (orL Δ)
cons_true_l h rewrite h = refl

cons_false_l : ∀ {p v Γ} → Bid v p ≡ false → Bid v (andL (p ∷ Γ)) ≡ false
cons_false_l h rewrite h = refl

cons_false_r : ∀ {p v Γ Δ} → Bid v p ≡ false → not (Bid v (andL Γ)) ∨ Bid v p ∨ Bid v (orL Δ) ≡ not (Bid v (andL Γ)) ∨ Bid v (orL Δ)
cons_false_r h rewrite h = refl

app_bid_and : ∀ {Γ Δ v} → Bid v (andL (Γ ++ Δ)) ≡ Bid v (andL Γ) ∧ Bid v (andL Δ)
app_bid_and {[]} {Δ} {v} = refl
app_bid_and {x ∷ Γ} {Δ} {v} with (Bid v x)
...         | true  = app_bid_and {Γ} {Δ} {v}
...         | false = refl

app_bid_or : ∀ {Γ Δ v} → Bid v (orL (Γ ++ Δ)) ≡ Bid v (orL Γ) ∨ Bid v (orL Δ)
app_bid_or {[]} {Δ} {v} = refl
app_bid_or {x ∷ Γ} {Δ} {v} with (Bid v x)
...         | true  = refl
...         | false = app_bid_or {Γ} {Δ} {v}

not_and_or : ∀ {p q a b} → not p ∨ a ≡ true → not q ∨ b ≡ true → not (p ∧ q) ∨ a ∨ b ≡ true
not_and_or {false} {q} {a} {b} h h1 = refl
not_and_or {true} {q} {a} {b} h h1 rewrite h = or_true_r

not_and_not_or : ∀ {p q} → not (p ∧ q) ≡ not p ∨ not q
not_and_not_or {false} {q} = refl
not_and_not_or {true}  {q} = refl


not_or_not_and : ∀ {p q} → not (p ∨ q) ≡ not p ∧ not q
not_or_not_and {false} {q} = refl
not_or_not_and {true}  {q} = refl

not_or_and : ∀ p q r → not ((p ∨ q) ∧ r) ≡ not p ∧ not q ∨ not r
not false or false and r = refl
not false or true and r = refl
not true or q and r = refl

or_elim : ∀ (p q r : Set ) →  (p ⊎ q) →  (p → r) → (q → r) → r
or p elim q r (inj₁ x) h1 h2 = h1 x
or p elim q r (inj₂ y) h1 h2 = h2 y

∨_true_or : ∀ p q → p ∨ q ≡ true → (p ≡ true) ⊎ (q ≡ true)
∨ false true q or h rewrite h = inj₂ refl
∨ true true q or h = inj₁ refl

soundness : ∀ {Γ Δ v} → Γ ⇒ Δ → Bid v (to (andL Γ) (orL Δ)) ≡ true
soundness LK⊥ = refl
soundness LK⊤ = refl
soundness {Γ} {p ∷ Δ} {v} LKinit with (Bid v p)
...       | true  = refl
...       | false = refl
soundness {p ∷ Γ} {Δ} {v} (LKweakeningL {_} {_} {p} h) with (Bid v p)
...       | true  = soundness h
...       | false = refl
soundness {Γ} {p ∷ Δ} {v} (LKweakeningR {_} {_} {p} h) with (Bid v p)
...       | true  = or_true_r
...       | false = soundness h
soundness {.(_ ∷ _)} {Δ} {v} (LKcontractionL {Γ} {Δ} {p} h)
  rewrite contra_semantic {p} {v} {Γ} {Δ} = soundness h
soundness {_} {.(_ ∷ _)} {v} (LKcontractionR {Γ} {Δ} {p} h)
  rewrite contra_semantic_or {p} {v} {Γ} {Δ} = soundness h
soundness {_} {_} {v} (LKexchangeL {Γ} {Δ} {p} {q} {Π} h)
  rewrite andL_exchange_Bid {Γ} {Π} {v} {q} {p} = soundness h
soundness {_} {_} {v} (LKexchangeR {Γ} {Δ} {p} {q} {Π} h)
  rewrite orL_exchange_Bid {Δ} {Π} {v} {q} {p} = soundness h
soundness {(land p q ∷ Γ)} {Δ} {v}  (LK∧LL h) with inspect (Bid v p) | (Bid v q)
...       | true  with≡ eq | true  rewrite eq | sym (cons_true_l {p} {v} {Γ} {Δ} eq) = soundness h
...       | true  with≡ eq | false rewrite eq = refl
...       | false with≡ eq | true  rewrite eq = refl
...       | false with≡ eq | false rewrite eq = refl
soundness {(land p q ∷ Γ)} {Δ} {v} (LK∧LR h) with inspect (Bid v q) | (Bid v p)
...       | true  with≡ eq | true
            rewrite eq | and_true_r  (Bid v p) | sym (cons_true_l {q} {v} {Γ} {Δ} eq)
            = soundness h
...       | true  with≡ eq | false rewrite eq | and_true_r  (Bid v p) = refl
...       | false with≡ eq | true  rewrite eq | and_false_r (Bid v p) = refl
...       | false with≡ eq | false rewrite eq | and_false_r (Bid v p) = refl
soundness {Γ} {(land p q ∷ Δ)} {v}  (LK∧R h h1) with inspect (Bid v q) | inspect (Bid v p)
...       | true  with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 = or_true_r
...       | false with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 | sym (cons_false_r {q} {v} {Γ} {Δ} eq1) = soundness h1
...       | true  with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 | sym (cons_false_r {p} {v} {Γ} {Δ} eq2) = soundness h
...       | false with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 | sym (cons_false_r {q} {v} {Γ} {Δ} eq1) = soundness h1
soundness {(lor p q ∷ Γ)} {Δ} {v}   (LK∨L h h1) with inspect (Bid v q) | inspect (Bid v p)
...       | true  with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 | sym (cons_true_l {p} {v} {Γ} {Δ} eq2) = soundness h
...       | false with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 | sym (cons_true_l {p} {v} {Γ} {Δ} eq2) = soundness h
...       | true  with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 | sym (cons_true_l {q} {v} {Γ} {Δ} eq1) = soundness h1
...       | false with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 = refl
soundness {Γ} {(lor p q ∷ Δ)} {v} (LK∨RL h) with inspect (Bid v p) | (Bid v q)
...       | true  with≡ eq | _     rewrite eq = or_true_r
...       | false with≡ eq | true  rewrite eq = or_true_r
...       | false with≡ eq | false rewrite eq | sym (cons_false_r {p} {v} {Γ} {Δ} eq) = soundness h
soundness {Γ} {(lor p q ∷ Δ)} {v} (LK∨RR h) with inspect (Bid v q) | (Bid v p)
...       | true  with≡ eq | true  rewrite eq = or_true_r
...       | true  with≡ eq | false rewrite eq = or_true_r
...       | false with≡ eq | true  rewrite eq = or_true_r
...       | false with≡ eq | false rewrite eq | sym (cons_false_r {q} {v} {Γ} {Δ} eq) = soundness h
soundness {_} {_} {v} (LK→L {Γ} {Δ} {p} {q} {Π} {Σ} h h1)
  rewrite app_bid_and {Γ} {Π} {v} | app_bid_or {Δ} {Σ} {v} with inspect (Bid v (andL Γ))
...       | true  with≡ eq1
          rewrite eq1 | or_true_r {not (Bid v p)} =
            or_elim (Bid v p ≡ true) (Bid v (orL Δ) ≡ true) _
              (∨_true_or (_) (_) (or_true_l_false {not (Bid v (andL Γ))} (soundness h) (T_not_F eq1)))
              (λ x →
                   not ((not (Bid v p) ∨ Bid v q) ∧ Bid v (andL Π)) ∨ Bid v (orL Δ) ∨ Bid v (orL Σ)
                 ≡⟨ cong (λ x → not ((not x ∨ Bid v q) ∧ Bid v (andL Π)) ∨ Bid v (orL Δ) ∨ Bid v (orL Σ)) x ⟩
                   not ((not true ∨ Bid v q) ∧ Bid v (andL Π)) ∨ Bid v (orL Δ) ∨ Bid v (orL Σ)
                 ≡⟨ cong (λ x → not (Bid v q ∧ Bid v (andL Π)) ∨ x) {Bid v (orL Δ) ∨ Bid v (orL Σ)} (or_swap {Bid v (orL Δ)} {Bid v (orL Σ)}) ⟩
                   not (Bid v q ∧ Bid v (andL Π)) ∨ Bid v (orL Σ) ∨ Bid v (orL Δ)
                 ≡⟨ sym (or_assoc {not (Bid v q ∧ Bid v (andL Π))} {Bid v (orL Σ)} {Bid v (orL Δ)}) ⟩
                   (not (Bid v q ∧ Bid v (andL Π)) ∨ Bid v (orL Σ) ) ∨ Bid v (orL Δ)
                 ≡⟨ or_intro_l {not (Bid v q ∧ Bid v (andL Π)) ∨ Bid v (orL Σ)} {Bid v (orL Δ)} (soundness h1) ⟩
                   true
                 ∎)
              λ x →
                begin
                  not ((not (Bid v p) ∨ Bid v q) ∧ Bid v (andL Π)) ∨ Bid v (orL Δ) ∨ Bid v (orL Σ)
                ≡⟨ cong (λ x → not ((not (Bid v p) ∨ Bid v q) ∧ Bid v (andL Π)) ∨ x ∨ Bid v (orL Σ)) x ⟩
                  not ((not (Bid v p) ∨ Bid v q) ∧ Bid v (andL Π)) ∨ true ∨ Bid v (orL Σ)
                ≡⟨ or_r_true refl ⟩
                  true
                ∎
...       | false with≡ eq1
            rewrite eq1 | and_false_r (not (Bid v p) ∨ Bid v q) = refl
soundness {Γ} {to p q ∷ Δ} {v} (LK→R h) with inspect (Bid v p) | inspect (Bid v q)
...       | true  with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 = or_true_r
...       | true  with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 |
                                              sym (cons_true_l {p} {v} {Γ} {Δ} eq1) |
                                              sym (cons_false_r {q} {v} {p ∷ Γ} {Δ} eq2)
                                              = soundness h
...       | false with≡ eq1 | true  with≡ eq2 rewrite eq1 | eq2 = or_true_r
...       | false with≡ eq1 | false with≡ eq2 rewrite eq1 | eq2 = or_true_r
soundness {lnot p ∷ Γ} {Δ} {v} (LK¬L h) with inspect (Bid v p)
...       | true  with≡ eq rewrite eq = refl
...       | false with≡ eq rewrite eq | sym (cons_false_r {p} {v} {Γ} {Δ} eq) = soundness h
soundness {Γ} {lnot p ∷ Δ} {v} (LK¬R h)  with inspect (Bid v p)
...       | true  with≡ eq rewrite eq | sym (cons_true_l {p} {v} {Γ} {Δ} eq ) = soundness h
...       | false with≡ eq rewrite eq = or_true_r

infix 9 _⊢_

data _⊢_ : List prop → prop → Set where
  ND_asumption : ∀ {x Γ} → x ∈ Γ → Γ ⊢ x
  ND_top : ∀ {Γ} → Γ ⊢ top
  ND_contra : ∀ {Γ p} → Γ ⊢ bot → Γ ⊢ p
  ND_and_intro : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ (land p q)
  ND_and_elimL : ∀ {Γ p q} → Γ ⊢ (land p q) → Γ ⊢ p
  ND_and_elimR : ∀ {Γ p q} → Γ ⊢ (land p q) → Γ ⊢ q
  ND_or_introL : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ (lor p q)
  ND_or_introR : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ (lor q p)
  ND_or_elim   : ∀ {Γ p q γ} → Γ ⊢ (lor p q) → (p ∷ Γ) ⊢ γ → (q ∷ Γ) ⊢ γ → Γ ⊢ γ
  ND_to_intro  : ∀ {Γ p q} → (p ∷ Γ) ⊢ q → Γ ⊢ (to p q)
  ND_to_elim   : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ (to p q) → Γ ⊢ q
  ND_not_intro : ∀ {Γ p} → (p ∷ Γ) ⊢ bot → Γ ⊢ (lnot p)
  ND_not_elim  : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ (lnot p) → Γ ⊢ bot


soundND : ∀ {Γ p v} → Γ ⊢ p → Bid v (to (andL Γ) p) ≡ true
soundND {Γ} {p} {v} ND x asumption with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq = (inandLBidiff x eq)
...     | false with≡ eq rewrite eq = refl
soundND ND_top = or_true_r
soundND {Γ} {p} {v} ND h contra with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq = ⊥-elim (to_F_F_⊥ {(andL Γ)} {bot} {v} (soundND h) eq refl)
...     | false with≡ eq rewrite eq = refl
soundND {Γ} {land p q} {v} ND h and h1 intro with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq =
          (and_prop_true {Bid v p} {Bid v q}
            (or_true_l_false (soundND h) (T_not_F eq) ,
              or_true_l_false (soundND h1) (T_not_F eq)))
...     | false with≡ eq rewrite eq = refl
soundND {Γ} {p} {v} (ND_and_elimL {_} {_} {q} h) with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq =
          (and_true_prop {_} {Bid v q} (or_true_l_false {not (Bid v (andL Γ))} (soundND h) (T_not_F eq))).proj₁
...     | false with≡ eq rewrite eq = refl
soundND {Γ} {q} {v} (ND_and_elimR {_} {p} h) with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq =
          (and_true_prop {_} {Bid v q} (or_true_l_false {not (Bid v (andL Γ))} (soundND h) (T_not_F eq))).proj₂
...     | false with≡ eq rewrite eq = refl
soundND {Γ} {lor p q} {v} (ND_or_introL h) rewrite sym (or_assoc {not (Bid v (andL Γ))} {Bid v p} {Bid v q})
        = (or_intro_l (soundND h) )
soundND {Γ} {lor p q} {v} (ND_or_introR h) with (Bid v p)
...     | true  = or_true_r
...     | false = soundND h
soundND {Γ} {z} {v} (ND_or_elim {_} {p} {q} h h1 h2) with inspect (Bid v (andL Γ)) | inspect (Bid v p)
...     | true  with≡ eq | true  with≡ eq0  rewrite eq =
        (or_true_l_false {not (Bid v p ∧ Bid v (andL Γ))} {Bid v z} (soundND h1) (T_not_F (and_prop_true {Bid v p} (eq0 , eq))))
...     | true  with≡ eq | false with≡ eq0  rewrite eq =
        begin
          Bid v z 
        ≡⟨ cong (λ x → not x ∨ Bid v z) {true} {Bid v q ∧ Bid v (andL Γ)}
          (sym (and_prop_true {Bid v q} {Bid v (andL Γ)}
            ((or_true_l_false {Bid v p} (or_true_l_false {not (Bid v (andL Γ))} {Bid v p ∨ Bid v q} (soundND h) (T_not_F eq)) eq0) , eq)) ) ⟩
         not (Bid v q ∧ Bid v (andL Γ)) ∨ Bid v z
        ≡⟨ soundND h2 ⟩
          true
        ∎
...     | false with≡ eq | _ rewrite eq = refl

soundND {Γ} {_} {v} (ND_to_intro {_} {p} {q} h) with inspect (Bid v p)
...     | true  with≡ eq rewrite eq =
        begin
          not (Bid v (andL Γ)) ∨ Bid v q
        ≡⟨ cong (λ x → not (x ∧ Bid v (andL Γ)) ∨ Bid v q) (sym eq) ⟩
          not (Bid v p ∧ Bid v (andL Γ)) ∨ Bid v q
        ≡⟨ soundND h ⟩
          true
        ∎
...     | false with≡ eq rewrite eq = or_true_r
soundND {_} {_} {v} (ND_to_elim {Γ} {p} {q} h h1) with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq =
        begin
            Bid v q
        ≡⟨ cong (λ x → not x ∨ (Bid v q)) (sym (or_true_l_false (soundND h) (T_not_F eq))) ⟩
            not (Bid v p) ∨ (Bid v q) 
        ≡⟨ cong (λ x → not x ∨ (not (Bid v p)) ∨ (Bid v q)) {true} {Bid v (andL Γ)} (sym (eq)) ⟩
            not (Bid v (andL Γ)) ∨ not (Bid v p) ∨ (Bid v q)
        ≡⟨ soundND h1 ⟩
            true
        ∎
...     | false with≡ eq rewrite eq = refl
soundND {Γ} {lnot p} {v} (ND_not_intro h) with inspect (Bid v p)
...     | true  with≡ eq rewrite eq =
        begin
          not (Bid v (andL Γ)) ∨ false
        ≡⟨ cong (λ x → not (x ∧ Bid v (andL Γ)) ∨ false ) (sym eq) ⟩
          not (Bid v p ∧ Bid v (andL Γ)) ∨ false
        ≡⟨ soundND h ⟩
          true
        ∎
...     | false with≡ eq rewrite eq = or_true_r
soundND {Γ} {bot} {v} (ND_not_elim {_} {p} h h1) with inspect (Bid v (andL Γ))
...     | true  with≡ eq rewrite eq = ⊥-elim
          (not_x_T_x_T_⊥ {Bid v p} (or_true_l_false (soundND h) (T_not_F eq))
                                    (or_true_l_false (soundND h1) (T_not_F eq)))
...     | false with≡ eq rewrite eq = refl

