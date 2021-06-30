module plfa.part2.Lambda where
open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import plfa.part1.Isomorphism using (_≲_)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

data Value : Term → Set where
  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)


infix 9 _[_:=_]
-- 
_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]


twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

Ex_β : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ (ƛ "x" ⇒ ` "x")
Ex_β = β-ƛ V-ƛ

-- twoᶜ : Term
-- twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- plusᶜ : Term
-- plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
--          ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

-- sucᶜ : Term
-- sucᶜ = ƛ "n" ⇒ `suc (` "n")

Ex_β₂ : twoᶜ · sucᶜ · `zero  —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
Ex_β₂ = ξ-·₁ (β-ƛ V-ƛ)

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

-- data _—↠_ : Term → Term → Set where
--   _∎ : ∀ M
--       ---------
--     → M —↠ M

--   _—→⟨_⟩_ : ∀ L {M N}
--     → L —→ M
--     → M —↠ N
--       ---------
--     → L —↠ N

-- begin_ : ∀ {M N}
--   → M —↠ N
--     ------
--   → M —↠ N
-- begin M—↠N = M—↠N

-- —↠≲—↠′ : ∀ (M N : Term) → M —↠ N ≲ M —↠′ N
-- —↠≲—↠′ = λ M N →
--        record { to = λ { (.M ∎) → refl′ ; 
--                          (.M —→⟨ x ⟩ y) →
--                            trans′ (step′ x) {!!}};
--                 from = λ { (step′ x) → {!!} ;
--                            refl′ → {!!} ;
--                            (trans′ x x₁) → {!!}} ;
--                 from∘to = {!!} }

not-value-reduction : ∀ M →
  Value M → 
  ¬ ( ∃[ N ] (M —→ N))
not-value-reduction .(ƛ _ ⇒ _) V-ƛ = λ { ()}
not-value-reduction .`zero V-zero = λ { ()}
not-value-reduction .(`suc _) (V-suc {V} h) =
  λ { (.(`suc _) Data.Product., ξ-suc {_} {M}  snd) →
            ⊥-elim (not-value-reduction V h (M Data.Product., snd))}

deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N
deterministic (ξ-·₁ {L} {M} {N} h1) (ξ-·₁ h2) =
  cong (λ x → x · N) (deterministic h1 h2)
deterministic (ξ-·₁ {L} {M} {L'} h1) (ξ-·₂ x h2) =
  (⊥-elim (not-value-reduction L x (M Data.Product., h1)) )

deterministic (ξ-·₂ x h1) (ξ-·₁ {L} {M} {N} h2) =
  (⊥-elim (not-value-reduction L x (M Data.Product., h2) ))
deterministic (ξ-·₂ {L} {M} {N} x h1) (ξ-·₂ x₁ h2) =
  cong (λ x → L · x) (deterministic h1 h2)
deterministic (ξ-·₂ {_} {_} {M} x h1) (β-ƛ {y} {N} {V} x₁) =
  (⊥-elim (not-value-reduction V x₁ ( M Data.Product., h1) ))

deterministic (β-ƛ {y} {N} {V} x) (ξ-·₂ {_} {_} {M} x₁ h2) =
  (⊥-elim (not-value-reduction V x (M Data.Product., h2)))
deterministic (β-ƛ x) (β-ƛ x₁) = refl

deterministic (ξ-suc h1) (ξ-suc h2) =
  cong (λ x → `suc x) (deterministic h1 h2)

deterministic (ξ-case {x}{M}{L}{N}{O} h1) (ξ-case h2) =
  cong (λ y → case y [zero⇒ N |suc x ⇒ O ] ) (deterministic h1 h2)

deterministic (ξ-case {X} {_} {_} {M} {N} (ξ-suc {L} {O} h1)) (β-suc x) =
  (⊥-elim (not-value-reduction L x (O Data.Product., h1)))

deterministic β-zero β-zero = refl

deterministic (β-suc x) (ξ-case {X} {_} {_} {M} {N} (ξ-suc {L} {O} h2)) =
  (⊥-elim (not-value-reduction L x (O Data.Product., h2)))
deterministic (β-suc x) (β-suc x₁) = refl

deterministic β-μ β-μ = refl

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context


infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A


_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z)) (⊢` Z) (⊢suc (((⊢` (S′ (S′ (S′ Z)))) · ⊢` Z) · ⊢` (S′ Z) )))))

-- ⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
-- ⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
--          (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
--   where
--   ∋+  = S′ (S′ (S′ Z))
--   ∋m  = S′ Z
--   ∋n  = Z
--   ∋m′ = Z
--   ∋n′ = S′ Z

