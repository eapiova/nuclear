module nuclear (Atoms : Set) where
infixr 8 _⇒_

data Form : Set where
  At : Atoms → Form
  False : Form
  _⇒_ : Form → Form → Form
  j : Form → Form

data Con : Set where
  • : Con
  _,_ : Con → Form → Con

open import Substructural.Core.Extensions Form public
  using (L⟨_⟩; Lift1; Max⟨_,_⟩; Kol1⟨_,_⟩; Kj)

open import Substructural.Core.Conservation Form public
  using (R'DerivableInMax; JHomogeneous; proposition5-2026; lemma2-2026; theorem6; theorem6-k=j-compatible)

variable A B C : Form
variable Γ Δ : Con

module Deriv (Φ : Form → Set) where
  infixl 5 _,_
  infix 3 _⊢_
  infix 3 _⊢*_

  data _⊢_ : Con → Form → Set where
    axiom : Φ A → Γ ⊢ A
    zero : Γ , A ⊢ A
    suc : Γ ⊢ A →  Γ , B ⊢ A
    lam : Γ , A ⊢ B → Γ ⊢ A ⇒ B
    app : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

  data _⊢*_ : Con → Con → Set where
    ε : Γ ⊢* •
    _,_ : Γ ⊢* Δ → Γ ⊢ A → Γ ⊢* Δ , A

  suc* : Γ ⊢* Δ → Γ , A ⊢* Δ
  suc* ε = ε
  suc* (δ , a) = (suc* δ) , (suc a)

  _^ : Γ ⊢* Δ → Γ , A ⊢* Δ , A
  δ ^ = suc* δ , zero

  id : Γ ⊢* Γ
  id {•} = ε
  id {Γ , A} = id ^

  _[_] : Γ ⊢ A → Δ ⊢* Γ → Δ ⊢ A
  axiom x [ δ ] = axiom x
  zero [ δ , a ] = a
  suc a [ δ , b ] = a [ δ ]
  lam a [ δ ] = lam (a [ δ ^ ])
  app a b [ δ ] = app (a [ δ ]) (b [ δ ])

data ∅ : Form → Set where

open Deriv ∅ using (zero ; suc ; lam ; app) renaming (_⊢_ to _⊢m_)

data EFQ : Form → Set where
  efq : EFQ (False ⇒ A)

open Deriv EFQ using (zero ; suc ; lam ; app) renaming (_⊢_ to _⊢i_)

not_ : Form → Form
not A = A ⇒ False

data NN : Form → Set where
  nn : NN ((not (not A)) ⇒ A)

open Deriv NN  renaming (_⊢_ to _⊢c_)

variable Φ Ψ : Form → Set

m→x : Γ ⊢m A → Deriv._⊢_ Φ Γ A
m→x zero = Deriv.zero
m→x (suc a) = Deriv.suc (m→x a)
m→x (lam a) = Deriv.lam (m→x a)
m→x (app a b) = Deriv.app (m→x a) (m→x b)

m→i : Γ ⊢m A → Γ ⊢i A
m→i zero = Deriv.zero
m→i (suc a) = Deriv.suc (m→i a)
m→i (lam a) = Deriv.lam (m→i a)
m→i (app a b) = Deriv.app (m→i a) (m→i b)

i→c : Γ ⊢i A → Γ ⊢c A
i→c (axiom efq) =
  Deriv.lam (Deriv.app (Deriv.axiom nn) (Deriv.lam (Deriv.suc Deriv.zero)))
i→c zero = Deriv.zero
i→c (suc a) = Deriv.suc (i→c a)
i→c (lam a) = Deriv.lam (i→c a)
i→c (app a b) = Deriv.app (i→c a) (i→c b)

open import Data.Empty

variable X Y Z : Set

¬_ : Set → Set
¬_ X = X → ⊥

case⊥ : ⊥ → X
case⊥ ()

→¬¬ : ¬ ¬ (X → Y) → (X → ¬ ¬ Y) 
→¬¬ = λ f x ny → f (λ g → ny (g x))

⇒notnot : Γ ⊢m not not (A ⇒ B) ⇒ A ⇒ not not B 
⇒notnot =
  Deriv.lam (Deriv.lam (Deriv.lam (Deriv.app
            (Deriv.suc (Deriv.suc Deriv.zero))
              (Deriv.lam (Deriv.app (Deriv.suc Deriv.zero)
              (Deriv.app Deriv.zero (Deriv.suc (Deriv.suc Deriv.zero))))))))

¬¬→ : (X → ¬ ¬ Y) → ¬ ¬ (X → Y)
¬¬→ = λ f g → g (λ x → case⊥ (f x (λ y → g (λ _ → y))))

notnot⇒ : Γ ⊢i (A ⇒ not not B) ⇒ not not (A ⇒ B) 
notnot⇒ = Deriv.lam (Deriv.lam (Deriv.app Deriv.zero
                    (Deriv.lam (Deriv.app (Deriv.axiom efq)
                    (Deriv.app (Deriv.app
                      (Deriv.suc (Deriv.suc Deriv.zero)) Deriv.zero)
                        (Deriv.lam (Deriv.app (Deriv.suc (Deriv.suc Deriv.zero))
                        (Deriv.lam (Deriv.suc Deriv.zero)))))))))

¬¬ : X → ¬ ¬ X
¬¬ = λ x nx → nx x

notnot : Γ ⊢i A ⇒ not not A
notnot = Deriv.lam (Deriv.lam (Deriv.app Deriv.zero (Deriv.suc Deriv.zero)))

Bind : ¬ ¬ X → (X → ¬ ¬ Y) → ¬ ¬ Y
Bind = λ nnx xnny ny → nnx (λ x → xnny x ny)

bind : Γ ⊢m not not A ⇒ (A ⇒ not not B) ⇒ not not B 
bind = Deriv.lam (Deriv.lam (Deriv.lam
     (Deriv.app (Deriv.suc (Deriv.suc Deriv.zero))
       (Deriv.lam (Deriv.app (Deriv.app (Deriv.suc (Deriv.suc Deriv.zero))
         Deriv.zero) (Deriv.suc Deriv.zero))))))

glivenko :  Γ ⊢c A → Γ ⊢i not not A
glivenko (Deriv.axiom nn) = Deriv.app notnot⇒ (Deriv.lam Deriv.zero)
glivenko Deriv.zero = Deriv.app notnot Deriv.zero
glivenko (Deriv.suc a) = Deriv.suc (glivenko a)
glivenko (Deriv.lam a) = Deriv.app notnot⇒ (Deriv.lam (glivenko a))
glivenko (Deriv.app a b) =
  Deriv.app (Deriv.app (m→i bind) (glivenko b))
  (Deriv.app (m→i ⇒notnot) (glivenko a))

data J : Form → Set where
  j-intro : J (A ⇒ j A)
  j-elim : J (j A ⇒ (A ⇒ j B) ⇒ j B)

open Deriv J renaming (_⊢_ to _⊢j_)

data S : Form → Set where
  j-intro : S (A ⇒ j A)
  j-stab : S (j A ⇒ A)

open Deriv S renaming (_⊢_ to _⊢s_)

data _∪_ {A : Set}(P Q : A → Set) : A → Set where
  inl : {a : A} → P a → (P ∪ Q) a
  inr : {a : A} → Q a → (P ∪ Q) a  

-- refactor using _⊆_
inlD : Deriv._⊢_ Φ Γ A → Deriv._⊢_ (Φ ∪ Ψ) Γ A
inlD (Deriv.axiom x) = Deriv.axiom (inl x)
inlD Deriv.zero = Deriv.zero
inlD (Deriv.suc a) = Deriv.suc (inlD a)
inlD (Deriv.lam a) = Deriv.lam (inlD a)
inlD (Deriv.app a b) = Deriv.app (inlD a) (inlD b)

data J-Shift : Form → Set where
  j-shift : J-Shift ((A ⇒ j B) ⇒ j (A ⇒ B))

Glivenko : Form → Set
Glivenko = J ∪ J-Shift

idm : Γ ⊢m A ⇒ A
idm = Deriv.lam Deriv.zero

open Deriv Glivenko renaming (_⊢_ to _⊢g_)

unshift :  Γ ⊢j j (A ⇒ B) ⇒ (A ⇒ j B)
unshift = Deriv.lam (Deriv.lam
        (Deriv.app (Deriv.app (Deriv.axiom j-elim) (Deriv.suc Deriv.zero))
          (Deriv.lam (Deriv.app (Deriv.axiom j-intro)
            (Deriv.app Deriv.zero (Deriv.suc Deriv.zero))))))

glivenko-j : Γ ⊢s A → Γ ⊢g j A
glivenko-j (Deriv.axiom j-intro) =
  Deriv.app (Deriv.axiom (inl j-intro)) (Deriv.axiom (inl j-intro))
glivenko-j (Deriv.axiom j-stab) =
  Deriv.app (Deriv.axiom (inr j-shift)) (m→x idm)
glivenko-j Deriv.zero =
  Deriv.app (Deriv.axiom (inl j-intro)) Deriv.zero
glivenko-j (Deriv.suc a) = Deriv.suc (glivenko-j a)
glivenko-j (Deriv.lam a) =
  Deriv.app (Deriv.axiom (inr j-shift)) (Deriv.lam (glivenko-j a))
glivenko-j (Deriv.app a b) =
  Deriv.app (Deriv.app (Deriv.axiom (inl j-elim)) (glivenko-j b))
    (Deriv.app (inlD unshift) (glivenko-j a))

{-

contr : Γ , A ⊢* Γ , A , A
contr = id , zero

contr⊢ : Γ , A , A ⊢ B → Γ , A ⊢ B
contr⊢ d = d [ contr ]

exchg : Γ , A , B ⊢* Γ , B , A
exchg = ((suc* (suc* id)) , zero) , (suc zero)

-}
