module LearnYouAnAgda.IPL where

data _∧_ (P : Set) (Q : Set) : Set where
  ∧-intro : P → Q → (P ∧ Q)

and-elim-left : {P Q : Set} → (P ∧ Q) → P
and-elim-left (∧-intro p q) = p

and-elim-right : {P Q : Set} → (P ∧ Q) → Q
and-elim-right (∧-intro p q) = q

_<=>_ : (P : Set) -> (Q : Set) -> Set
p <=> q = (p → q) ∧ (q → p)

∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm' (∧-intro p q) = ∧-intro q p

∧-comm : {P Q : Set} → (P ∧ Q) <=> (Q ∧ P)
∧-comm = ∧-intro ∧-comm' ∧-comm'

∧-assoc₁ : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

∧-assoc₂ : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

∧-assoc : {P Q R : Set} → (P ∧ (Q ∧ R)) <=> ((P ∧ Q) ∧ R)
∧-assoc = ∧-intro ∧-assoc₂ ∧-assoc₁

data _∨_ (P Q : Set) : Set where
  ∨-intro₁ : P → P ∨ Q
  ∨-intro₂ : Q → P ∨ Q

∨-elim : {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q) → R
∨-elim pr qr (∨-intro₁ p) = pr p
∨-elim pr qr (∨-intro₂ q) = qr q

∨-comm' : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm' (∨-intro₁ p) = ∨-intro₂ p
∨-comm' (∨-intro₂ q) = ∨-intro₁ q

∨-comm : {P Q : Set} → (P ∨ Q) <=> (Q ∨ P)
∨-comm = ∧-intro ∨-comm' ∨-comm'

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥
