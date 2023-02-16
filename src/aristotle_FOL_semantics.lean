/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.set.basic

/--  First-order semantics for Aristotle's assertoric syllogisms
A first-order logic semantics is a variant of a set-theoretic semantics.
See, for instance Malink (2013, ch. 3).
Terms are interpreted as non-empty subsets of some set of individuals. -/

variable {α : Type}
variable {x : α}
variables {A B C : α → Prop}

/-- semantics of the `a` relation -/
def universal_affirmative (A: α → Prop) (B: α → Prop) : Prop := 
  ∀x, B x → A x
infixr ` a ` : 80 := universal_affirmative

/-- semantics of the `e` relation -/
def universal_negative (A: α → Prop) (B: α → Prop) : Prop :=  
  ∀x, B x → ¬ A x
infixr ` e ` : 80 := universal_negative

/-- semantics of the `i` relation -/
def particular_affirmative (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, A x ∧ B x
-- existential import needs to be stipulated
infixr ` i ` : 80 := particular_affirmative

/-- semantics of the `o` relation -/
def particular_negative (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, B x ∧ ¬ A x
infixr ` o ` : 80 := particular_negative

/-- semantics of contradictory: contradictory is defined as negation -/
def c (p : Prop) : Prop := ¬ p


/--  We prove the soundness of the axiom system DR -/

lemma Barbara₁ : A a B → B a C → A a C :=
begin
intros h1 h2,
rw universal_affirmative,
{ intros p h3,
  have h4 : B p := by exact h2 p h3,
  exact h1 p h4 },
end

lemma Celarent₁ : A e B → B a C → A e C :=
begin
  intros h1 h2 p h3,
  have h4 : B p := by exact h2 p h3,
  exact h1 p h4
end

lemma e_conv : A e B → B e A :=
begin
intros h1 b h2,
by_contra,
show false, from (h1 b h) h2,
end

lemma a_conv (hex: ∃x, B x) : A a B → B i A :=
  begin
  intro h1,
  rw universal_affirmative at h1,
  rw particular_affirmative,
  cases hex with p hp,
  apply exists.intro p (and.intro hp (h1 p hp))
  end 

lemma contr {p r : Prop} : (c r → c p) → p → r :=
begin
intros h1,
contrapose,
assumption
end

/-- We can also prove the contradictories axioms -/

lemma contr_a : c (A a B) = A o B := by simp [c, particular_negative, universal_affirmative]

lemma contr_e : c (A e B) = A i B := 
begin
simp [c, particular_affirmative, universal_negative],
finish
end

lemma contr_i : c (A i B) = A e B :=
begin
simp [c, particular_affirmative, universal_negative],
finish
end

lemma contr_o : c (A o B) = A a B := by simp [c, particular_negative, universal_affirmative]


/--  it is, of course, also possible to prove the redundant axioms  -/

lemma Darii₁ : A a B → B i C → A i C :=
begin
intros h1 h2,
cases h2 with p h,
apply exists.intro p,
exact and.intro (h1 p h.1) h.2
end

lemma Ferio₁ : A e B → B i C → A o C :=
begin
  intros h1 h2,
  cases h2 with p h,
  --rw universal_denial at h1,
  have h3 : ¬ A p := by exact h1 p h.1,
  --rw particular_denial,
  apply exists.intro p (and.intro h.2 h3)
end

lemma i_conv : A i B → B i A :=
begin
intros h1,
cases h1 with p h2,
cases h2 with q r,
apply exists.intro p (and.intro r q)
end

#lint