/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

/-  First-order semantics for Aristotle's assertoric syllogisms
    A first-order logic semantics is a variant of a set-theoretic semantics.
A set-theoretic semantics for Aristotle's assertoric syllogisms is used by many authors.
See, for instance, ch. 3 of Malink, Marko. Aristotle’s Modal Syllogistic. Harvard University Press, 2013.
A term is interpreted as a non-empty subset of some set of individuals.
-/

variable {α : Type}
variables {A B C : α → Prop}
variable {x : α}

def universal_affirmation (A: α → Prop) (B: α → Prop) : Prop := 
  ∀x, B x → A x
infixr ` a ` : 80 := universal_affirmation

def universal_denial (A: α → Prop) (B: α → Prop) : Prop :=  
  ∀x, B x → ¬ A x
infixr ` e ` : 80 := universal_denial

def particular_affirmation (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, A x ∧ B x
-- existential import
infixr ` i ` : 80 := particular_affirmation

def particular_denial (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, B x ∧ ¬ A x
infixr ` o ` : 80 := particular_denial

/-    We prove the soundness of the axiom system DR -/

lemma Barbara : A a B → B a C → A a C :=
begin
intros h1 h2,
rw universal_affirmation,
{ intros p h3,
  have h4 : B p := by exact h2 p h3,
  exact h1 p h4 },
end

lemma Celarent : A e B → B a C → A e C :=
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
  rw universal_affirmation at h1,
  rw particular_affirmation,
  cases hex with p hp,
  apply exists.intro p (and.intro hp (h1 p hp))
  end 

lemma contr_1 : A a B = ¬ A o B :=
begin
apply propext,
simp [particular_denial, universal_affirmation] at *, 
apply iff.intro,
{ intro h1,
  by_contra h2,
  cases h2 with u hu,
  have h3 : A u, from h1 _ hu.1,
  cc  },
{ intros h1 u hB,
    by_contra h3,
    have h5 : ∃x, B x ∧ ¬ A x, from exists.intro u (and.intro hB h3),
    cc    },
end

lemma contr_2 : A e B = ¬ A i B :=
begin
apply propext,
simp [particular_affirmation, universal_denial] at *, 
apply iff.intro,
{ intro h1,
  by_contra h2,
  cases h2 with u hu,
  have h3 : ¬ A u, from h1 u hu.2,  
  cc  },
{ intros h1 u hB,
  by_contra h4,
  have h6 : ∃x, A x ∧ B x, from exists.intro u (and.intro h4 hB),
  show false, from h1 h6    }
end

/-  it is, of course, also possible to prove the redundant axioms  -/

lemma i_conv : A i B → B i A :=
begin
intros h1,
cases h1 with p h2,
cases h2 with q r,
apply exists.intro p (and.intro r q)
end

lemma Darii : A a B → B i C → A i C :=
begin
intros h1 h2,
cases h2 with p h,
apply exists.intro p,
--have h2 : A p := by exact h1 p h.2,
exact and.intro (h1 p h.1) h.2
end

lemma Ferio : A e B → B i C → A o C :=
begin
  intros h1 h2,
  cases h2 with p h,
  --rw universal_denial at h1,
  have h3 : ¬ A p := by exact h1 p h.1,
  --rw particular_denial,
  apply exists.intro p (and.intro h.2 h3)
end

