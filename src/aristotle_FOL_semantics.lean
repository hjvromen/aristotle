/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

/-  First-order semantics for Aristotle's assertoric syllogisms -/

variable {α : Type}
variables {A B C : α → Prop}
variable {x : α}

def universal_affirmation (A: α → Prop) (B: α → Prop) : Prop := 
  ∀x, B x → A x
infixr ` a ` : 80 := universal_affirmation

def universal_denial (A: α → Prop) (B: α → Prop) : Prop :=  
  ∀x, B x → ¬ A x
infixr ` e ` : 80 := universal_denial
#check A e B 

def particular_affirmation (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, B x ∧ A x
infixr ` i ` : 80 := particular_affirmation

def particular_denial (A: α → Prop) (B: α → Prop) : Prop := 
  ∃x, B x ∧ ¬ A x
infixr ` o ` : 80 := particular_denial

/-    We prove the soundness of the axioms dr -/

lemma Barbara : A a B → B a C → A a C :=
begin
intros h1 h2 p h3,
have h4 : B p := by exact h2 p h3,
exact h1 p h4
end

lemma Celarent : A e B → B a C → A e C :=
begin
  intros h1 h2 p h3,
  have h4 : B p := by exact h2 p h3,
  exact h1 p h4
end

lemma e_conv : A e B → B e A :=
begin
--simp [universal_denial] at *,
intros h1 b h2,
by_contra,
show false, from (h1 b h) h2,
end

lemma a_conv : (A a B ∧ (∃x, B x)) → B i A :=
  begin
  intro h1,
  cases and.elim_right h1 with p,
  apply exists.intro p (and.intro (h1.1 p h) h)
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
  cc    }
end

lemma contr_2 : A e B = ¬ A i B :=
begin
apply propext,
simp [particular_affirmation, universal_denial] at *, 
apply iff.intro,
{ intro h1,
  by_contra h2,
  cases h2 with u hu,
  have h3 : ¬ A u, from h1 u hu.1,  
  cc  },
{ intros h1 u hB,
  by_contra h4,
  have h6 : ∃x, B x ∧ A x, from exists.intro u (and.intro hB h4),
  cc    }
end

/-  the following lemma's are not strictly necessary  -/

lemma i_conv : A i B → B i A :=
begin
intros h1,
cases h1 with p h2,
cases h2 with q r,
--simp [particular_affirmation],
apply exists.intro p (and.intro r q)
end

lemma Darii : A a B → B i C → A i C :=
begin
intros h1 h2,
cases h2 with p h,
apply exists.intro p,
--have h2 : A p := by exact h1 p h.2,
apply and.intro h.1 (h1 p h.2)
end

lemma Ferio : A e B → B i C → A o C :=
begin
  intros h1 h2,
  cases h2 with p h,
  have h3 : ¬ A p := by exact h1 p h.2,
  apply exists.intro p (and.intro h.1 h3)
end

