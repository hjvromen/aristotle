/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/


/-  Set-theoretic semantics for Aristotle's assertoric syllogisms -/

variable {α : Type}
variables {A B C : set α}
--variable {x : α}

def universal_affirmation (A: set α) (B: set α) : Prop := 
  A ∩ B = B
infixr ` a ` : 80 := universal_affirmation

def universal_denial (A: set α) (B: set α) : Prop := 
  ∀x ∈ B, x ∉ A
infixr ` e ` : 80 := universal_denial

def particular_affirmation (A: set α) (B: set α) : Prop := 
  ∃x, x ∈ B ∧ x ∈ A 
infixr ` i ` : 80 := particular_affirmation

def particular_denial (A: set α) (B: set α) : Prop :=  
  ∃x, x ∈ B ∧ x ∉ A
infixr ` o ` : 80 := particular_denial

/-    We prove the soundness of the axiom system dr -/

lemma Barbara : A a B → B a C → A a C :=
begin
intros h1 h2,
rw universal_affirmation at *,
calc A ∩ C 
    = A ∩ (B ∩ C) : by rw h2
... = (A ∩ B) ∩ C : by inter_assoc
... = B ∩ C : by rw h1
... = C : by rw h2,
sorry
end

lemma Celarent : A e B → B a C → A e C :=
begin
  intros h1 h2 p h3,
  have h4 : p ∈ B := by exact h2 p h3,
  exact h1 p h4
end

lemma e_conv : A e B → B e A :=
begin
intros h1 b h2,
by_contra,
show false, from (h1 b h) h2,
end

lemma a_conv : (A a B ∧ (∃x, B x)) → B i A :=
  begin
  intro h1,
  cases and.elim_right h1 with p hp,
  exact exists.intro p (and.intro (h1.1 p hp) hp)
  end 

lemma contr_1 : A a B = ¬ A o B :=
begin
apply propext,
simp [particular_denial, universal_affirmation] at *, 
apply iff.intro,
{ intro h1,
  by_contra h2,
  cases h2 with u hu,
  have h3 : u ∈ A, from h1 u hu.1,
  cc  },
{ intros h1 u hB,
  by_contra h3,
  have h5 : ∃x, x ∈ B ∧ x ∉ A, from exists.intro u (and.intro hB h3),
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
  have h3 : u ∉ A, from h1 u hu.1,  
  cc  },
{ intros h1 u hB,
  by_contra h4,
  have h6 : ∃x, x ∈ B x ∧ x ∈ A, from exists.intro u (and.intro hB h4),
  cc    }
end

/-  the following lemma's are not strictly necessary  -/

lemma Darii : A a B → B i C → A i C :=
begin
intros h1 h2,
cases h2 with p hp,
have h2 : p ∈ A := by exact h1 p hp.2,
exact exists.intro p (and.intro hp.1 h2)
end

lemma Ferio : A e B → B i C → A o C :=
begin
  intros h1 h2,
  cases h2 with p h,
  have h3 : p ∉ A := by exact h1 p h.2,
  exact exists.intro p (and.intro h.1 h3)
end

lemma i_conv : A i B → B i A :=
begin
intros h1,
cases h1 with p h2,
cases h2 with q r,
exact exists.intro p (and.intro r q)
end

