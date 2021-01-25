/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.set.basic
/-  
A set-theoretic semantics for Aristotle's assertoric syllogisms is used by many authors.
See, for instance, Smith, Robin. Aristotle Prior Analytics. Indianapolis, IN: Hackett, 1989.
Terms are interpreted as non-empty subsets of some set of individuals.
-/

variable {α : Type*}
variables {A B C : set α}
-- *** how can I stipulate that these sets have to be nonempty?
variable {x : α}

def universal_affirmative (A: set α) (B: set α) : Prop := 
  A ∩ B = B
infixr ` a ` : 80 := universal_affirmative

def universal_negative (A: set α) (B: set α) : Prop := 
  A ∩ B = ∅ 
infixr ` e ` : 80 := universal_negative

def particular_affirmative (A: set α) (B: set α) : Prop := 
  (A ∩ B).nonempty 
infixr ` i ` : 80 := particular_affirmative

def particular_negative (A: set α) (B: set α) : Prop :=  
  A ∩ B ≠ B
infixr ` o ` : 80 := particular_negative

--first, we prove a helpful lemma
lemma inter_empty (h1 : A e B) : x ∈ B → x ∉ A :=
begin
rw universal_negative at h1,
intro h2,
by_contra h3,
have h4 : x ∈ A ∩ B, from set.mem_inter h3 h2,
have h5 : (A ∩ B).nonempty, from exists.intro x h4,
have h6 : A ∩ B ≠ ∅, from set.nonempty.ne_empty h5,
show false, from h6 h1
end


/-    We prove the soundness of the axiom system DR -/

lemma Barbara : A a B → B a C → A a C :=
begin
intros h1 h2,
rw universal_affirmative at *,
calc A ∩ C 
    = A ∩ (B ∩ C) : by rw h2
... = (A ∩ B) ∩ C : by tidy
... = B ∩ C : by rw h1
... = C : by rw h2
end

lemma Celarent : A e B → B a C → A e C :=
begin
  intros h1 h2,
  rw universal_negative at *,
  rw universal_affirmative at h2,
  calc A ∩ C 
      = A ∩ (B ∩ C): by rw h2
  ... = (A ∩ B) ∩ C: by tidy
  ... = ∅ ∩ C : by rw h1
  ... = ∅ : by simp,
end

lemma e_conv : A e B → B e A :=
begin
intro h1,
rw universal_negative at *,
cc,
end

lemma a_conv : (A a B ∧ B.nonempty) → B i A :=
  begin
  intro h1,
  cases h1.2 with p hp,
  rw particular_affirmative,
  rw universal_affirmative at h1,
  cc,
  end 

lemma contr_1 : A a B = ¬ A o B := 
begin
--apply propext,
simp [particular_negative, universal_affirmative] at *, 
end

lemma contr_2 : A e B = ¬ A i B :=
begin
--apply propext,
simp [particular_affirmative, universal_negative] at *,
split,
{ intro h1,
  by_contra h2,
  show false, from (set.nonempty.ne_empty h2) h1},
{ intro h1,
  rw set.nonempty at h1,
  tidy  }
end

/-  it is, of course, also possible to prove the redundant axioms  -/

lemma Darii : A a B → B i C → A i C :=
begin
intros h1 h2,
--simp [universal_affirmation, particular_affirmation] at *,
--by_contra h3,
cases h2 with p hp,
cases hp,
rw universal_affirmative at h1,
have h4 : p ∈ A ∩ B, by cc,
have h5 : p ∈ A, by exact h4.left,
exact exists.intro p (and.intro h5 hp_right),
end

lemma Ferio : A e B → B i C → A o C :=
begin
  intros h1 h2,
  cases h2 with p h,
  rw particular_negative,
  cases h with hb hc,
  have h3 : p ∉ A, by exact inter_empty h1 hb,
  simp,
  by_contra h4,
  rw ← h4 at hc,
  show false, from h3 hc.1
end

lemma i_conv : A i B → B i A :=
begin
intros h1,
cases h1 with p h2,
cases h2 with q r,
exact exists.intro p (and.intro r q)
end

