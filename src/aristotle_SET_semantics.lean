/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.set.basic
/-- A set-theoretic semantics for Aristotle's assertoric syllogisms is used by 
    many authors. See, for instance, Smith, 1989.
    Terms are interpreted as non-empty subsets of some set of individuals. -/

variable {α : Type}
variable {x : α}
variables {A B C : set α}
-- *** how can I stipulate that these sets have to be nonempty?

/-- semantics of the `a` relation -/
def universal_affirmative (A: set α) (B: set α) : Prop := 
  A ∩ B = B
infixr ` a ` : 80 := universal_affirmative

/-- semantics of the `e` relation -/
def universal_negative (A: set α) (B: set α) : Prop := 
  A ∩ B = ∅ 
infixr ` e ` : 80 := universal_negative

/-- semantics of the `i` relation -/
def particular_affirmative (A: set α) (B: set α) : Prop := 
  (A ∩ B).nonempty 
infixr ` i ` : 80 := particular_affirmative

/-- semantics of the `o` relation -/
def particular_negative (A: set α) (B: set α) : Prop :=  
  A ∩ B ≠ B
infixr ` o ` : 80 := particular_negative

/-- semantics of contradictory: contradictory is defined as negation -/
def c (p : Prop) : Prop := ¬ p

/-- first, we prove a helpful lemma -/
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


/--  Now, we prove the soundness of the axiom system DR -/

lemma Barbara₁ : A a B → B a C → A a C :=
begin
intros h1 h2,
rw universal_affirmative at *,
calc A ∩ C 
    = A ∩ (B ∩ C) : by rw h2
... = (A ∩ B) ∩ C : by tidy
... = B ∩ C : by rw h1
... = C : by rw h2
end


lemma Celarent₁ : A e B → B a C → A e C :=
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


lemma contr {p r : Prop} : (c r → c p) → p → r :=
begin
intros h1,
contrapose!,
assumption
end

/-- we can also prove the contradictories axioms -/

lemma contr_a : c (A a B) = A o B := by simp [c, particular_negative, universal_affirmative]

lemma contr_e : c (A e B) = A i B := 
begin
simp [c, particular_affirmative, universal_negative],
exact set.ne_empty_iff_nonempty
end

lemma contr_i : c (A i B) = A e B :=
begin
simp [c, particular_affirmative, universal_negative],
exact set.not_nonempty_iff_eq_empty
end

lemma contr_o : c (A o B) = A a B := by simp [c, particular_negative, universal_affirmative]


/-- it is, of course, also possible to prove the redundant axioms  -/

lemma Darii₁ : A a B → B i C → A i C :=
begin
intros h1 h2,
--simp [universal_affirmation, particular_affirmation] at *,
--by_contra h3,
cases h2 with p hp,
cases hp,
rw universal_affirmative at h1,
have h4 : p ∈ A ∩ B, by cc,
exact exists.intro p (and.intro h4.left hp_right),
end

lemma Ferio₁ : A e B → B i C → A o C :=
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

#lint