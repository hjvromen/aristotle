/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import order.bounded_lattice

/-  Preorder semantics for Aristotle's assertoric syllogisms
Terms are regarded to be primitives. They form a meet semi-lattice with bot.
See, for instance, Andrade-Lotero, Edgar, and Catarina Dutilh Novaes. 
‘Validity, the Squeezing Argument and Alternative Semantic Systems: 
The Case of Aristotelian Syllogistic’. Journal of Philosophical Logic 41, 
no. 2 (April 2012): 387–418, pp. 402-403.
-/

variable {α : Type} 
variables [semilattice_inf_bot α] {A B C : α}
-- *** how can I stipulate that these variables are not the bottom element of α?

def universal_affirmative (A : α) (B: α) : Prop := 
  A ⊓ B = B
infixr ` a ` : 80 := universal_affirmative

def universal_negative (A : α) (B: α) : Prop := 
  A ⊓ B = ⊥ 
infixr ` e ` : 80 := universal_negative

def particular_affirmative (A: α) (B: α) : Prop := 
  A ⊓ B ≠ ⊥ 
infixr ` i ` : 80 := particular_affirmative

def particular_negative (A: α) (B: α) : Prop :=  
  A ⊓ B ≠ B
infixr ` o ` : 80 := particular_negative

/-    We prove the soundness of the axiom system DR -/

lemma Barbara : A a B → B a C → A a C :=
begin
intros hab hbc,
rw universal_affirmative at *,
finish
end

lemma Celarent : A e B → B a C → A e C :=
begin
intros h1 h2,
simp [universal_affirmative, universal_negative] at *,
have h3 : A ⊓ C ≤ A ⊓ B, by apply inf_le_inf_left; assumption,
--have h4 : A ⊓ C ≤ ⊥, by finish,
finish,
end

lemma e_conv : A e B → B e A :=
begin
intro h1,
rw universal_negative at *,
rw inf_comm at h1,
assumption
end

lemma a_conv : B ≠ ⊥ →  A a B → B i A :=
begin
intros h1 h2 h3,
rw universal_affirmative at h2,
rw inf_comm at h3,
have h4 : B = ⊥, from eq.trans (eq.symm h2) h3,
show false, from h1 h4
end 

lemma contr_1 : A a B = ¬ A o B :=
begin
simp [particular_negative, universal_affirmative] at *, 
end

lemma contr_2 : A e B = ¬ A i B :=
begin
simp [particular_affirmative, universal_negative] at *, 
end

/-  it is, of course, also possible to prove the redundant axioms  -/

lemma Darii : A a B → B i C → A i C :=
begin
intros h1 h2,
simp [particular_affirmative, universal_affirmative] at *, 
by_contra h3,
have h4 : B ⊓ C ≤ A ⊓ C, by apply inf_le_inf_right; assumption,
have h5 : B ⊓ C = ⊥, by exact eq_bot_mono h4 h3,
show false, from h2 h5
end


lemma Ferio : A e B → B i C → A o C :=
begin
  intros h1 h2,
  simp [particular_affirmative, universal_negative] at h1 h2,
  rw [particular_negative, ne],
  by_contra h3,
  rw inf_comm at h1,
  have h4 : B ⊓ C = ⊥, by calc B ⊓ C
      = B ⊓ (A ⊓ C) : by rw h3
  ... = (B ⊓ A) ⊓ C : by rw inf_assoc 
  ... = ⊥ ⊓ C : by rw h1
  ... = ⊥ : by exact bot_inf_eq,
show false, from h2 h4
end

lemma i_conv : A i B → B i A :=
begin
intros h1,
simp [particular_affirmative] at *,
rw [inf_comm],
assumption
end


