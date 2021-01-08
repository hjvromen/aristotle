/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

variable {α : Type}
variables {A B C P S M: α → Prop}

/-  Aristotle's assertoric syllogisms -/
constant universal_affirmation (A: α → Prop) (B: α → Prop) : Prop
local infixr ` a ` : 80 := universal_affirmation

constant universal_denial (A: α → Prop) (B: α → Prop) : Prop
local infixr ` e ` : 80 := universal_denial
#check A e B 

constant particular_affirmation (A: α → Prop) (B: α → Prop) : Prop
local infixr ` i ` : 80 := particular_affirmation

constant particular_denial (A: α → Prop) (B: α → Prop) : Prop
local infixr ` o ` : 80 := particular_denial

/- Aristotle uses these seven axioms / deduction rules (→ Malink)
   Corcoran calls this system d   
   System dr uses only the numbers 1, 2, 5 and 7  (see end of this file for a proof)  -/

axiom Barbara₁ : P a M → M a S → P a S
axiom Celarent₁ : P e M → M a S → P e S
axiom Darii₁ : P a M → M i S → P i S 
axiom Ferio₁ : P e M → M i S → P o S
axiom e_conv : A e B → B e A      --   simple conversion
axiom i_conv : A i B → B i A      --   simple conversion
axiom a_conv : A a B → B i A      --   accidental conversion
--  Aristotle also uses these `contradictories`
axiom contr_1 : A a B = ¬ A o B
axiom contr_2 : A e B = ¬ A i B

lemma subaltrn_1: A a B → A i B :=        --   accidental conversion
by intro h; exact i_conv (a_conv h)

lemma subaltrn_2 : A e B → A o B :=       --   accidental conversion
begin
intro h,
by_contra h2,
rw ← contr_1 at h2,
have h4 : B e A, from e_conv h,
rw contr_2 at h4,
show false, from h4 (a_conv h2)
end

-- Aristotle does not use 'extended' deductions (he does not use already proved theorems but only axioms)

/-  first-figure syllogisms that Aristotle did not mention -/
lemma Barbari (h1: P a M) (h2 : M a S) : P i S :=
-- this a subalternate mood
by exact i_conv (a_conv (Barbara₁ h1 h2))

lemma Celaront (h1: P e M) (h2 : M a S) : P o S :=
-- this a subalternate mood
by exact subaltrn_2 (Celarent₁ h1 h2)

/- second-figure syllogisms -/
lemma Cesare₂ (h1: M e P) (h2 : M a S) : P e S :=
by exact Celarent₁ (e_conv h1) h2

lemma Camestres₂ (h1: M a P) (h2 : M e S) : P e S :=
by exact e_conv (Celarent₁ (e_conv h2) h1)

lemma Festino₂ (h1: M e P) (h2 : M i S) : P o S :=
by exact Ferio₁ (e_conv h1) h2

lemma Baroco₂ (h1: M a P) (h2 : M o S) : P o S :=
begin
-- here Aristotle needs a proof by contradiction
by_contra h3,
rw ← contr_1 at h3,
have h4 : M a S, from Barbara₁ h1 h3,
rw contr_1 at h4,
cc
end

/-  second-figure syllogisms that Aristotle did not mention -/
lemma Cesaro₂ (h1: M e P) (h2 : M a S) : P o S :=
-- this a subalternate mood
by exact subaltrn_2 (Celarent₁ (e_conv h1) h2)

lemma Camestrop₂ (h1: M a P) (h2 : M e S) : P o S :=
-- this a subalternate mood
by exact subaltrn_2 (e_conv (Celarent₁ (e_conv h2) h1))

/- third-figure syllogisms  -/
lemma Darapti₃ (h1 : P a M) (h2 : S a M) : P i S :=
by exact Darii₁ h1 (a_conv h2)

lemma Datisi₃ (h1 : P a M) (h2 : S i M) : P i S :=
by exact Darii₁ h1 (i_conv h2)

lemma Bocardo₃ (h1 : P o M) (h2 : S a M) : P o S :=
begin
-- here Aristotle needs a proof by contradiction
by_contra h3,
rw ← contr_1 at h3,
have h4 : P a M, from Barbara₁ h3 h2,
rw contr_1 at h4,
cc
end

lemma Felapton₃ (h1 : P e M) (h2 : S a M) : P o S :=
by exact Ferio₁ h1 (a_conv h2)

lemma Disamis₃ (h1 : P i M) (h2 : S a M) : P i S :=
by exact i_conv (Darii₁ h2 (i_conv h1))

lemma Ferison₃ (h1 : P e M) (h2 : S i M) : P o S :=
by exact Ferio₁ h1 (i_conv h2)

/-  Aristotle did not mention fourth-figure syllogisms-/
lemma Bramantip₄ (h1 : M a P) (h2 : C a M) : P i C :=
by exact a_conv (Barbara₁ h2 h1)

lemma Camenes₄ (h1 : M a P) (h2 : C e M) : P e C :=
by exact e_conv(Celarent₁ h2 h1)

lemma Dimaris₄ (h1 : M i P) (h2 : C a M) : P i C :=
by exact i_conv(Darii₁ h2 h1)

lemma Fesapo₄ (h1 : M e P) (h2 : C a M) : P o C :=
by exact Ferio₁ (e_conv h1) (a_conv h2)

lemma Fresison₄ (h1 : M e P) (h2 : C i M) : P o C :=
by exact Festino₂ h1 (i_conv h2)

lemma Camenop₄ (h1 : M a P) (h2 : C e M) : P o C :=
-- this a subalternate mood
by exact subaltrn_2(e_conv(Celarent₁ h2 h1))

/- Aristotle also argues that Darii and Ferio do not have to be assumed as axioms, 
but can be derived from the other axioms -/

lemma Dariiₐ (h1 : P a M) (h2 : M i S) : P i S :=
begin
by_contra h3,
rw ← contr_2 at h3,
-- Camestres only uses Celarent
have h4 : M e S, from Camestres₂ h1 h3,
rw contr_2 at h4,
show false, from h4 h2
end

lemma Ferioₐ (h1 : P e M) (h2 : M i S) : P o S :=
begin
by_contra h3,
rw ← contr_1 at h3,
-- Cesare only uses Celarent
have h4 : M e S, from Cesare₂ h1 h3,
rw contr_2 at h4,
show false, from h4 h2
end

/- it is even possible to get rid of axiom i_conv -/

lemma i_conv₁ : A i B → B i A :=
begin
intro h1,
by_contra h2,
rw ← contr_2 at h2,
have h3 : A e B, from e_conv h2,
rw contr_2 at h3,
cc
end

/- Aristotle also uses 'ecthesis' as an alternative proof method instead of proof by contradiction -/


 