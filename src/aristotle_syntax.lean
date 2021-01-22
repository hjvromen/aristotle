/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

variable {term : Type}                     -- type for terms
variables {A B C P S M: term}

inductive copula : Type
| a : copula
| i : copula
| e : copula
| o : copula

/- variable assertoric : term → copula → term → Prop
#check assertoric

variable syllogism : assertoric → assertoric → assertoric → Prop

structure univ_aff extends assertoric := (x = a) -/

constant universal_affirmation (A : term) (B : term) : Prop
local infixr ` a ` : 80 := universal_affirmation

constant universal_denial (A : term) (B : term) : Prop
local infixr ` e ` : 80 := universal_denial

constant particular_affirmation (A : term) (B : term) : Prop
local infixr ` i ` : 80 := particular_affirmation

constant particular_denial (A : term) (B : term) : Prop
local infixr ` o ` : 80 := particular_denial

def c : Prop → Prop 

/- Aristotle uses the following seven axioms / deduction rules 
   and a definition of the contradictory of a proposition
   see Smith (1989, pp. xix-xx)  -/

-- the four 'perfect' syllogisms
axiom Barbara₁ : P a M → M a S → P a S
axiom Celarent₁ : P e M → M a S → P e S
axiom Darii₁ : P a M → M i S → P i S 
axiom Ferio₁ : P e M → M i S → P o S
-- the three conversion rules
axiom e_conv : A e B → B e A      --   simple conversion
axiom i_conv : A i B → B i A      --   simple conversion
axiom a_conv : A a B → B i A      --   accidental conversion
--  the 'contradictories'
axiom contr_a : c (A a B) = A o B 
axiom contr_e : c (A e B) = A i B 
axiom contr_i : c (A i B) = A e B 
axiom contr_o : c (A o B) = A a B 
--axiom contr_3 {h1 h2 r : Prop} : h1 → h2 → (c r → c h1) → r 
--axiom contr_4 {h1 h2 r : Prop} : h1 → h2 → (c r → c h2) → r 
axiom contr_5 {p r : Prop} : (c r → c p) → p → r

/-
lemma subaltrn_1: A a B → A i B :=        --   accidental conversion
by intro h; exact i_conv (a_conv h)
-/

lemma subaltrn_2 : A e B → A o B :=       --   accidental conversion
begin
intro h,
rw contr_2 at h,
by_contra h2,
rw ← contr_1 at h2,
show false, from h (i_conv (a_conv h2)),
end

lemma subaltrn_2_test : A e B → A o B :=       --   accidental conversion
begin
intro h,
have h3 : c (A o B) → c (A e B) :=
   begin
      intro h4,
      rw contr_e, rw contr_o at h4,
      exact 
   end,
exact contr_5 h3 h,
end

/- Aristotle does not use 'extended' deductions (he does not use already proved theorems but only axioms)
The following proofs follow Aristotle's text -/

--subaltern first-figure syllogisms that Aristotle did not mention
lemma Barbari (h1: P a M) (h2 : M a S) : P i S :=
   i_conv (a_conv (Barbara₁ h1 h2))

lemma Celaront (h1: P e M) (h2 : M a S) : P o S :=
   subaltrn_2 (Celarent₁ h1 h2)

/- second-figure syllogisms -/
lemma Cesare₂ (h1: M e P) (h2 : M a S) : P e S :=
   Celarent₁ (e_conv h1) h2

lemma Camestres₂ (h1: M a P) (h2 : M e S) : P e S :=
   e_conv (Celarent₁ (e_conv h2) h1)

lemma Festino₂ (h1: M e P) (h2 : M i S) : P o S :=
   Ferio₁ (e_conv h1) h2

lemma Baroco₂ (h1: M a P) (h2 : M o S) : P o S :=
begin
-- here Aristotle needs a proof by contradiction
by_contra h3,
rw ← contr_1 at h3,
have h4 : M a S := Barbara₁ h1 h3,
rw contr_1 at h4,
cc
end

lemma Baroco_test (h1: M a P) (h2 : M o S) : P o S :=
begin
have h3 : c (P o S) → c (M o S) := 
   begin
      intro h4,
      rw contr_o at *,
      exact Barbara₁ h1 h4,
   end,
exact contr_5 h3 h2,
end

--subaltern second-figure syllogisms that Aristotle did not mention
lemma Cesaro₂ (h1: M e P) (h2 : M a S) : P o S :=
   subaltrn_2 (Celarent₁ (e_conv h1) h2)

lemma Camestrop₂ (h1: M a P) (h2 : M e S) : P o S :=
   subaltrn_2 (e_conv (Celarent₁ (e_conv h2) h1))

/- third-figure syllogisms  -/
lemma Darapti₃ (h1 : P a M) (h2 : S a M) : P i S :=
   Darii₁ h1 (a_conv h2)

lemma Datisi₃ (h1 : P a M) (h2 : S i M) : P i S :=
   Darii₁ h1 (i_conv h2)

lemma Bocardo₃ (h1 : P o M) (h2 : S a M) : P o S :=
begin
-- here Aristotle needs a proof by contradiction
by_contra h3,
rw ← contr_1 at h3,
have h4 : P a M := Barbara₁ h3 h2,
rw contr_1 at h4,
cc
end

lemma Bocardo_test (h1 : P o M) (h2 : S a M) : P o S :=
begin
have h3 : c (P o S) → c (P o M) :=
   begin
      intro h4,
      rw contr_o at *,
      exact Barbara₁ h4 h2,
   end,
exact contr_5 h3 h1,
end

lemma Felapton₃ (h1 : P e M) (h2 : S a M) : P o S :=
   Ferio₁ h1 (a_conv h2)

lemma Disamis₃ (h1 : P i M) (h2 : S a M) : P i S :=
   i_conv (Darii₁ h2 (i_conv h1))

lemma Ferison₃ (h1 : P e M) (h2 : S i M) : P o S :=
   Ferio₁ h1 (i_conv h2)

/-  Aristotle did not mention these fourth-figure syllogisms-/
lemma Bramantip₄ (h1 : M a P) (h2 : C a M) : P i C :=
   a_conv (Barbara₁ h2 h1)

lemma Camenes₄ (h1 : M a P) (h2 : C e M) : P e C :=
   e_conv(Celarent₁ h2 h1)

lemma Dimaris₄ (h1 : M i P) (h2 : C a M) : P i C :=
   i_conv(Darii₁ h2 h1)

lemma Fesapo₄ (h1 : M e P) (h2 : C a M) : P o C :=
   Ferio₁ (e_conv h1) (a_conv h2)

lemma Fresison₄ (h1 : M e P) (h2 : C i M) : P o C :=
   Festino₂ h1 (i_conv h2)

lemma Camenop₄ (h1 : M a P) (h2 : C e M) : P o C :=
   subaltrn_2(e_conv(Celarent₁ h2 h1))

/- Aristotle also argues that Darii and Ferio do not have to be assumed as axioms, 
but can be derived from the other axioms -/

lemma Dariiₐ (h1 : P a M) (h2 : M i S) : P i S :=
begin
by_contra h3,
rw ← contr_2 at h3,
-- Camestres only uses Celarent
have h4 : M e S := Camestres₂ h1 h3,
rw contr_2 at h4,
show false, from h4 h2
end

lemma Darii_test (h1 : P a M) (h2 : M i S) : P i S :=
begin
have h3 : c (P i S) → c (M i S) :=
   begin
      intro h4,
      rw contr_i at *,
      exact e_conv (Celarent₁ (e_conv h4) h1),
   end,
exact contr_5 h3 h2,
end

lemma Ferioₐ (h1 : P e M) (h2 : M i S) : P o S :=
begin
by_contra h3,
rw ← contr_1 at h3,
-- Cesare only uses Celarent
have h4 : M e S :=  Cesare₂ h1 h3,
rw contr_2 at h4,
show false, from h4 h2
end

lemma Ferio_test (h1 : P e M) (h2 : M i S) : P o S :=
begin
have h3 : c (P o S) → c (M i S) :=
   begin
      intro h4,
      rw contr_i, rw contr_o at h4,
      exact Celarent₁ (e_conv h1) h4,
   end,
exact contr_5 h3 h2,
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

lemma i_conv_test : A i B → B i A :=
begin
intro h3,
have h4 : c (B i A) → c (A i B) :=
   begin
      intro h5,
      rw contr_i at *,
      exact e_conv h5
   end,
exact contr_5 h4 h3,
end

/- 
************** TODO ****************
prove that all invalid syllogisms cannot be derived
-/