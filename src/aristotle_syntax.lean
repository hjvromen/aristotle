/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

/- This is a formalisation of Aristotle's assertoric (non-modal) syllogistic. 
   We start with a syntactical account (language and proof system). 
   After that, three differrent semantics are presented, 
   each with a proof of soundness of the proof system. -/

variable {term : Type}                     -- type for terms
variables {A B C P S M: term}

constant a : term → term → Prop            -- universal affirmative
local infixr ` a ` : 80 := a

constant e : term → term → Prop            -- universal negative
local infixr ` e ` : 80 := e

constant i : term → term → Prop            -- particular affirmative
local infixr ` i ` : 80 := i

constant o : term → term → Prop            -- particular negative
local infixr ` o ` : 80 := o

-- the 'contradictories'
-- *** is it possible to give an inductive definition instead of using axioms?
constant c : Prop → Prop
axiom contr_a : c (A a B) = A o B 
axiom contr_e : c (A e B) = A i B 
axiom contr_i : c (A i B) = A e B 
axiom contr_o : c (A o B) = A a B 

/- Aristotle uses eight axioms / deduction rules see Smith (1989, pp. xix-xx)  -/

-- the four 'perfect' syllogisms
axiom Barbara₁ : P a M → M a S → P a S
axiom Celarent₁ : P e M → M a S → P e S
axiom Darii₁ : P a M → M i S → P i S 
axiom Ferio₁ : P e M → M i S → P o S

-- the three conversion rules
axiom e_conv : A e B → B e A      --   simple conversion
axiom i_conv : A i B → B i A      --   simple conversion
axiom a_conv : A a B → B i A      --   accidental conversion

-- reductio ad absurdum
axiom contr {p r : Prop} : (c r → c p) → p → r

/- Aristotle does not use 'extended' deductions, i.e. he does not use already proved 
theorems but only axioms. The following proofs follow Aristotle's text as closely as 
possible. 
-/


/- second-figure syllogisms -/
lemma Cesare₂ (h1: M e P) (h2 : M a S) : P e S :=
   Celarent₁ (e_conv h1) h2

lemma Camestres₂ (h1: M a P) (h2 : M e S) : P e S :=
   e_conv (Celarent₁ (e_conv h2) h1)

lemma Festino₂ (h1: M e P) (h2 : M i S) : P o S :=
   Ferio₁ (e_conv h1) h2

lemma Baroco₂ (h1: M a P) (h2 : M o S) : P o S :=
-- here a reductio proof is needed
begin
have h3 : c (P o S) → c (M o S) := 
   begin
      intro h4,
      rw contr_o at *,
      exact Barbara₁ h1 h4,
   end,
exact contr h3 h2,
end

/- third-figure syllogisms  -/
lemma Darapti₃ (h1 : P a M) (h2 : S a M) : P i S :=
   Darii₁ h1 (a_conv h2)

lemma Felapton₃ (h1 : P e M) (h2 : S a M) : P o S :=
   Ferio₁ h1 (a_conv h2)

lemma Disamis₃ (h1 : P i M) (h2 : S a M) : P i S :=
   i_conv (Darii₁ h2 (i_conv h1))

lemma Datisi₃ (h1 : P a M) (h2 : S i M) : P i S :=
   Darii₁ h1 (i_conv h2)

lemma Bocardo₃ (h1 : P o M) (h2 : S a M) : P o S :=
-- here a reductio proof is needed
begin
have h3 : c (P o S) → c (P o M) :=
   begin
      intro h4,
      rw contr_o at *,
      exact Barbara₁ h4 h2,
   end,
exact contr h3 h1,
end

lemma Ferison₃ (h1 : P e M) (h2 : S i M) : P o S :=
   Ferio₁ h1 (i_conv h2)


/- Aristotle did not mention the four subaltern syllogisms. In order to prove them,
we state a helpful lemma. -/

lemma subaltrn_e : A e B → A o B :=       --   accidental conversion
begin
intro h,
have h3 : c (A o B) → c (A e B) :=
   begin
      intro h4,
      rw contr_e, rw contr_o at h4,
      exact i_conv (a_conv h4),
   end,
exact contr h3 h,
end


--subaltern first-figure syllogisms that Aristotle did not mention
lemma Barbari (h1: P a M) (h2 : M a S) : P i S :=
   i_conv (a_conv (Barbara₁ h1 h2))

lemma Celaront (h1: P e M) (h2 : M a S) : P o S :=
   subaltrn_e (Celarent₁ h1 h2)


--subaltern second-figure syllogisms that Aristotle did not mention
lemma Cesaro₂ (h1: M e P) (h2 : M a S) : P o S :=
   subaltrn_e (Celarent₁ (e_conv h1) h2)

lemma Camestrop₂ (h1: M a P) (h2 : M e S) : P o S :=
   subaltrn_e (e_conv (Celarent₁ (e_conv h2) h1))


-- Aristotle did not mention the fourth-figure syllogisms
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
   subaltrn_e (e_conv(Celarent₁ h2 h1))

/- Metalogical observations. 
   Aristotle argues that Darii and Ferio do not have to be assumed as axioms, 
   but can be derived from Barbara and Celarent. (An. Pr. 29b1-2])   -/

lemma Darii (h1 : P a M) (h2 : M i S) : P i S :=
begin
have h3 : c (P i S) → c (M i S) :=
   begin
      intro h4,
      rw contr_i at *,
      exact e_conv (Celarent₁ (e_conv h4) h1),
   end,
exact contr h3 h2,
end

lemma Ferio (h1 : P e M) (h2 : M i S) : P o S :=
begin
have h3 : c (P o S) → c (M i S) :=
   begin
      intro h4,
      rw contr_i, rw contr_o at h4,
      exact Celarent₁ (e_conv h1) h4,
   end,
exact contr h3 h2,
end

-- it is even possible to get rid of axiom i_conv

lemma i_conv_deduction : A i B → B i A :=
begin
intro h3,
have h4 : c (B i A) → c (A i B) :=
   begin
      intro h5,
      rw contr_i at *,
      exact e_conv h5
   end,
exact contr h4 h3,
end

/- 
So, Barbara and Celarent together with e-conv and a-conv and contr suffice to 
prove all 24 valid syllogisms; we call this system DR.   -/

/-
************** TODO ****************
1. Aristotle argued for the invalidity of all but 24 syllogisms by semantical means, 
i.e. by providing counterexamples. I would like to prove that all invalid syllogisms 
not be derived; therefore:
a. state some rules that are sufficient to refute all invalid syllogisms;
   see, for instance, Rooij, Robert van, and Kaibo Xie. ‘A Causal Analysis 
   of Modal Syllogisms’. In Monotonicity in Logic and Language, edited by Dun 
   Deng, Fenrong Liu, Mingming Liu, and Dag Westerståhl, p. 187. 
   Lecture Notes in Computer Science. Springer Berlin Heidelberg, 2020.
b. investigate if it is possible to prove these rules in our proof system.

2. To show that there are exactly 256 syllogisms, I would like to give an inductive 
definition of a syllogism, maybe starting with:
   
   inductive assertoric : Type
   | mk : term → copula → term → ass

   inductive syllogism : Prop
   | mk : assertoric → assertoric → assertoric → Prop
But this does not work.
-/