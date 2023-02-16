/-
Copyright (c) 2023 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

/- This is a formalisation of Aristotle's assertoric (non-modal) syllogistic. 
   We start with a syntactical account (language and proof system). 
   After that, in the other files, three differrent semantics are presented, 
   each with a proof of soundness of the proof system. -/

variable {term : Type}                     -- type for terms
variables {A B C P S M: term}
constants {a e i o : term → term → Prop}

infixr ` a ` : 80 := a
infixr ` e ` : 80 := e
infixr ` i ` : 80 := i
infixr ` o ` : 80 := o

-- the 'contradictories'
constant c : Prop → Prop
axiom contr_a : c (A a B) = A o B 
axiom contr_e : c (A e B) = A i B 
axiom contr_i : c (A i B) = A e B 
axiom contr_o : c (A o B) = A a B 


/-- The deductive system that follows Aristotle's text as closely as possible 
    uses eight axioms / deduction rules. (Smith 1989 pp. xix-xx)  -/

-- four 'perfect' syllogisms (we use the traditional medieval names)
axiom Barbara₁ : P a M → M a S → P a S
axiom Celarent₁ : P e M → M a S → P e S
axiom Darii₁ : P a M → M i S → P i S 
axiom Ferio₁ : P e M → M i S → P o S

-- three conversion rules
axiom e_conv : A e B → B e A      --   simple e_conversion
axiom i_conv : A i B → B i A      --   simple i_conversion
axiom a_conv : A a B → B i A      --   accidental a_conversion

-- reductio ad absurdum
axiom contr {p r : Prop} : (c r → c p) → p → r

/-- Aristotle does not use 'extended' deductions, i.e. he does not use already 
    proved theorems but only axioms. The following proofs follow Aristotle's text as closely as 
    possible. -/

-- four second-figure syllogisms
lemma Cesare₂ (h1: M e P) (h2 : M a S) : P e S :=
   Celarent₁ (e_conv h1) h2

lemma Camestres₂ (h1: M a P) (h2 : M e S) : P e S :=
   e_conv (Celarent₁ (e_conv h2) h1)

lemma Festino₂ (h1: M e P) (h2 : M i S) : P o S :=
   Ferio₁ (e_conv h1) h2

lemma Baroco₂ (h1: M a P) (h2 : M o S) : P o S :=
begin
have h3 : c (P o S) → c (M o S) := 
   begin
      intro h4,
      rw contr_o at *,
      exact Barbara₁ h1 h4,
   end,
exact contr h3 h2,
end

-- six third-figure syllogisms  -/
lemma Darapti₃ (h1 : P a M) (h2 : S a M) : P i S :=
   Darii₁ h1 (a_conv h2)

lemma Felapton₃ (h1 : P e M) (h2 : S a M) : P o S :=
   Ferio₁ h1 (a_conv h2)

lemma Disamis₃ (h1 : P i M) (h2 : S a M) : P i S :=
   i_conv (Darii₁ h2 (i_conv h1))

lemma Datisi₃ (h1 : P a M) (h2 : S i M) : P i S :=
   Darii₁ h1 (i_conv h2)

lemma Bocardo₃ (h1 : P o M) (h2 : S a M) : P o S :=
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


/-- Up to now, we have 14 valid syllogisms. There are 10 more. 
    First, we prove the four subaltern syllogisms. 
    In order to prove them, we first prove a helpful lemma. -/

lemma subaltrn_e : A e B → A o B :=       --   accidental e_conversion
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


-- the two subaltern first-figure syllogisms
lemma Barbari (h1: P a M) (h2 : M a S) : P i S :=
   i_conv (a_conv (Barbara₁ h1 h2))

lemma Celaront (h1: P e M) (h2 : M a S) : P o S :=
   subaltrn_e (Celarent₁ h1 h2)


-- the two subaltern second-figure syllogisms
lemma Cesaro₂ (h1: M e P) (h2 : M a S) : P o S :=
   subaltrn_e (Celarent₁ (e_conv h1) h2)

lemma Camestrop₂ (h1: M a P) (h2 : M e S) : P o S :=
   subaltrn_e (e_conv (Celarent₁ (e_conv h2) h1))


/-- Second, we prove the six fourth-figure syllogisms -/

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


/-- Metalogical observations. The proof system is redundant. Aristotle already 
    mentioned that Darii₁ and Ferio₁ do not have to be assumed as axioms, 
    but can be derived from Barbara₁ and Celarent₁ (An. Pr. 29b1-2] 
    in Smith, 1989). This is proven below.   -/

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

/-- It is even possible to derive rule i_conv from the other rules (25a22) -/

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


/- So, Barbara₁ and Celarent₁ together with e-conv and a-conv and contr 
    suffice to prove all 24 valid syllogisms.
    We will refer to this system by the name `DR` in the semantics files.   -/


/- ************** ideas for further research ****************
Aristotle argued for the invalidity of all other syllogisms by semantical means, 
i.e. by providing counterexamples. I would like to prove that all invalid syllogisms 
cannot be derived; therefore:
a. To show that there are exactly 256 syllogisms, I will have to give an inductive 
   definition of a syllogism.
b. Then select some rules that are sufficient to refute all invalid syllogisms;
   see, for instance, van Rooij (2020, p.187).
c. Finally, investigate if it is possible to prove these rules in our proof system.
-/
