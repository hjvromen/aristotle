/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

variable {α : Type}                     -- type for terms
variables {A B C P S M: α}

constant universal_affirmation (A : α) (B : α) : Prop
local infixr ` a ` : 80 := universal_affirmation

constant universal_denial (A : α) (B : α) : Prop
local infixr ` e ` : 80 := universal_denial

constant particular_affirmation (A : α) (B : α) : Prop
local infixr ` i ` : 80 := particular_affirmation

constant particular_denial (A : α) (B : α) : Prop
local infixr ` o ` : 80 := particular_denial

/- Aristotle uses these seven axioms / deduction rules (→ Malink)
   Corcoran calls this system d   
   System dr is also complete while using only the numbers 1, 2, 5 and 7  (see end of this file for a proof)  -/

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

/-
lemma subaltrn_1: A a B → A i B :=        --   accidental conversion
by intro h; exact i_conv (a_conv h)
-/

lemma subaltrn_2 : A e B → A o B :=       --   accidental conversion
begin
intro h,
by_contra h2,
rw ← contr_1 at h2,
have h4 : B e A, from e_conv h,
rw contr_2 at h4,
show false, from h4 (a_conv h2)
end

/- Aristotle does not use 'extended' deductions (he does not use already proved theorems but only axioms)
The following proofs follow Aristotle's text -/

/-  first-figure syllogisms that Aristotle did not mention -/
lemma Barbari (h1: P a M) (h2 : M a S) : P i S :=
-- this a subalternate mood
   i_conv (a_conv (Barbara₁ h1 h2))

lemma Celaront (h1: P e M) (h2 : M a S) : P o S :=
-- this a subalternate mood
   subaltrn_2 (Celarent₁ h1 h2)

/- second-figure syllogisms -/
lemma Cesare₂ (h1: M e P) (h2 : M a S) : P e S :=
   Celarent₁ (e_conv h1) h2

lemma Camestres₂ (h1: M a P) (h2 : M e S) : P e S :=
   e_conv (Celarent₁ (e_conv h2) h1)

inductive form : Type
| a (A : α → Prop) (B : α → Prop) : form 
| A i B 
| A e B 
| A o B 

@[reducible] def ctx : Type := set (form)
notation AX `∪` φ := set.insert φ AX

inductive syll : form → form → Prop 
| ax {AX} {φ} (h : φ ∈ AX) : prfK AX φ
| pl1 {AX} {φ ψ}           : prfK AX (φ ⊃ (ψ ⊃ φ))
| pl2 {AX} {φ ψ χ}         : prfK AX ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
| pl3 {AX} {φ ψ}           : prfK AX (((¬φ) ⊃ (¬ψ)) ⊃ (((¬φ) ⊃ ψ) ⊃ φ))
| pl4 {AX} {φ ψ}           : prfK AX (φ ⊃ (ψ ⊃ (φ & ψ)))
| pl5 {AX} {φ ψ}           : prfK AX ((φ & ψ) ⊃ φ)
| pl6 {AX} {φ ψ}           : prfK AX ((φ & ψ) ⊃ ψ)
| pl7 {AX} {φ ψ}           : prfK AX (((¬φ) ⊃ (¬ψ)) ⊃ (ψ ⊃ φ))
| kdist {AX} {φ ψ}         : prfK AX ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
| mp {AX} {φ ψ} 
  (hpq: prfK AX (φ ⊃ ψ)) 
  (hp : prfK AX φ)         : prfK AX ψ
| nec {AX} {φ} 
  (hp: prfK AX φ)          : prfK AX (□ φ)