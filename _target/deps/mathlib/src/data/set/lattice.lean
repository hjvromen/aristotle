/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

-- QUESTION: can make the first argument in ∀ x ∈ a, ... implicit?
-/
import order.complete_boolean_algebra
import data.sigma.basic
import order.galois_connection
import order.directed

open function tactic set auto

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {ι' : Sort y}

namespace set

instance lattice_set : complete_lattice (set α) :=
{ Sup    := λs, {a | ∃ t ∈ s, a ∈ t },
  Inf    := λs, {a | ∀ t ∈ s, a ∈ t },

  le_Sup := assume s t t_in a a_in, ⟨t, ⟨t_in, a_in⟩⟩,
  Sup_le := assume s t h a ⟨t', ⟨t'_in, a_in⟩⟩, h t' t'_in a_in,

  le_Inf := assume s t h a a_in t' t'_in, h t' t'_in a_in,
  Inf_le := assume s t t_in a h, h _ t_in,

  .. set.boolean_algebra,
  .. (infer_instance : complete_lattice (α → Prop)) }

/-- Image is monotone. See `set.image_image` for the statement in terms of `⊆`. -/
lemma monotone_image {f : α → β} : monotone (image f) :=
assume s t, assume h : s ⊆ t, image_subset _ h

theorem monotone_inter [preorder β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, f x ∩ g x) :=
assume b₁ b₂ h, inter_subset_inter (hf h) (hg h)

theorem monotone_union [preorder β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, f x ∪ g x) :=
assume b₁ b₂ h, union_subset_union (hf h) (hg h)

theorem monotone_set_of [preorder α] {p : α → β → Prop}
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
assume a a' h b, hp b h

section galois_connection
variables {f : α → β}

protected lemma image_preimage : galois_connection (image f) (preimage f) :=
assume a b, image_subset_iff

/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s` -/
def kern_image (f : α → β) (s : set α) : set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}

protected lemma preimage_kern_image : galois_connection (preimage f) (kern_image f) :=
assume a b,
⟨ assume h x hx y hy, have f y ∈ a, from hy.symm ▸ hx, h this,
  assume h x (hx : f x ∈ a), h hx rfl⟩

end galois_connection

/- union and intersection over a family of sets indexed by a type -/

/-- Indexed union of a family of sets -/
@[reducible] def Union (s : ι → set β) : set β := supr s

/-- Indexed intersection of a family of sets -/
@[reducible] def Inter (s : ι → set β) : set β := infi s

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

@[simp] theorem mem_Union {x : β} {s : ι → set β} : x ∈ Union s ↔ ∃ i, x ∈ s i :=
⟨assume ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩, ⟨a, t_eq.symm ▸ h⟩,
  assume ⟨a, h⟩, ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
/- alternative proof: dsimp [Union, supr, Sup]; simp -/
  -- TODO: more rewrite rules wrt forall / existentials and logical connectives
  -- TODO: also eliminate ∃i, ... ∧ i = t ∧ ...

theorem set_of_exists (p : ι → β → Prop) : {x | ∃ i, p i x} = ⋃ i, {x | p i x} :=
ext $ λ i, mem_Union.symm

@[simp] theorem mem_Inter {x : β} {s : ι → set β} : x ∈ Inter s ↔ ∀ i, x ∈ s i :=
⟨assume (h : ∀a ∈ {a : set β | ∃i, s i = a}, x ∈ a) a, h (s a) ⟨a, rfl⟩,
  assume h t ⟨a, (eq : s a = t)⟩, eq ▸ h a⟩

theorem set_of_forall (p : ι → β → Prop) : {x | ∀ i, p i x} = ⋂ i, {x | p i x} :=
ext $ λ i, mem_Inter.symm

theorem Union_subset {s : ι → set β} {t : set β} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
-- TODO: should be simpler when sets' order is based on lattices
@supr_le (set β) _ set.lattice_set _ _ h

theorem Union_subset_iff {s : ι → set β} {t : set β} : (⋃ i, s i) ⊆ t ↔ (∀ i, s i ⊆ t) :=
⟨assume h i, subset.trans (le_supr s _) h, Union_subset⟩

theorem mem_Inter_of_mem {x : β} {s : ι → set β} : (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
mem_Inter.2

theorem subset_Inter {t : set β} {s : ι → set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
-- TODO: should be simpler when sets' order is based on lattices
@le_infi (set β) _ set.lattice_set _ _ h

theorem subset_Inter_iff {t : set β} {s : ι → set β} : t ⊆ (⋂ i, s i) ↔ ∀ i, t ⊆ s i :=
@le_infi_iff (set β) _ set.lattice_set _ _

theorem subset_Union : ∀ (s : ι → set β) (i : ι), s i ⊆ (⋃ i, s i) := le_supr

-- This rather trivial consequence is convenient with `apply`,
-- and has `i` explicit for this use case.
theorem subset_subset_Union
  {A : set β} {s : ι → set β} (i : ι) (h : A ⊆ s i) : A ⊆ ⋃ (i : ι), s i :=
subset.trans h (subset_Union s i)

theorem Inter_subset : ∀ (s : ι → set β) (i : ι), (⋂ i, s i) ⊆ s i := infi_le

lemma Inter_subset_of_subset {s : ι → set α} {t : set α} (i : ι)
  (h : s i ⊆ t) : (⋂ i, s i) ⊆ t :=
set.subset.trans (set.Inter_subset s i) h

lemma Inter_subset_Inter {s t : ι → set α} (h : ∀ i, s i ⊆ t i) :
  (⋂ i, s i) ⊆ (⋂ i, t i) :=
set.subset_Inter $ λ i, set.Inter_subset_of_subset i (h i)

lemma Inter_subset_Inter2 {s : ι → set α} {t : ι' → set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
  (⋂ i, s i) ⊆ (⋂ j, t j) :=
set.subset_Inter $ λ j, let ⟨i, hi⟩ := h j in Inter_subset_of_subset i hi

lemma Inter_set_of (P : ι → α → Prop) : (⋂ i, {x : α | P i x }) = {x : α | ∀ i, P i x} :=
by { ext, simp }

theorem Union_const [nonempty ι] (s : set β) : (⋃ i:ι, s) = s :=
ext $ by simp

theorem Inter_const [nonempty ι] (s : set β) : (⋂ i:ι, s) = s :=
ext $ by simp

@[simp] -- complete_boolean_algebra
theorem compl_Union (s : ι → set β) : (⋃ i, s i)ᶜ = (⋂ i, (s i)ᶜ) :=
ext (by simp)

-- classical -- complete_boolean_algebra
theorem compl_Inter (s : ι → set β) : (⋂ i, s i)ᶜ = (⋃ i, (s i)ᶜ) :=
ext (λ x, by simp [not_forall])

-- classical -- complete_boolean_algebra
theorem Union_eq_comp_Inter_comp (s : ι → set β) : (⋃ i, s i) = (⋂ i, (s i)ᶜ)ᶜ :=
by simp [compl_Inter, compl_compl]

-- classical -- complete_boolean_algebra
theorem Inter_eq_comp_Union_comp (s : ι → set β) : (⋂ i, s i) = (⋃ i, (s i)ᶜ)ᶜ :=
by simp [compl_compl]

theorem inter_Union (s : set β) (t : ι → set β) :
  s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i :=
ext $ by simp

theorem Union_inter (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
ext $ by simp

theorem Union_union_distrib (s : ι → set β) (t : ι → set β) :
  (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ (⋃ i, t i) :=
ext $ by simp [exists_or_distrib]

theorem Inter_inter_distrib (s : ι → set β) (t : ι → set β) :
  (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ (⋂ i, t i) :=
ext $ by simp [forall_and_distrib]

theorem union_Union [nonempty ι] (s : set β) (t : ι → set β) :
  s ∪ (⋃ i, t i) = ⋃ i, s ∪ t i :=
by rw [Union_union_distrib, Union_const]

theorem Union_union [nonempty ι] (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
by rw [Union_union_distrib, Union_const]

theorem inter_Inter [nonempty ι] (s : set β) (t : ι → set β) :
  s ∩ (⋂ i, t i) = ⋂ i, s ∩ t i :=
by rw [Inter_inter_distrib, Inter_const]

theorem Inter_inter [nonempty ι] (s : set β) (t : ι → set β) :
  (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
by rw [Inter_inter_distrib, Inter_const]

-- classical
theorem union_Inter (s : set β) (t : ι → set β) :
  s ∪ (⋂ i, t i) = ⋂ i, s ∪ t i :=
ext $ assume x, by simp [forall_or_distrib_left]

theorem Union_diff (s : set β) (t : ι → set β) :
  (⋃ i, t i) \ s = ⋃ i, t i \ s :=
Union_inter _ _

theorem diff_Union [nonempty ι] (s : set β) (t : ι → set β) :
  s \ (⋃ i, t i) = ⋂ i, s \ t i :=
by rw [diff_eq, compl_Union, inter_Inter]; refl

theorem diff_Inter (s : set β) (t : ι → set β) :
  s \ (⋂ i, t i) = ⋃ i, s \ t i :=
by rw [diff_eq, compl_Inter, inter_Union]; refl

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊆) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp only [directed_on, exists_prop, mem_Union, exists_imp_distrib]; exact
assume a₁ b₁ fb₁ a₂ b₂ fb₂,
let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) in
⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

lemma Union_inter_subset {ι α} {s t : ι → set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ (⋃ i, t i) :=
by { rintro x ⟨_, ⟨i, rfl⟩, ⟨xs, xt⟩⟩, exact ⟨⟨_, ⟨i, rfl⟩, xs⟩, ⟨_, ⟨i, rfl⟩, xt⟩⟩ }

lemma Union_inter_of_monotone {ι α} [semilattice_sup ι] {s t : ι → set α}
  (hs : monotone s) (ht : monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ (⋃ i, t i) :=
begin
  ext x, refine ⟨λ hx, Union_inter_subset hx, _⟩,
  rintro ⟨⟨_, ⟨i, rfl⟩, xs⟩, ⟨_, ⟨j, rfl⟩, xt⟩⟩,
  exact ⟨_, ⟨i ⊔ j, rfl⟩, ⟨hs le_sup_left xs, ht le_sup_right xt⟩⟩
end

/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
lemma Union_Inter_subset {ι ι' α} {s : ι → ι' → set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
by { rintro x ⟨_, ⟨i, rfl⟩, hx⟩ _ ⟨j, rfl⟩, exact ⟨_, ⟨i, rfl⟩, hx _ ⟨j, rfl⟩⟩ }

/- bounded unions and intersections -/

theorem mem_bUnion_iff {s : set α} {t : α → set β} {y : β} :
  y ∈ (⋃ x ∈ s, t x) ↔ ∃ x ∈ s, y ∈ t x := by simp

theorem mem_bInter_iff {s : set α} {t : α → set β} {y : β} :
  y ∈ (⋂ x ∈ s, t x) ↔ ∀ x ∈ s, y ∈ t x := by simp

theorem mem_bUnion {s : set α} {t : α → set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
  y ∈ ⋃ x ∈ s, t x :=
by simp; exact ⟨x, ⟨xs, ytx⟩⟩

theorem mem_bInter {s : set α} {t : α → set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
  y ∈ ⋂ x ∈ s, t x :=
by simp; assumption

theorem bUnion_subset {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, u x ⊆ t) :
  (⋃ x ∈ s, u x) ⊆ t :=
show (⨆ x ∈ s, u x) ≤ t, -- TODO: should not be necessary when sets' order is based on lattices
  from supr_le $ assume x, supr_le (h x)

theorem subset_bInter {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, t ⊆ u x) :
  t ⊆ (⋂ x ∈ s, u x) :=
subset_Inter $ assume x, subset_Inter $ h x

theorem subset_bUnion_of_mem {s : set α} {u : α → set β} {x : α} (xs : x ∈ s) :
  u x ⊆ (⋃ x ∈ s, u x) :=
show u x ≤ (⨆ x ∈ s, u x),
  from le_supr_of_le x $ le_supr _ xs

theorem bInter_subset_of_mem {s : set α} {t : α → set β} {x : α} (xs : x ∈ s) :
  (⋂ x ∈ s, t x) ⊆ t x :=
show (⨅x ∈ s, t x) ≤ t x,
  from infi_le_of_le x $ infi_le _ xs

theorem bUnion_subset_bUnion_left {s s' : set α} {t : α → set β}
  (h : s ⊆ s') : (⋃ x ∈ s, t x) ⊆ (⋃ x ∈ s', t x) :=
bUnion_subset (λ x xs, subset_bUnion_of_mem (h xs))

theorem bInter_subset_bInter_left {s s' : set α} {t : α → set β}
  (h : s' ⊆ s) : (⋂ x ∈ s, t x) ⊆ (⋂ x ∈ s', t x) :=
subset_bInter (λ x xs, bInter_subset_of_mem (h xs))

theorem bUnion_subset_bUnion_right {s : set α} {t1 t2 : α → set β}
  (h : ∀ x ∈ s, t1 x ⊆ t2 x) : (⋃ x ∈ s, t1 x) ⊆ (⋃ x ∈ s, t2 x) :=
bUnion_subset (λ x xs, subset.trans (h x xs) (subset_bUnion_of_mem xs))

theorem bInter_subset_bInter_right {s : set α} {t1 t2 : α → set β}
  (h : ∀ x ∈ s, t1 x ⊆ t2 x) : (⋂ x ∈ s, t1 x) ⊆ (⋂ x ∈ s, t2 x) :=
subset_bInter (λ x xs, subset.trans (bInter_subset_of_mem xs) (h x xs))

theorem bUnion_subset_bUnion {γ : Type*} {s : set α} {t : α → set β} {s' : set γ} {t' : γ → set β}
  (h : ∀ x ∈ s, ∃ y ∈ s', t x ⊆ t' y) :
  (⋃ x ∈ s, t x) ⊆ (⋃ y ∈ s', t' y) :=
begin
  intros x,
  simp only [mem_Union],
  rintros ⟨a, a_in, ha⟩,
  rcases h a a_in with ⟨c, c_in, hc⟩,
  exact ⟨c, c_in, hc ha⟩
end

theorem bInter_mono' {s s' : set α} {t t' : α → set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
  (⋂ x ∈ s', t x) ⊆ (⋂ x ∈ s, t' x) :=
begin
  intros x x_in,
  simp only [mem_Inter] at *,
  exact λ a a_in, h a a_in $ x_in _ (hs a_in)
end

theorem bInter_mono {s : set α} {t t' : α → set β} (h : ∀ x ∈ s, t x ⊆ t' x) :
  (⋂ x ∈ s, t x) ⊆ (⋂ x ∈ s, t' x) :=
bInter_mono' (subset.refl s) h

theorem bUnion_mono {s : set α} {t t' : α → set β} (h : ∀ x ∈ s, t x ⊆ t' x) :
  (⋃ x ∈ s, t x) ⊆ (⋃ x ∈ s, t' x) :=
bUnion_subset_bUnion (λ x x_in, ⟨x, x_in, h x x_in⟩)

theorem bUnion_eq_Union (s : set α) (t : Π x ∈ s, set β) :
  (⋃ x ∈ s, t x ‹_›) = (⋃ x : s, t x x.2) :=
supr_subtype'

theorem bInter_eq_Inter (s : set α) (t : Π x ∈ s, set β) :
  (⋂ x ∈ s, t x ‹_›) = (⋂ x : s, t x x.2) :=
infi_subtype'

theorem bInter_empty (u : α → set β) : (⋂ x ∈ (∅ : set α), u x) = univ :=
show (⨅x ∈ (∅ : set α), u x) = ⊤, -- simplifier should be able to rewrite x ∈ ∅ to false.
  from infi_emptyset

theorem bInter_univ (u : α → set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
infi_univ

-- TODO(Jeremy): here is an artifact of the the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.

@[simp] theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : set α), s x) = s a :=
show (⨅ x ∈ ({a} : set α), s x) = s a, by simp

theorem bInter_union (s t : set α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
show (⨅ x ∈ s ∪ t, u x) = (⨅ x ∈ s, u x) ⊓ (⨅ x ∈ t, u x),
  from infi_union

-- TODO(Jeremy): simp [insert_eq, bInter_union] doesn't work
@[simp] theorem bInter_insert (a : α) (s : set α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
begin rw insert_eq, simp [bInter_union] end

-- TODO(Jeremy): another example of where an annotation is needed

theorem bInter_pair (a b : α) (s : α → set β) :
  (⋂ x ∈ ({a, b} : set α), s x) = s a ∩ s b :=
by simp [inter_comm]

theorem bUnion_empty (s : α → set β) : (⋃ x ∈ (∅ : set α), s x) = ∅ :=
supr_emptyset

theorem bUnion_univ (s : α → set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
supr_univ

@[simp] theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : set α), s x) = s a :=
supr_singleton

@[simp] theorem bUnion_of_singleton (s : set α) : (⋃ x ∈ s, {x}) = s :=
ext $ by simp

theorem bUnion_union (s t : set α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

-- TODO(Jeremy): once again, simp doesn't do it alone.

@[simp] theorem bUnion_insert (a : α) (s : set α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
begin rw [insert_eq], simp [bUnion_union] end

theorem bUnion_pair (a b : α) (s : α → set β) :
  (⋃ x ∈ ({a, b} : set α), s x) = s a ∪ s b :=
by simp [union_comm]

@[simp] -- complete_boolean_algebra
theorem compl_bUnion (s : set α) (t : α → set β) : (⋃ i ∈ s, t i)ᶜ = (⋂ i ∈ s, (t i)ᶜ) :=
ext (λ x, by simp)

-- classical -- complete_boolean_algebra
theorem compl_bInter (s : set α) (t : α → set β) : (⋂ i ∈ s, t i)ᶜ = (⋃ i ∈ s, (t i)ᶜ) :=
ext (λ x, by simp [not_forall])

theorem inter_bUnion (s : set α) (t : α → set β) (u : set β) :
  u ∩ (⋃ i ∈ s, t i) = ⋃ i ∈ s, u ∩ t i :=
begin
  ext x,
  simp only [exists_prop, mem_Union, mem_inter_eq],
  exact ⟨λ ⟨hx, ⟨i, is, xi⟩⟩, ⟨i, is, hx, xi⟩, λ ⟨i, is, hx, xi⟩, ⟨hx, ⟨i, is, xi⟩⟩⟩
end

theorem bUnion_inter (s : set α) (t : α → set β) (u : set β) :
  (⋃ i ∈ s, t i) ∩ u = (⋃ i ∈ s, t i ∩ u) :=
by simp [@inter_comm _ _ u, inter_bUnion]

/-- Intersection of a set of sets. -/
@[reducible] def sInter (S : set (set α)) : set α := Inf S

prefix `⋂₀`:110 := sInter

theorem mem_sUnion_of_mem {x : α} {t : set α} {S : set (set α)} (hx : x ∈ t) (ht : t ∈ S) :
  x ∈ ⋃₀ S :=
⟨t, ⟨ht, hx⟩⟩

theorem mem_sUnion {x : α} {S : set (set α)} : x ∈ ⋃₀ S ↔ ∃t ∈ S, x ∈ t := iff.rfl

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : set α} {S : set (set α)}
  (hx : x ∉ ⋃₀ S) (ht : t ∈ S) : x ∉ t :=
λ h, hx ⟨t, ht, h⟩

@[simp] theorem mem_sInter {x : α} {S : set (set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := iff.rfl

theorem sInter_subset_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
Inf_le tS

theorem subset_sUnion_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
le_Sup tS

lemma subset_sUnion_of_subset {s : set α} (t : set (set α)) (u : set α) (h₁ : s ⊆ u)
  (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t' ⊆ t) : (⋃₀ S) ⊆ t :=
Sup_le h

theorem sUnion_subset_iff {s : set (set α)} {t : set α} : ⋃₀ s ⊆ t ↔ ∀t' ∈ s, t' ⊆ t :=
⟨assume h t' ht', subset.trans (subset_sUnion_of_mem ht') h, sUnion_subset⟩

theorem subset_sInter {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t ⊆ t') : t ⊆ (⋂₀ S) :=
le_Inf h

theorem sUnion_subset_sUnion {S T : set (set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
sUnion_subset $ λ s hs, subset_sUnion_of_mem (h hs)

theorem sInter_subset_sInter {S T : set (set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
subset_sInter $ λ s hs, sInter_subset_of_mem (h hs)

@[simp] theorem sUnion_empty : ⋃₀ ∅ = (∅ : set α) := Sup_empty

@[simp] theorem sInter_empty : ⋂₀ ∅ = (univ : set α) := Inf_empty

@[simp] theorem sUnion_singleton (s : set α) : ⋃₀ {s} = s := Sup_singleton

@[simp] theorem sInter_singleton (s : set α) : ⋂₀ {s} = s := Inf_singleton

@[simp] theorem sUnion_eq_empty {S : set (set α)} : (⋃₀ S) = ∅ ↔ ∀ s ∈ S, s = ∅ := Sup_eq_bot

@[simp] theorem sInter_eq_univ {S : set (set α)} : (⋂₀ S) = univ ↔ ∀ s ∈ S, s = univ := Inf_eq_top

@[simp] theorem nonempty_sUnion {S : set (set α)} : (⋃₀ S).nonempty ↔ ∃ s ∈ S, set.nonempty s :=
by simp [← ne_empty_iff_nonempty]

lemma nonempty.of_sUnion {s : set (set α)} (h : (⋃₀ s).nonempty) : s.nonempty :=
let ⟨s, hs, _⟩ := nonempty_sUnion.1 h in ⟨s, hs⟩

lemma nonempty.of_sUnion_eq_univ [nonempty α] {s : set (set α)} (h : ⋃₀ s = univ) : s.nonempty :=
nonempty.of_sUnion $ h.symm ▸ univ_nonempty

theorem sUnion_union (S T : set (set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T := Sup_union

theorem sInter_union (S T : set (set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T := Inf_union

theorem sInter_Union (s : ι → set (set α)) : ⋂₀ (⋃ i, s i) = ⋂ i, ⋂₀ s i :=
begin
  ext x,
  simp only [mem_Union, mem_Inter, mem_sInter, exists_imp_distrib],
  split ; tauto
end

@[simp] theorem sUnion_insert (s : set α) (T : set (set α)) : ⋃₀ (insert s T) = s ∪ ⋃₀ T := Sup_insert

@[simp] theorem sInter_insert (s : set α) (T : set (set α)) : ⋂₀ (insert s T) = s ∩ ⋂₀ T := Inf_insert

theorem sUnion_pair (s t : set α) : ⋃₀ {s, t} = s ∪ t :=
Sup_pair

theorem sInter_pair (s t : set α) : ⋂₀ {s, t} = s ∩ t :=
Inf_pair

@[simp] theorem sUnion_image (f : α → set β) (s : set α) : ⋃₀ (f '' s) = ⋃ x ∈ s, f x := Sup_image

@[simp] theorem sInter_image (f : α → set β) (s : set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x := Inf_image

@[simp] theorem sUnion_range (f : ι → set β) : ⋃₀ (range f) = ⋃ x, f x := rfl

@[simp] theorem sInter_range (f : ι → set β) : ⋂₀ (range f) = ⋂ x, f x := rfl

lemma sUnion_eq_univ_iff {c : set (set α)} :
  ⋃₀ c = @set.univ α ↔ ∀ a, ∃ b ∈ c, a ∈ b :=
⟨λ H a, let ⟨b, hm, hb⟩ := mem_sUnion.1 $ by rw H; exact mem_univ a in ⟨b, hm, hb⟩,
 λ H, set.univ_subset_iff.1 $ λ x hx, let ⟨b, hm, hb⟩ := H x in set.mem_sUnion_of_mem hb hm⟩

theorem compl_sUnion (S : set (set α)) :
  (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
ext $ λ x, by simp

-- classical
theorem sUnion_eq_compl_sInter_compl (S : set (set α)) :
  ⋃₀ S = (⋂₀ (compl '' S))ᶜ :=
by rw [←compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : set (set α)) :
  (⋂₀ S)ᶜ = ⋃₀ (compl '' S) :=
by rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_comp_sUnion_compl (S : set (set α)) :
   ⋂₀ S = (⋃₀ (compl '' S))ᶜ :=
by rw [←compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : set α} {S : set (set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) :
  s ∩ t = ∅ :=
eq_empty_of_subset_empty $ by rw ← h; exact
inter_subset_inter_right _ (subset_sUnion_of_mem hs)

theorem range_sigma_eq_Union_range {γ : α → Type*} (f : sigma γ → β) :
  range f = ⋃ a, range (λ b, f ⟨a, b⟩) :=
set.ext $ by simp

theorem Union_eq_range_sigma (s : α → set β) : (⋃ i, s i) = range (λ a : Σ i, s i, a.2) :=
by simp [set.ext_iff]

theorem Union_image_preimage_sigma_mk_eq_self {ι : Type*} {σ : ι → Type*} (s : set (sigma σ)) :
  (⋃ i, sigma.mk i '' (sigma.mk i ⁻¹' s)) = s :=
begin
  ext x,
  simp only [mem_Union, mem_image, mem_preimage],
  split,
  { rintros ⟨i, a, h, rfl⟩, exact h },
  { intro h, cases x with i a, exact ⟨i, a, h, rfl⟩ }
end

lemma sUnion_mono {s t : set (set α)} (h : s ⊆ t) : (⋃₀ s) ⊆ (⋃₀ t) :=
sUnion_subset $ assume t' ht', subset_sUnion_of_mem $ h ht'

lemma Union_subset_Union {s t : ι → set α} (h : ∀i, s i ⊆ t i) : (⋃i, s i) ⊆ (⋃i, t i) :=
@supr_le_supr (set α) ι _ s t h

lemma Union_subset_Union2 {ι₂ : Sort*} {s : ι → set α} {t : ι₂ → set α} (h : ∀i, ∃j, s i ⊆ t j) :
  (⋃i, s i) ⊆ (⋃i, t i) :=
@supr_le_supr2 (set α) ι ι₂ _ s t h

lemma Union_subset_Union_const {ι₂ : Sort x} {s : set α} (h : ι → ι₂) : (⋃ i:ι, s) ⊆ (⋃ j:ι₂, s) :=
@supr_le_supr_const (set α) ι ι₂ _ s h

@[simp] lemma Union_of_singleton (α : Type u) : (⋃(x : α), {x}) = @set.univ α :=
ext $ λ x, ⟨λ h, ⟨⟩, λ h, ⟨{x}, ⟨⟨x, rfl⟩, mem_singleton x⟩⟩⟩

theorem bUnion_subset_Union (s : set α) (t : α → set β) :
  (⋃ x ∈ s, t x) ⊆ (⋃ x, t x) :=
Union_subset_Union $ λ i, Union_subset $ λ h, by refl

lemma sUnion_eq_bUnion {s : set (set α)} : (⋃₀ s) = (⋃ (i : set α) (h : i ∈ s), i) :=
by rw [← sUnion_image, image_id']

lemma sInter_eq_bInter {s : set (set α)} : (⋂₀ s) = (⋂ (i : set α) (h : i ∈ s), i) :=
by rw [← sInter_image, image_id']

lemma sUnion_eq_Union {s : set (set α)} : (⋃₀ s) = (⋃ (i : s), i) :=
by simp only [←sUnion_range, subtype.range_coe]

lemma sInter_eq_Inter {s : set (set α)} : (⋂₀ s) = (⋂ (i : s), i) :=
by simp only [←sInter_range, subtype.range_coe]

lemma union_eq_Union {s₁ s₂ : set α} : s₁ ∪ s₂ = ⋃ b : bool, cond b s₁ s₂ :=
set.ext $ λ x, by simp [bool.exists_bool, or_comm]

lemma inter_eq_Inter {s₁ s₂ : set α} : s₁ ∩ s₂ = ⋂ b : bool, cond b s₁ s₂ :=
set.ext $ λ x, by simp [bool.forall_bool, and_comm]

instance : complete_boolean_algebra (set α) :=
{ compl               := compl,
  sdiff               := (\),
  infi_sup_le_sup_Inf := assume s t x, show x ∈ (⋂ b ∈ t, s ∪ b) → x ∈ s ∪ (⋂₀ t),
    by simp; exact assume h,
      or.imp_right
        (assume hn : x ∉ s, assume i hi, or.resolve_left (h i hi) hn)
        (classical.em $ x ∈ s),
  inf_Sup_le_supr_inf := assume s t x, show x ∈ s ∩ (⋃₀ t) → x ∈ (⋃ b ∈ t, s ∩ b),
    by simp [-and_imp, and.left_comm],
  .. set.boolean_algebra, .. set.lattice_set }

lemma sInter_union_sInter {S T : set (set α)} :
  (⋂₀S) ∪ (⋂₀T) = (⋂p ∈ S.prod T, (p : (set α) × (set α)).1 ∪ p.2) :=
Inf_sup_Inf

lemma sUnion_inter_sUnion {s t : set (set α)} :
  (⋃₀s) ∩ (⋃₀t) = (⋃p ∈ s.prod t, (p : (set α) × (set α )).1 ∩ p.2) :=
Sup_inf_Sup

/-- If `S` is a set of sets, and each `s ∈ S` can be represented as an intersection
of sets `T s hs`, then `⋂₀ S` is the intersection of the union of all `T s hs`. -/
lemma sInter_bUnion {S : set (set α)} {T : Π s ∈ S, set (set α)} (hT : ∀s∈S, s = ⋂₀ T s ‹s ∈ S›) :
  ⋂₀ (⋃s∈S, T s ‹_›) = ⋂₀ S :=
begin
  ext,
  simp only [and_imp, exists_prop, set.mem_sInter, set.mem_Union, exists_imp_distrib],
  split,
  { assume H s sS,
    rw [hT s sS, mem_sInter],
    assume t tTs,
    exact H t s sS tTs },
  { assume H t s sS tTs,
    suffices : s ⊆ t, exact this (H s sS),
    rw [hT s sS, sInter_eq_bInter],
    exact bInter_subset_of_mem tTs }
end

/-- If `S` is a set of sets, and each `s ∈ S` can be represented as an union
of sets `T s hs`, then `⋃₀ S` is the union of the union of all `T s hs`. -/
lemma sUnion_bUnion {S : set (set α)} {T : Π s ∈ S, set (set α)} (hT : ∀s∈S, s = ⋃₀ T s ‹_›) :
  ⋃₀ (⋃s∈S, T s ‹_›) = ⋃₀ S :=
begin
  ext,
  simp only [exists_prop, set.mem_Union, set.mem_set_of_eq],
  split,
  { rintros ⟨t, ⟨⟨s, ⟨sS, tTs⟩⟩, xt⟩⟩,
    refine ⟨s, ⟨sS, _⟩⟩,
    rw hT s sS,
    exact subset_sUnion_of_mem tTs xt },
  { rintros ⟨s, ⟨sS, xs⟩⟩,
    rw hT s sS at xs,
    rcases mem_sUnion.1 xs with ⟨t, tTs, xt⟩,
    exact ⟨t, ⟨⟨s, ⟨sS, tTs⟩⟩, xt⟩⟩ }
end

lemma Union_range_eq_sUnion {α β : Type*} (C : set (set α))
  {f : ∀(s : C), β → s} (hf : ∀(s : C), surjective (f s)) :
  (⋃(y : β), range (λ(s : C), (f s y).val)) = ⋃₀ C :=
begin
  ext x, split,
  { rintro ⟨s, ⟨y, rfl⟩, ⟨⟨s, hs⟩, rfl⟩⟩, refine ⟨_, hs, _⟩, exact (f ⟨s, hs⟩ y).2 },
  { rintro ⟨s, hs, hx⟩, cases hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy, refine ⟨_, ⟨y, rfl⟩, ⟨⟨s, hs⟩, _⟩⟩,
    exact congr_arg subtype.val hy }
end

lemma Union_range_eq_Union {ι α β : Type*} (C : ι → set α)
  {f : ∀(x : ι), β → C x} (hf : ∀(x : ι), surjective (f x)) :
  (⋃(y : β), range (λ(x : ι), (f x y).val)) = ⋃x, C x :=
begin
  ext x, rw [mem_Union, mem_Union], split,
  { rintro ⟨y, ⟨i, rfl⟩⟩, exact ⟨i, (f i y).2⟩ },
  { rintro ⟨i, hx⟩, cases hf i ⟨x, hx⟩ with y hy, refine ⟨y, ⟨i, congr_arg subtype.val hy⟩⟩ }
end

lemma union_distrib_Inter_right {ι : Type*} (s : ι → set α) (t : set α) :
  (⋂ i, s i) ∪ t = (⋂ i, s i ∪ t) :=
begin
  ext x,
  rw [mem_union_eq, mem_Inter],
  split ; finish
end

lemma union_distrib_Inter_left {ι : Type*} (s : ι → set α) (t : set α) :
  t ∪ (⋂ i, s i) = (⋂ i, t ∪ s i) :=
begin
  rw [union_comm, union_distrib_Inter_right],
  simp [union_comm]
end

section function
/-!
### `maps_to`
-/

lemma maps_to_sUnion {S : set (set α)} {t : set β} {f : α → β} (H : ∀ s ∈ S, maps_to f s t) :
  maps_to f (⋃₀ S) t :=
λ x ⟨s, hs, hx⟩, H s hs hx

lemma maps_to_Union {s : ι → set α} {t : set β} {f : α → β} (H : ∀ i, maps_to f (s i) t) :
  maps_to f (⋃ i, s i) t :=
maps_to_sUnion $ forall_range_iff.2 H

lemma maps_to_bUnion {p : ι → Prop} {s : Π (i : ι) (hi : p i), set α} {t : set β} {f : α → β}
  (H : ∀ i hi, maps_to f (s i hi) t) :
  maps_to f (⋃ i hi, s i hi) t :=
maps_to_Union $ λ i, maps_to_Union (H i)

lemma maps_to_Union_Union {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, maps_to f (s i) (t i)) :
  maps_to f (⋃ i, s i) (⋃ i, t i) :=
maps_to_Union $ λ i, (H i).mono (subset.refl _) (subset_Union t i)

lemma maps_to_bUnion_bUnion {p : ι → Prop} {s : Π i (hi : p i), set α} {t : Π i (hi : p i), set β}
  {f : α → β} (H : ∀ i hi, maps_to f (s i hi) (t i hi)) :
  maps_to f (⋃ i hi, s i hi) (⋃ i hi, t i hi) :=
maps_to_Union_Union $ λ i, maps_to_Union_Union (H i)

lemma maps_to_sInter {s : set α} {T : set (set β)} {f : α → β} (H : ∀ t ∈ T, maps_to f s t) :
  maps_to f s (⋂₀ T) :=
λ x hx t ht, H t ht hx

lemma maps_to_Inter {s : set α} {t : ι → set β} {f : α → β} (H : ∀ i, maps_to f s (t i)) :
  maps_to f s (⋂ i, t i) :=
λ x hx, mem_Inter.2 $ λ i, H i hx

lemma maps_to_bInter {p : ι → Prop} {s : set α} {t : Π i (hi : p i), set β} {f : α → β}
  (H : ∀ i hi, maps_to f s (t i hi)) :
  maps_to f s (⋂ i hi, t i hi) :=
maps_to_Inter $ λ i, maps_to_Inter (H i)

lemma maps_to_Inter_Inter {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, maps_to f (s i) (t i)) :
  maps_to f (⋂ i, s i) (⋂ i, t i) :=
maps_to_Inter $ λ i, (H i).mono (Inter_subset s i) (subset.refl _)

lemma maps_to_bInter_bInter {p : ι → Prop} {s : Π i (hi : p i), set α}
  {t : Π i (hi : p i), set β} {f : α → β} (H : ∀ i hi, maps_to f (s i hi) (t i hi)) :
  maps_to f (⋂ i hi, s i hi) (⋂ i hi, t i hi) :=
maps_to_Inter_Inter $ λ i, maps_to_Inter_Inter (H i)

lemma image_Inter_subset (s : ι → set α) (f : α → β) :
  f '' (⋂ i, s i) ⊆ ⋂ i, f '' (s i) :=
(maps_to_Inter_Inter $ λ i, maps_to_image f (s i)).image_subset

lemma image_bInter_subset {p : ι → Prop} (s : Π i (hi : p i), set α) (f : α → β) :
  f '' (⋂ i hi, s i hi) ⊆ ⋂ i hi, f '' (s i hi) :=
(maps_to_bInter_bInter $ λ i hi, maps_to_image f (s i hi)).image_subset

lemma image_sInter_subset (S : set (set α)) (f : α → β) :
  f '' (⋂₀ S) ⊆ ⋂ s ∈ S, f '' s :=
by { rw sInter_eq_bInter, apply image_bInter_subset }

/-!
### `inj_on`
-/

lemma inj_on.image_Inter_eq [nonempty ι] {s : ι → set α} {f : α → β} (h : inj_on f (⋃ i, s i)) :
  f '' (⋂ i, s i) = ⋂ i, f '' (s i) :=
begin
  inhabit ι,
  refine subset.antisymm (image_Inter_subset s f) (λ y hy, _),
  simp only [mem_Inter, mem_image_iff_bex] at hy,
  choose x hx hy using hy,
  refine ⟨x (default ι), mem_Inter.2 $ λ i, _, hy _⟩,
  suffices : x (default ι) = x i,
  { rw this, apply hx },
  replace hx : ∀ i, x i ∈ ⋃ j, s j := λ i, (subset_Union _ _) (hx i),
  apply h (hx _) (hx _),
  simp only [hy]
end

lemma inj_on.image_bInter_eq {p : ι → Prop} {s : Π i (hi : p i), set α} (hp : ∃ i, p i) {f : α → β}
  (h : inj_on f (⋃ i hi, s i hi)) :
  f '' (⋂ i hi, s i hi) = ⋂ i hi, f '' (s i hi) :=
begin
  simp only [Inter, infi_subtype'],
  haveI : nonempty {i // p i} := nonempty_subtype.2 hp,
  apply inj_on.image_Inter_eq,
  simpa only [Union, supr_subtype'] using h
end

lemma inj_on_Union_of_directed {s : ι → set α} (hs : directed (⊆) s)
  {f : α → β} (hf : ∀ i, inj_on f (s i)) :
  inj_on f (⋃ i, s i) :=
begin
  intros x hx y hy hxy,
  rcases mem_Union.1 hx with ⟨i, hx⟩,
  rcases mem_Union.1 hy with ⟨j, hy⟩,
  rcases hs i j with ⟨k, hi, hj⟩,
  exact hf k (hi hx) (hj hy) hxy
end

/-!
### `surj_on`
-/

lemma surj_on_sUnion {s : set α} {T : set (set β)} {f : α → β} (H : ∀ t ∈ T, surj_on f s t) :
  surj_on f s (⋃₀ T) :=
λ x ⟨t, ht, hx⟩, H t ht hx

lemma surj_on_Union {s : set α} {t : ι → set β} {f : α → β} (H : ∀ i, surj_on f s (t i)) :
  surj_on f s (⋃ i, t i) :=
surj_on_sUnion $ forall_range_iff.2 H

lemma surj_on_Union_Union {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) (t i)) :
  surj_on f (⋃ i, s i) (⋃ i, t i) :=
surj_on_Union $ λ i, (H i).mono (subset_Union _ _) (subset.refl _)

lemma surj_on_bUnion {p : ι → Prop} {s : set α} {t : Π i (hi : p i), set β} {f : α → β}
  (H : ∀ i hi, surj_on f s (t i hi)) :
  surj_on f s (⋃ i hi, t i hi) :=
surj_on_Union $ λ i, surj_on_Union (H i)

lemma surj_on_bUnion_bUnion {p : ι → Prop} {s : Π i (hi : p i), set α} {t : Π i (hi : p i), set β}
  {f : α → β} (H : ∀ i hi, surj_on f (s i hi) (t i hi)) :
  surj_on f (⋃ i hi, s i hi) (⋃ i hi, t i hi) :=
surj_on_Union_Union $ λ i, surj_on_Union_Union (H i)

lemma surj_on_Inter [hi : nonempty ι] {s : ι → set α} {t : set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) t) (Hinj : inj_on f (⋃ i, s i)) :
  surj_on f (⋂ i, s i) t :=
begin
  intros y hy,
  rw [Hinj.image_Inter_eq, mem_Inter],
  exact λ i, H i hy
end

lemma surj_on_Inter_Inter [hi : nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, surj_on f (s i) (t i)) (Hinj : inj_on f (⋃ i, s i)) :
  surj_on f (⋂ i, s i) (⋂ i, t i) :=
surj_on_Inter (λ i, (H i).mono (subset.refl _) (Inter_subset _ _)) Hinj

/-!
### `bij_on`
-/

lemma bij_on_Union {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ i, bij_on f (s i) (t i))
  (Hinj : inj_on f (⋃ i, s i)) :
  bij_on f (⋃ i, s i) (⋃ i, t i) :=
⟨maps_to_Union_Union $ λ i, (H i).maps_to, Hinj, surj_on_Union_Union $ λ i, (H i).surj_on⟩

lemma bij_on_Inter [hi :nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β}
  (H : ∀ i, bij_on f (s i) (t i)) (Hinj : inj_on f (⋃ i, s i)) :
  bij_on f (⋂ i, s i) (⋂ i, t i) :=
⟨maps_to_Inter_Inter $ λ i, (H i).maps_to, hi.elim $ λ i, (H i).inj_on.mono (Inter_subset _ _),
  surj_on_Inter_Inter (λ i, (H i).surj_on) Hinj⟩

lemma bij_on_Union_of_directed {s : ι → set α} (hs : directed (⊆) s) {t : ι → set β} {f : α → β}
  (H : ∀ i, bij_on f (s i) (t i)) :
  bij_on f (⋃ i, s i) (⋃ i, t i) :=
bij_on_Union H $ inj_on_Union_of_directed hs (λ i, (H i).inj_on)

lemma bij_on_Inter_of_directed [nonempty ι] {s : ι → set α} (hs : directed (⊆) s) {t : ι → set β}
  {f : α → β} (H : ∀ i, bij_on f (s i) (t i)) :
  bij_on f (⋂ i, s i) (⋂ i, t i) :=
bij_on_Inter H $ inj_on_Union_of_directed hs (λ i, (H i).inj_on)

end function

section

variables {p : Prop} {μ : p → set α}

@[simp] lemma Inter_pos (hp : p) : (⋂h:p, μ h) = μ hp := infi_pos hp

@[simp] lemma Inter_neg (hp : ¬ p) : (⋂h:p, μ h) = univ := infi_neg hp

@[simp] lemma Union_pos (hp : p) : (⋃h:p, μ h) = μ hp := supr_pos hp

@[simp] lemma Union_neg (hp : ¬ p) : (⋃h:p, μ h) = ∅ := supr_neg hp

@[simp] lemma Union_empty : (⋃i:ι, ∅:set α) = ∅ := supr_bot

@[simp] lemma Inter_univ : (⋂i:ι, univ:set α) = univ := infi_top

variables {s : ι → set α}

@[simp] lemma Union_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ := supr_eq_bot

@[simp] lemma Inter_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ := infi_eq_top

@[simp] lemma nonempty_Union : (⋃ i, s i).nonempty ↔ ∃ i, (s i).nonempty :=
by simp [← ne_empty_iff_nonempty]

end

section image

lemma image_Union {f : α → β} {s : ι → set α} : f '' (⋃ i, s i) = (⋃i, f '' s i) :=
begin
  apply set.ext, intro x,
  simp [image, exists_and_distrib_right.symm, -exists_and_distrib_right],
  exact exists_swap
end

lemma univ_subtype {p : α → Prop} : (univ : set (subtype p)) = (⋃x (h : p x), {⟨x, h⟩})  :=
set.ext $ assume ⟨x, h⟩, by simp [h]

lemma range_eq_Union {ι} (f : ι → α) : range f = (⋃i, {f i}) :=
set.ext $ assume a, by simp [@eq_comm α a]

lemma image_eq_Union (f : α → β) (s : set α) : f '' s = (⋃i∈s, {f i}) :=
set.ext $ assume b, by simp [@eq_comm β b]

@[simp] lemma bUnion_range {f : ι → α} {g : α → set β} : (⋃x ∈ range f, g x) = (⋃y, g (f y)) :=
supr_range

@[simp] lemma bInter_range {f : ι → α} {g : α → set β} : (⋂x ∈ range f, g x) = (⋂y, g (f y)) :=
infi_range

variables {s : set γ} {f : γ → α} {g : α → set β}

@[simp] lemma bUnion_image : (⋃x∈ (f '' s), g x) = (⋃y ∈ s, g (f y)) :=
supr_image

@[simp] lemma bInter_image : (⋂x∈ (f '' s), g x) = (⋂y ∈ s, g (f y)) :=
infi_image

end image

section image2

variables (f : α → β → γ) {s : set α} {t : set β}

lemma Union_image_left : (⋃ a ∈ s, f a '' t) = image2 f s t :=
by { ext y, split; simp only [mem_Union]; rintros ⟨a, ha, x, hx, ax⟩; exact ⟨a, x, ha, hx, ax⟩ }

lemma Union_image_right : (⋃ b ∈ t, (λ a, f a b) '' s) = image2 f s t :=
by { ext y, split; simp only [mem_Union]; rintros ⟨a, b, c, d, e⟩, exact ⟨c, a, d, b, e⟩,
     exact ⟨b, d, a, c, e⟩ }

end image2

section preimage

theorem monotone_preimage {f : α → β} : monotone (preimage f) := assume a b h, preimage_mono h

@[simp] theorem preimage_Union {ι : Sort w} {f : α → β} {s : ι → set β} :
  preimage f (⋃i, s i) = (⋃i, preimage f (s i)) :=
set.ext $ by simp [preimage]

theorem preimage_bUnion {ι} {f : α → β} {s : set ι} {t : ι → set β} :
  f ⁻¹' (⋃i ∈ s, t i) = (⋃i ∈ s, f ⁻¹' (t i)) :=
by simp

@[simp] theorem preimage_sUnion {f : α → β} {s : set (set β)} :
  f ⁻¹' (⋃₀ s) = (⋃t ∈ s, f ⁻¹' t) :=
set.ext $ by simp [preimage]

lemma preimage_Inter {ι : Sort*} {s : ι → set β} {f : α → β} :
  f ⁻¹' (⋂ i, s i) = (⋂ i, f ⁻¹' s i) :=
by ext; simp

lemma preimage_bInter {s : γ → set β} {t : set γ} {f : α → β} :
  f ⁻¹' (⋂ i∈t, s i) = (⋂ i∈t, f ⁻¹' s i) :=
by ext; simp

@[simp] lemma bUnion_preimage_singleton (f : α → β) (s : set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
by rw [← preimage_bUnion, bUnion_of_singleton]

lemma bUnion_range_preimage_singleton (f : α → β) : (⋃ y ∈ range f, f ⁻¹' {y}) = univ :=
by simp

end preimage

section prod

theorem monotone_prod [preorder α] {f : α → set β} {g : α → set γ}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x).prod (g x)) :=
assume a b h, prod_mono (hf h) (hg h)

alias monotone_prod ← monotone.set_prod

lemma prod_Union {ι} {s : set α} {t : ι → set β} : s.prod (⋃ i, t i) = ⋃ i, s.prod (t i) :=
by { ext, simp }

lemma prod_bUnion {ι} {u : set ι} {s : set α} {t : ι → set β} :
  s.prod (⋃ i ∈ u, t i) = ⋃ i ∈ u, s.prod (t i) :=
by simp_rw [prod_Union]

lemma prod_sUnion {s : set α} {C : set (set β)} : s.prod (⋃₀ C) = ⋃₀ ((λ t, s.prod t) '' C) :=
by { simp only [sUnion_eq_bUnion, prod_bUnion, bUnion_image] }

lemma Union_prod {ι} {s : ι → set α} {t : set β} : (⋃ i, s i).prod t = ⋃ i, (s i).prod t :=
by { ext, simp }

lemma bUnion_prod {ι} {u : set ι} {s : ι → set α} {t : set β} :
  (⋃ i ∈ u, s i).prod t = ⋃ i ∈ u, (s i).prod t :=
by simp_rw [Union_prod]

lemma sUnion_prod {C : set (set α)} {t : set β} :
  (⋃₀ C).prod t = ⋃₀ ((λ s : set α, s.prod t) '' C) :=
by { simp only [sUnion_eq_bUnion, bUnion_prod, bUnion_image] }

lemma Union_prod_of_monotone [semilattice_sup α] {s : α → set β} {t : α → set γ}
  (hs : monotone s) (ht : monotone t) : (⋃ x, (s x).prod (t x)) = (⋃ x, (s x)).prod (⋃ x, (t x)) :=
begin
  ext ⟨z, w⟩, simp only [mem_prod, mem_Union, exists_imp_distrib, and_imp, iff_def], split,
  { intros x hz hw, exact ⟨⟨x, hz⟩, ⟨x, hw⟩⟩ },
  { intros x hz x' hw, exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩ }
end

end prod

section seq

/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : set (α → β)) (t : set α) : set β := {b | ∃f∈s, ∃a∈t, (f : α → β) a = b}

lemma seq_def {s : set (α → β)} {t : set α} : seq s t = ⋃f∈s, f '' t :=
set.ext $ by simp [seq]

@[simp] lemma mem_seq_iff {s : set (α → β)} {t : set α} {b : β} :
  b ∈ seq s t ↔ ∃ (f ∈ s) (a ∈ t), (f : α → β) a = b :=
iff.rfl

lemma seq_subset {s : set (α → β)} {t : set α} {u : set β} :
  seq s t ⊆ u ↔ (∀f∈s, ∀a∈t, (f : α → β) a ∈ u) :=
iff.intro
  (assume h f hf a ha, h ⟨f, hf, a, ha, rfl⟩)
  (assume h b ⟨f, hf, a, ha, eq⟩, eq ▸ h f hf a ha)

lemma seq_mono {s₀ s₁ : set (α → β)} {t₀ t₁ : set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
  seq s₀ t₀ ⊆ seq s₁ t₁ :=
assume b ⟨f, hf, a, ha, eq⟩, ⟨f, hs hf, a, ht ha, eq⟩

lemma singleton_seq {f : α → β} {t : set α} : set.seq {f} t = f '' t :=
set.ext $ by simp

lemma seq_singleton {s : set (α → β)} {a : α} : set.seq s {a} = (λf:α→β, f a) '' s :=
set.ext $ by simp

lemma seq_seq {s : set (β → γ)} {t : set (α → β)} {u : set α} :
  seq s (seq t u) = seq (seq ((∘) '' s) t) u :=
begin
  refine set.ext (assume c, iff.intro _ _),
  { rintros ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩,
    exact ⟨f ∘ g, ⟨(∘) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩ },
  { rintros ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩,
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩ }
end

lemma image_seq {f : β → γ} {s : set (α → β)} {t : set α} :
  f '' seq s t = seq ((∘) f '' s) t :=
by rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]

lemma prod_eq_seq {s : set α} {t : set β} : s.prod t = (prod.mk '' s).seq t :=
begin
  ext ⟨a, b⟩,
  split,
  { rintros ⟨ha, hb⟩, exact ⟨prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩ },
  { rintros ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩, rw ← eq, exact ⟨hx, hy⟩ }
end

lemma prod_image_seq_comm (s : set α) (t : set β) :
  (prod.mk '' s).seq t = seq ((λb a, (a, b)) '' t) s :=
by rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp, prod.swap]

lemma image2_eq_seq (f : α → β → γ) (s : set α) (t : set β) : image2 f s t = seq (f '' s) t :=
by { ext, simp }

end seq

instance : monad set :=
{ pure       := λ(α : Type u) a, {a},
  bind       := λ(α β : Type u) s f, ⋃i∈s, f i,
  seq        := λ(α β : Type u), set.seq,
  map        := λ(α β : Type u), set.image }

section monad
variables {α' β' : Type u} {s : set α'} {f : α' → set β'} {g : set (α' → β')}

@[simp] lemma bind_def : s >>= f = ⋃i∈s, f i := rfl

@[simp] lemma fmap_eq_image (f : α' → β') : f <$> s = f '' s := rfl

@[simp] lemma seq_eq_set_seq {α β : Type*} (s : set (α → β)) (t : set α) : s <*> t = s.seq t := rfl

@[simp] lemma pure_def (a : α) : (pure a : set α) = {a} := rfl

end monad

instance : is_lawful_monad set :=
{ pure_bind             := assume α β x f, by simp,
  bind_assoc            := assume α β γ s f g, set.ext $ assume a,
    by simp [exists_and_distrib_right.symm, -exists_and_distrib_right,
             exists_and_distrib_left.symm, -exists_and_distrib_left, and_assoc];
       exact exists_swap,
  id_map                := assume α, id_map,
  bind_pure_comp_eq_map := assume α β f s, set.ext $ by simp [set.image, eq_comm],
  bind_map_eq_seq       := assume α β s t, by simp [seq_def] }

instance : is_comm_applicative (set : Type u → Type u) :=
⟨ assume α β s t, prod_image_seq_comm s t ⟩

section pi

lemma pi_def {α : Type*} {π : α → Type*} (i : set α) (s : Πa, set (π a)) :
  pi i s = (⋂ a∈i, ((λf:(Πa, π a), f a) ⁻¹' (s a))) :=
by ext; simp [pi]

end pi

end set

/- disjoint sets -/

section disjoint

variables {s t u : set α}

namespace disjoint

/-! We define some lemmas in the `disjoint` namespace to be able to use projection notation. -/

theorem union_left (hs : disjoint s u) (ht : disjoint t u) : disjoint (s ∪ t) u :=
hs.sup_left ht

theorem union_right (ht : disjoint s t) (hu : disjoint s u) : disjoint s (t ∪ u) :=
ht.sup_right hu

lemma preimage {α β} (f : α → β) {s t : set β} (h : disjoint s t) : disjoint (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, h hx

end disjoint

namespace set

protected theorem disjoint_iff : disjoint s t ↔ s ∩ t ⊆ ∅ := iff.rfl

theorem disjoint_iff_inter_eq_empty : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

lemma not_disjoint_iff : ¬disjoint s t ↔ ∃x, x ∈ s ∧ x ∈ t :=
not_forall.trans $ exists_congr $ λ x, not_not

lemma disjoint_left : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
show (∀ x, ¬(x ∈ s ∩ t)) ↔ _, from ⟨λ h a, not_and.1 $ h a, λ h a, not_and.2 $ h a⟩

theorem disjoint_right : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
by rw [disjoint.comm, disjoint_left]

theorem disjoint_of_subset_left (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
d.mono_left h

theorem disjoint_of_subset_right (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
d.mono_right h

theorem disjoint_of_subset {s t u v : set α} (h1 : s ⊆ u) (h2 : t ⊆ v) (d : disjoint u v) :
  disjoint s t :=
d.mono h1 h2

@[simp] theorem disjoint_union_left :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
disjoint_sup_left

@[simp] theorem disjoint_union_right :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
disjoint_sup_right

theorem disjoint_diff {a b : set α} : disjoint a (b \ a) :=
disjoint_iff.2 (inter_diff_self _ _)

@[simp] theorem disjoint_empty (s : set α) : disjoint s ∅ := disjoint_bot_right

@[simp] theorem empty_disjoint (s : set α) : disjoint ∅ s := disjoint_bot_left

@[simp] lemma univ_disjoint {s : set α}: disjoint univ s ↔ s = ∅ :=
top_disjoint

@[simp] lemma disjoint_univ {s : set α} : disjoint s univ ↔ s = ∅ :=
disjoint_top

@[simp] theorem disjoint_singleton_left {a : α} {s : set α} : disjoint {a} s ↔ a ∉ s :=
by simp [set.disjoint_iff, subset_def]; exact iff.rfl

@[simp] theorem disjoint_singleton_right {a : α} {s : set α} : disjoint s {a} ↔ a ∉ s :=
by rw [disjoint.comm]; exact disjoint_singleton_left

theorem disjoint_image_image {f : β → α} {g : γ → α} {s : set β} {t : set γ}
  (h : ∀b∈s, ∀c∈t, f b ≠ g c) : disjoint (f '' s) (g '' t) :=
by rintros a ⟨⟨b, hb, eq⟩, ⟨c, hc, rfl⟩⟩; exact h b hb c hc eq

theorem pairwise_on_disjoint_fiber (f : α → β) (s : set β) :
  pairwise_on s (disjoint on (λ y, f ⁻¹' {y})) :=
λ y₁ _ y₂ _ hy x ⟨hx₁, hx₂⟩, hy (eq.trans (eq.symm hx₁) hx₂)

lemma preimage_eq_empty {f : α → β} {s : set β} (h : disjoint s (range f)) :
  f ⁻¹' s = ∅ :=
by simpa using h.preimage f

lemma preimage_eq_empty_iff {f : α → β} {s : set β} : disjoint s (range f) ↔ f ⁻¹' s = ∅ :=
⟨preimage_eq_empty,
  λ h, by { simp [eq_empty_iff_forall_not_mem, set.disjoint_iff_inter_eq_empty] at h ⊢, finish }⟩

end set

end disjoint

namespace set

/-- A collection of sets is `pairwise_disjoint`, if any two different sets in this collection
are disjoint.  -/
def pairwise_disjoint (s : set (set α)) : Prop :=
pairwise_on s disjoint

lemma pairwise_disjoint.subset {s t : set (set α)} (h : s ⊆ t)
  (ht : pairwise_disjoint t) : pairwise_disjoint s :=
pairwise_on.mono h ht

lemma pairwise_disjoint.range {s : set (set α)} (f : s → set α) (hf : ∀(x : s), f x ⊆ x.1)
  (ht : pairwise_disjoint s) : pairwise_disjoint (range f) :=
begin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy, refine (ht _ x.2 _ y.2 _).mono (hf x) (hf y),
  intro h, apply hxy, apply congr_arg f, exact subtype.eq h
end

/- classical -/
lemma pairwise_disjoint.elim {s : set (set α)} (h : pairwise_disjoint s) {x y : set α}
  (hx : x ∈ s) (hy : y ∈ s) (z : α) (hzx : z ∈ x) (hzy : z ∈ y) : x = y :=
not_not.1 $ λ h', h x hx y hy h' ⟨hzx, hzy⟩

end set

namespace set
variables (t : α → set β)

lemma subset_diff {s t u : set α} : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u :=
⟨λ h, ⟨λ x hxs, (h hxs).1, λ x ⟨hxs, hxu⟩, (h hxs).2 hxu⟩,
λ ⟨h1, h2⟩ x hxs, ⟨h1 hxs, λ hxu, h2 ⟨hxs, hxu⟩⟩⟩

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigma_to_Union (x : Σi, t i) : (⋃i, t i) := ⟨x.2, mem_Union.2 ⟨x.1, x.2.2⟩⟩

lemma sigma_to_Union_surjective : surjective (sigma_to_Union t)
| ⟨b, hb⟩ := have ∃a, b ∈ t a, by simpa using hb, let ⟨a, hb⟩ := this in ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩

lemma sigma_to_Union_injective (h : ∀i j, i ≠ j → disjoint (t i) (t j)) :
  injective (sigma_to_Union t)
| ⟨a₁, ⟨b₁, h₁⟩⟩ ⟨a₂, ⟨b₂, h₂⟩⟩ eq :=
  have b_eq : b₁ = b₂, from congr_arg subtype.val eq,
  have a_eq : a₁ = a₂, from classical.by_contradiction $ assume ne,
    have b₁ ∈ t a₁ ∩ t a₂, from ⟨h₁, b_eq.symm ▸ h₂⟩,
    h _ _ ne this,
  sigma.eq a_eq $ subtype.eq $ by subst b_eq; subst a_eq

lemma sigma_to_Union_bijective (h : ∀i j, i ≠ j → disjoint (t i) (t j)) :
  bijective (sigma_to_Union t) :=
⟨sigma_to_Union_injective t h, sigma_to_Union_surjective t⟩

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def Union_eq_sigma_of_disjoint {t : α → set β}
  (h : ∀i j, i ≠ j → disjoint (t i) (t j)) : (⋃i, t i) ≃ (Σi, t i) :=
(equiv.of_bijective _ $ sigma_to_Union_bijective t h).symm

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bUnion_eq_sigma_of_disjoint {s : set α} {t : α → set β}
  (h : pairwise_on s (disjoint on t)) : (⋃i∈s, t i) ≃ (Σi:s, t i.val) :=
equiv.trans (equiv.set_congr (bUnion_eq_Union _ _)) $ Union_eq_sigma_of_disjoint $
  assume ⟨i, hi⟩ ⟨j, hj⟩ ne, h _ hi _ hj $ assume eq, ne $ subtype.eq eq

end set
