/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic cnf

universes u v

variables {α : Type u} [decidable_eq α]

namespace list

variables {β : Type v} [add_monoid β] [partial_order β] 
variables [contravariant_class β β (+) (<)]
variables [covariant_class β β (+) (<)]
variables [covariant_class β β (function.swap (+)) (≤)]
variables [covariant_class β β (function.swap (+)) (<)]
variables [covariant_class β β (+) (≤)]
variables [@decidable_rel β (≤)]

lemma sum_map_le_sum_map {l : list α} {f g : α → β} (hfg : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum :=
begin
  induction l with x l ih,
  { refl },
  { simp only [sum_cons, map],
    exact add_le_add (hfg _ (mem_cons_self _ _)) (ih (λ x hx, hfg _ (mem_cons_of_mem _ hx))) }
end

lemma sum_map_lt_sum_map (l : list α) (f g : α → β) (hfg : ∀ x ∈ l, f x ≤ g x) :
  (l.map f).sum < (l.map g).sum ↔ ∃ x ∈ l, f x < g x :=
begin
  refine ⟨_, _⟩,
  { induction l with a as ih,
    { simp only [lt_self_iff_false, forall_false_left, map_nil] },
    { by_cases h : f a < g a,
      { exact λ _, ⟨a, ⟨mem_cons_self _ _, h⟩⟩ },
      { have hfa : f a = g a := decidable.eq_iff_le_not_lt.2 ⟨hfg _ (mem_cons_self _ _), h⟩,
        simp only [list.map_cons, list.sum_cons, hfa, add_lt_add_iff_left],
        intro h',
        obtain ⟨x, ⟨hx, hx'⟩⟩ := ih (λ x hx, hfg _ (mem_cons_of_mem _ hx)) h',
        exact ⟨x, ⟨mem_cons_of_mem _ hx, hx'⟩⟩ } } },
  { rintro ⟨x, ⟨hx, hx'⟩⟩,
    obtain ⟨s, t, rfl⟩ := list.mem_split hx,
    simp only [sum_cons, map, sum_append, map_append],
    refine add_lt_add_of_le_of_lt (sum_map_le_sum_map (λ x hx, hfg _ (mem_append_left _ hx))) _,
    exact add_lt_add_of_lt_of_le hx' (sum_map_le_sum_map (λ x hx, hfg _ (mem_append_right _ (mem_cons_of_mem _ hx)))) }
end

end list

namespace literal

end literal

namespace clause

def unit_propagate (l : literal α) (c : clause α) : clause α :=
c.filter $ (≠) l.inverse

def unit_propagate' (l : literal α) (c : clause α) : option (clause α) :=
if l ∈ c then none else some (unit_propagate l c)

lemma unit_propagate'_of_mem {l : literal α} {c : clause α} (h : l ∈ c) : unit_propagate' l c = none :=
by simp only [unit_propagate', h, if_true]

lemma unit_propagate'_of_not_mem {l : literal α} {c : clause α} (h : l ∉ c) :
  unit_propagate' l c = some (unit_propagate l c) :=
by simp only [unit_propagate', h, if_false]

lemma unit_propagate'_eq_some (l : literal α) (c d : clause α) :
  unit_propagate' l c = some d ↔ l ∉ c ∧ unit_propagate l c = d :=
by by_cases h : l ∈ c; simp [unit_propagate', h]

@[simp]
def satisfied' (ι : interpretation α) : option (clause α) → Prop
| none := tt
| (some c) := satisfied ι c

@[simp]
def length' : option (clause α) → ℕ
| none := 0
| (some c) := c.length

lemma length'_comp_some : (length' : option (clause α) → ℕ) ∘ some = list.length :=
rfl

lemma length_unit_propagate {l : literal α} {c : clause α} (hl : l.inverse ∈ c) :
  (unit_propagate l c).length < c.length :=
(list.length_filter_lt_length_iff_exists _ _).2 ⟨_, hl, λ h, h rfl⟩

lemma length'_unit_propagate'_of_mem {l : literal α} {c : clause α} (hl : l ∈ c) : length' (unit_propagate' l c) < c.length :=
by simpa only [unit_propagate'_of_mem hl, length'] using list.length_pos_of_mem hl

lemma length'_unit_propagate' {l : literal α} {c : clause α} (hl : l.inverse ∈ c) : length' (unit_propagate' l c) < c.length :=
begin
  by_cases h : l ∈ c,
  { exact length'_unit_propagate'_of_mem h },
  { rw [unit_propagate'_of_not_mem h, length'],
    exact length_unit_propagate hl }
end

lemma length_unit_propagate_le (l : literal α) (c : clause α) : (unit_propagate l c).length ≤ c.length :=
list.length_le_of_sublist $ list.filter_sublist c

lemma length'_unit_propagate'_le (l : literal α) (c : clause α) : length' (unit_propagate' l c) ≤ c.length :=
begin
  by_cases h : l ∈ c,
  { rw unit_propagate'_of_mem h,
    exact zero_le _ },
  { rw unit_propagate'_of_not_mem h,
    exact length_unit_propagate_le l c }
end

lemma mem_unit_propagate {l : literal α} {c : clause α} {m : literal α} :
  m ∈ unit_propagate l c ↔ m ∈ c ∧ l.inverse ≠ m :=
by rw [unit_propagate, list.mem_filter]

lemma satisfied_unit_propagate (l : literal α) (c : clause α) (ι : interpretation α)
  (hl : literal.satisfied ι l) : satisfied ι (unit_propagate l c) ↔ satisfied ι c :=
begin
  simp only [satisfied],
  refine ⟨_, _⟩,
  { rintro ⟨m, ⟨hmem, hm⟩⟩,
    rw [mem_unit_propagate] at hmem,
    exact ⟨m, ⟨hmem.1, hm⟩⟩ },
  { rintro ⟨m, ⟨hmem, hm⟩⟩,
    refine ⟨m, ⟨_, hm⟩⟩,
    { rw mem_unit_propagate,
      refine ⟨hmem, _⟩,
      symmetry,
      apply literal.not_satisfied_and_satisfied_inverse _ _ _ hm hl } }
end

lemma satisfied'_unit_propagate' (l : literal α) (c : clause α) (ι : interpretation α)
  (hl : literal.satisfied ι l) : satisfied' ι (unit_propagate' l c) ↔ satisfied ι c :=
begin
  by_cases h : l ∈ c,
  { rw [unit_propagate'_of_mem h, satisfied', satisfied, coe_sort_tt, true_iff],
    exact ⟨_, h, hl⟩ },
  { rw [unit_propagate'_of_not_mem h, satisfied', satisfied_unit_propagate],
    exact hl }
end

end clause

namespace cnf

def unit_propagate (l : literal α) (c : cnf α) : cnf α :=
c.filter_map $ clause.unit_propagate' l

lemma unit_propagate_cons (l : literal α) (γ : clause α) (c : cnf α) :
  unit_propagate l (γ :: c) = if l ∈ γ then unit_propagate l c else (clause.unit_propagate l γ) :: unit_propagate l c :=
begin
  by_cases h : l ∈ γ,
  { simp only [h, unit_propagate, clause.unit_propagate'_of_mem h, list.filter_map_cons_none, if_true] },
  { simp only [h, unit_propagate, list.filter_map_cons_some _ _ _ (clause.unit_propagate'_of_not_mem h),
      eq_self_iff_true, if_false, and_self] }
end

lemma sizeof_unit_propagate (l : literal α) (c : cnf α) :
  sizeof (unit_propagate l c) = (c.map (clause.length' ∘ clause.unit_propagate' l)).sum :=
begin
  induction c with γ c ih,
  { refl },
  { simp only [sizeof_eq_size, size, unit_propagate_cons, list.sum_cons, function.comp_app, list.map],
    by_cases h : l ∈ γ,
    { simp only [h, clause.unit_propagate'_of_mem h, ←ih, sizeof_eq_size, size, if_true, clause.length', zero_add] },
    { simp only [h, clause.unit_propagate'_of_not_mem h, ←ih, sizeof_eq_size, size, list.sum_cons, clause.length',
      if_false, list.map] } }
end

lemma sizeof_cnf (c : cnf α) : sizeof c = (c.map (clause.length' ∘ some)).sum :=
by rw [clause.length'_comp_some, sizeof_eq_size, size]

lemma sizeof_unit_propagate_of_mem {l : literal α} {γ : clause α} {c : cnf α} (hlγ : l ∈ γ ∨ l.inverse ∈ γ) (hγc: γ ∈ c) :
  sizeof (unit_propagate l c) < sizeof c :=
begin
  rw [sizeof_unit_propagate, sizeof_cnf, list.sum_map_lt_sum_map],
  { cases hlγ,
    { exact ⟨γ, hγc, clause.length'_unit_propagate'_of_mem hlγ⟩ },
    { exact ⟨γ, hγc, clause.length'_unit_propagate' hlγ⟩ } },
  { exact λ _ _, clause.length'_unit_propagate'_le _ _ }
end

lemma mem_unit_propagate (l : literal α) (c : cnf α) (γ : clause α) :
  γ ∈ unit_propagate l c ↔ ∃ δ, (δ ∈ c ∧ l ∉ δ) ∧ clause.unit_propagate l δ = γ :=
by simp only [unit_propagate, clause.unit_propagate'_eq_some, and.assoc, list.mem_filter_map]

lemma non_mem_unit_propagate {l : literal α} {c : cnf α} {γ : clause α} (hγ : γ ∈ unit_propagate l c) : l ∉ γ :=
begin
  obtain ⟨δ, ⟨⟨hδc, hlδ⟩, rfl⟩⟩ := (mem_unit_propagate l c γ).1 hγ,
  exact λ hl, hlδ (clause.mem_unit_propagate.1 hl).1
end

lemma inverse_non_mem_unit_propagate {l : literal α} {c : cnf α} {γ : clause α} (hγ : γ ∈ unit_propagate l c) :
  l.inverse ∉ γ :=
begin
  obtain ⟨δ, ⟨⟨hδc, hlδ⟩, rfl⟩⟩ := (mem_unit_propagate l c γ).1 hγ,
  exact λ hl, (clause.mem_unit_propagate.1 hl).2 rfl
end

lemma satisfied_unit_propagate (l : literal α) {c : cnf α} {ι : interpretation α}
  (hl : literal.satisfied ι l) : satisfied ι (unit_propagate l c) ↔ satisfied ι c :=
begin
  simp only [satisfied],
  refine ⟨λ h γ hγ, _, λ h γ hγ, _⟩,
  { by_cases hlγ : l ∈ γ,
    { rw clause.satisfied,
      exact ⟨l, hlγ, hl⟩ },
    { rw ←clause.satisfied_unit_propagate l _ _ hl,
      apply h,
      rw mem_unit_propagate,
      exact ⟨γ, ⟨hγ, hlγ⟩, rfl⟩ } },
  { rw mem_unit_propagate at hγ,
    rcases hγ with ⟨δ, ⟨hδ, -⟩, rfl⟩, 
    rw clause.satisfied_unit_propagate _ _ _ hl,
    exact h _ hδ }
end

lemma satisfiable_of_satisfiable_unit_propagate {l : literal α} {c : cnf α} (h : satisfiable (unit_propagate l c)) :
  satisfiable c :=
begin
  rcases h with ⟨ι, hι⟩,
  by_cases h : literal.satisfied ι l,
  { exact ⟨ι, (satisfied_unit_propagate _ h).1 hι⟩ },
  { refine ⟨ι.flip l, (satisfied_unit_propagate l _).1 ((satisfied_iff _ ι (λ γ hγ m hm, _)).2 hι)⟩,
    { simpa only [interpretation.satisfied_flip_eq] using h },
    { apply interpretation.satisfied_flip_neq;
      rintro rfl,
      exacts [non_mem_unit_propagate hγ hm, inverse_non_mem_unit_propagate hγ hm] } }
end

def any_literal : Π (c : clause α) (hc : c ≠ []), literal α
| [] hc := false.elim (hc rfl)
| (l::lc) hc := l

lemma any_literal_mem : ∀ {c : clause α} (hc : c ≠ []), any_literal c hc ∈ c
| [] hc := false.elim (hc rfl)
| (l::lc) hc := list.mem_cons_self _ _

def dpll : cnf α → bool
| [] := tt
| (x::xs) := if h : [] ∈ x::xs then ff else
    have hx : x ≠ [], from λ hx, h $ or.inl hx.symm,
    have h1 : sizeof (unit_propagate (any_literal x hx) (x::xs)) < sizeof (x::xs),
      from sizeof_unit_propagate_of_mem (or.inl (any_literal_mem hx)) (list.mem_cons_self _ _),
    have h2 : sizeof (unit_propagate (any_literal x hx).inverse (x::xs)) < sizeof (x::xs), by
    { refine sizeof_unit_propagate_of_mem (or.inr _) (list.mem_cons_self _ _),
      simpa only [literal.inverse_inverse] using any_literal_mem hx },
    dpll (unit_propagate (any_literal x hx) (x::xs)) || dpll (unit_propagate (any_literal x hx).inverse (x::xs))

theorem dpll_correct : ∀ (c : cnf α), dpll c ↔ satisfiable c
| [] := by simp only [dpll, satisfiable_empty, coe_sort_tt]
| (x::xs) := if h : [] ∈ x::xs then by simpa [dpll, h] using not_satisfiable_of_empty_mem h else
    have hx : x ≠ [], from λ hx, h $ or.inl hx.symm,
    have h1 : sizeof (unit_propagate (any_literal x hx) (x::xs)) < sizeof (x::xs),
      from sizeof_unit_propagate_of_mem (or.inl (any_literal_mem hx)) (list.mem_cons_self _ _),
    have h2 : sizeof (unit_propagate (any_literal x hx).inverse (x::xs)) < sizeof (x::xs), by
    { refine sizeof_unit_propagate_of_mem (or.inr _) (list.mem_cons_self _ _),
      simpa only [literal.inverse_inverse] using any_literal_mem hx },
    begin
      simp only [dpll, h, dpll_correct, bor_coe_iff, bor, dif_neg, not_false_iff, literal.inverse],
      clear h1 h2,
      refine ⟨_, _⟩,
      { rintro (hr|hr),
        { apply satisfiable_of_satisfiable_unit_propagate hr },
        { apply satisfiable_of_satisfiable_unit_propagate hr } },
      { rintro ⟨ι, hι⟩,
        by_cases hlι : literal.satisfied ι (any_literal x hx),
        { exact or.inl ⟨ι, (satisfied_unit_propagate _ hlι).2 hι⟩ },
        { refine or.inr ⟨ι, (satisfied_unit_propagate _ _).2 hι⟩,
          simpa only [literal.satisfied_inverse] using hlι } }
    end

section
open literal

#eval dpll [[pos 5], [neg 5, pos 6], [neg 6]]

end

end cnf
