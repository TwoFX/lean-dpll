
/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic

universe u

variables {α : Type u}

section
variables (α)

@[derive decidable_eq]
inductive literal : Type u
| pos (x : α) : literal
| neg (x : α) : literal

abbreviation clause : Type u := list (literal α)
abbreviation cnf : Type u := list (clause α)
abbreviation interpretation : Type u := α → bool

end

namespace literal

@[simp]
def inverse : literal α → literal α
| (pos x) := neg x
| (neg x) := pos x

@[simp]
def var : literal α → α
| (pos x) := x
| (neg x) := x

@[simp]
def satisfied (ι : interpretation α) : literal α → Prop
| (pos x) := ι x
| (neg x) := ¬ι x

instance decidable_satisfied (ι : interpretation α) : decidable_pred (satisfied ι) :=
λ l, by cases l; dsimp only [satisfied]; apply_instance

@[simp]
lemma satisfied_inverse (ι : interpretation α) (l : literal α) : satisfied ι l.inverse ↔ ¬satisfied ι l :=
by cases l; simp

@[simp]
lemma inverse_inverse (l : literal α) : l.inverse.inverse = l :=
by cases l; refl

lemma not_satisfied_and_satisfied_inverse (ι : interpretation α) (l m : literal α)
  (hl : satisfied ι l) (hm : satisfied ι m) : l ≠ m.inverse :=
λ h, absurd hl $ by { convert hm, rw [←satisfied_inverse, h, inverse_inverse] }

end literal

namespace interpretation
variable [decidable_eq α]

def flip (ι : interpretation α) : literal α → interpretation α
| (literal.pos x) := function.update ι x ¬ι x
| (literal.neg x) := function.update ι x ¬ι x

@[simp]
lemma satisfied_flip_eq (ι : interpretation α) (l : literal α) :
  literal.satisfied (ι.flip l) l ↔ ¬literal.satisfied ι l :=
by cases l; simp only [flip, function.update_same, literal.satisfied, bool.of_to_bool_iff]

lemma satisfied_flip_neq (ι : interpretation α) (l m : literal α) (h₁ : m ≠ l) (h₂ : m ≠ l.inverse) :
  literal.satisfied (ι.flip l) m ↔ literal.satisfied ι m :=
begin
  cases l; cases m;
  simp only [flip, literal.satisfied, ne.def, not_false_iff, literal.inverse] at ⊢ h₁ h₂;
  rw function.update_noteq h₁ <|> rw function.update_noteq h₂
end

end interpretation

namespace clause

def satisfied (ι : interpretation α) (γ : clause α) : Prop :=
∃ l ∈ γ, literal.satisfied ι l

@[simp]
lemma not_satisfied_nil (ι : interpretation α) : ¬satisfied ι [] :=
λ ⟨_, ⟨hl, _⟩⟩, list.not_mem_nil _ hl

@[simp]
lemma satisfied_cons (ι : interpretation α) (γ : clause α) (l : literal α) :
  satisfied ι (l::γ) ↔ literal.satisfied ι l ∨ satisfied ι γ :=
by simp only [satisfied, list.exists_mem_cons_iff]

lemma satisfied_eq {ι κ : interpretation α} {γ : clause α} (h : ∀ l ∈ γ, literal.satisfied ι l ↔ literal.satisfied κ l) :
  γ.satisfied ι ↔ γ.satisfied κ :=
begin
  induction γ with l γ ih,
  { simp only [not_satisfied_nil] },
  { simp only [satisfied_cons, h _ (list.mem_cons_self _ _), ih (λ m hm, h _ (list.mem_cons_of_mem _ hm))] }
end

end clause

namespace cnf

def satisfied (ι : interpretation α) (c : cnf α) : Prop :=
∀ γ ∈ c, clause.satisfied ι γ

@[simp]
lemma satisfied_nil (ι : interpretation α) : satisfied ι [] :=
λ γ hγ, absurd hγ $ list.not_mem_nil _

@[simp]
lemma satisfied_cons (ι : interpretation α) (c : cnf  α) (γ : clause α) :
  satisfied ι (γ::c) ↔ clause.satisfied ι γ ∧ satisfied ι c :=
by simp only [satisfied, list.forall_mem_cons]

lemma satisfied_iff (ι κ : interpretation α) {c : cnf α} (h : ∀ γ ∈ c, ∀ l ∈ γ, literal.satisfied ι l ↔ literal.satisfied κ l) :
  c.satisfied ι ↔ c.satisfied κ :=
begin
  induction c with γ c ih,
  { simp only [satisfied_nil] },
  { simp only [satisfied_cons, clause.satisfied_eq (λ l hl, h _ (list.mem_cons_self _ _) _ hl),
      ih (λ δ hδ l hl, h _ (list.mem_cons_of_mem _ hδ) _ hl)] }
end

def satisfiable (c : cnf α) : Prop :=
∃ ι, satisfied ι c

@[simp]
lemma satisfiable_empty : satisfiable ([] : cnf α) :=
⟨λ x, false, satisfied_nil _⟩

lemma not_satisfiable_of_empty_mem {c : cnf α} (hc : [] ∈ c) : ¬satisfiable c :=
λ ⟨ι, hι⟩, clause.not_satisfied_nil _ (hι _ hc)

def size (c : cnf α) : ℕ :=
(c.map list.length).sum

instance : has_sizeof (cnf α) :=
{ sizeof := size }

lemma sizeof_eq_size (c : cnf α) : sizeof c = size c :=
rfl

end cnf