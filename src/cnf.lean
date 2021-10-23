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
def satisfied (ι : interpretation α) : literal α → bool
| (pos x) := ι x
| (neg x) := bnot (ι x)

@[simp]
lemma satisfied_inverse (ι : interpretation α) (l : literal α) : satisfied ι l.inverse = bnot (satisfied ι l) :=
by cases l; simp

@[simp]
lemma inverse_inverse (l : literal α) : l.inverse.inverse = l :=
by cases l; refl

@[simp]
lemma bnot_iff_not (b : bool) : !b ↔ ¬b :=
by { unfold_coes, simp only [bnot_eq_true_eq_eq_ff, eq_ff_eq_not_eq_tt] }

lemma not_satisfied_and_satisfied_inverse (ι : interpretation α) (l m : literal α)
  (hl : satisfied ι l) (hm : satisfied ι m) : l ≠ m.inverse :=
λ h, absurd hl $ by { convert hm, simp [h] }

end literal

namespace clause

def satisfied (ι : interpretation α) (c : clause α) : bool :=
c.any (literal.satisfied ι)

lemma satisfied_eq {ι κ : interpretation α} {c : clause α} (h : ∀ l ∈ c, literal.satisfied ι l = literal.satisfied κ l) :
  c.satisfied ι = c.satisfied κ :=
begin
  induction c with l ls ih,
  { refl },
  { rw [satisfied, satisfied, list.any_cons, list.any_cons, h l (list.mem_cons_self _ _), ←satisfied, ←satisfied,
      ih (λ m hm, h _ (list.mem_cons_of_mem _ hm))] }
end

lemma satisfied_iff (ι : interpretation α) (c : clause α) : satisfied ι c ↔ ∃ l ∈ c, literal.satisfied ι l :=
by rw [satisfied, list.any_iff_exists]

@[simp] 
lemma not_satisfied_empty (ι : interpretation α) : satisfied ι [] = ff :=
rfl

lemma not_satisfied_empty' (ι : interpretation α) : ¬satisfied ι [] :=
by simp

end clause

namespace cnf

def satisfied (ι : interpretation α) (c : cnf α) : bool :=
c.all (clause.satisfied ι)

lemma satisfied_eq (ι κ : interpretation α) {c : cnf α} (h : ∀ γ ∈ c, ∀ l ∈ γ, literal.satisfied ι l = literal.satisfied κ l) :
  c.satisfied ι = c.satisfied κ :=
begin
  induction c with γ c ih,
  { refl },
  { rw [satisfied, satisfied, list.all_cons, list.all_cons,
      clause.satisfied_eq (λ l hl, h _ (list.mem_cons_self _ _) _ hl), ←satisfied, ←satisfied,
      ih (λ δ hδ l hl, h _ (list.mem_cons_of_mem _ hδ) _ hl)] }
end

lemma satisfied_iff (ι : interpretation α) (c : cnf α) : satisfied ι c ↔ ∀ γ ∈ c, clause.satisfied ι γ :=
by rw [satisfied, list.all_iff_forall]

def satisfiable (c : cnf α) : Prop :=
∃ ι, satisfied ι c

@[simp]
lemma satisfiable_empty : satisfiable ([] : cnf α) :=
⟨λ x, false, dec_trivial⟩

lemma not_satisfiable_of_empty_mem {c : cnf α} (hc : [] ∈ c) : ¬satisfiable c :=
begin
  rw satisfiable,
  rintro ⟨ι, hι⟩,
  rw satisfied_iff at hι,
  exact clause.not_satisfied_empty' ι (hι _ hc)
end

#print axioms not_satisfiable_of_empty_mem

def size (c : cnf α) : ℕ :=
(c.map list.length).sum

instance : has_sizeof (cnf α) :=
{ sizeof := size }

lemma sizeof_eq_size (c : cnf α) : sizeof c = size c :=
rfl

end cnf