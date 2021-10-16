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

def inverse : literal α → literal α
| (pos x) := neg x
| (neg x) := pos x

def satisfied (ι : interpretation α) : literal α → bool
| (pos x) := ι x
| (neg x) := bnot (ι x)

end literal

namespace clause

def satisfied (ι : interpretation α) (c : clause α) : bool :=
c.any (literal.satisfied ι)

@[simp] 
lemma not_satisfied_empty (ι : interpretation α) : satisfied ι [] = ff :=
rfl

end clause

namespace cnf

def satisfied (ι : interpretation α) (c : cnf α) : bool :=
c.all (clause.satisfied ι)

def satisfiable (c : cnf α) : Prop :=
∃ ι, satisfied ι c

lemma satisfiable_empty : satisfiable ([] : cnf α) :=
⟨λ x, false, dec_trivial⟩

end cnf