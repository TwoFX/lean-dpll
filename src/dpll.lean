import tactic cnf

universe u

variables {α : Type u} [decidable_eq α]

namespace literal

end literal

namespace clause

def unit_propagate (l : literal α) (c : clause α) : clause α :=
c.filter $ (≠) l.inverse

end clause

namespace cnf

def unit_propagate (l : literal α) (c : cnf α) : cnf α :=
(c.filter $ (∉) l).map $ clause.unit_propagate l

def dpll : cnf α → bool
| [] := tt
| ([]::xs) := ff
| ((l::ls)::xs) := bor (unit_propagate l ((l::ls)::xs)).dpll (unit_propagate l ((l::ls)::xs)).dpll

end cnf