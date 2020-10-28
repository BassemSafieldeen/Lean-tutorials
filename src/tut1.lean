---- STRUCTURES IN LEAN

/--
A type is a foo if the specified axioms are satisfied:
-/
class foo (α : Type) :=
(axiom_1 : 4 = 4)
(axiom_2 : 5 = 5)

/--
Some foos are also bar if an additional axiom is satisfied:
-/
class bar (α : Type) extends foo α :=
(axiom_3 : 6 = 6)

/--
Let's prove a theorem.

Theorem: If a type is bar it is also foo.
-/
theorem foo_of_bar (α : Type) : bar α → foo α :=
begin
    intro,
    split,
    {refl},
    {refl}
end

/--
Let's prove another theorem: If a type α is foo then 4 = 4.
-/
theorem four_eq_four_of_foo (α : Type) : foo α → 4 = 4 := 
begin
    intro,
    exact a.axiom_1,
end