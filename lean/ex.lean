-- Lean theorem prover / programming language
-- https://leanprover.github.io/
--
-- In many functional programming languages types are _first-class_ objects.
--
-- This means that they can be passed as arguments or returned as
-- results from functions, assigned to variables, and stored in data structures.
--
-- Lean is a _dependently-typed_ language, which means that types can depend
-- on _run-time_ values.
--
def foo (b : Bool) : if b then Nat else String :=
  match b with
  | true  => (3 : Nat)
  | false => "three"

#eval foo true
#eval foo false

-- Can also prove things...
theorem zero_add_idempotent : ∀ n, 0 + n = n :=
  by simp

-- And do regular programming stuff in the same language
def sum : List Nat → Nat
  | []    => 0
  | x::xs => x + sum xs

#eval sum [1, 2, 3, 4, 5]
