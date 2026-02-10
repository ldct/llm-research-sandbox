-- InductiveTypes Exercise 2: List operations and proofs
namespace Hidden

def length : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1

def reverse : List α → List α := go []
where
  go (acc : List α) : List α → List α
    | [] => acc
    | x :: xs => go (x :: acc) xs

-- Prove these properties
theorem length_append (xs ys : List α) : length (xs ++ ys) = length xs + length ys := sorry
theorem length_reverse (xs : List α) : length (reverse xs) = length xs := sorry
theorem reverse_reverse (xs : List α) : reverse (reverse xs) = xs := sorry

end Hidden
