-- InductiveTypes Exercise 1: Define operations on natural numbers
-- and prove their basic properties
namespace Hidden

def mul : Nat → Nat → Nat
  | _, 0 => 0
  | n, Nat.succ m => mul n m + n

def pred : Nat → Nat
  | 0 => 0
  | Nat.succ n => n

def sub : Nat → Nat → Nat
  | n, 0 => n
  | 0, _ => 0
  | Nat.succ n, Nat.succ m => sub n m

def exp : Nat → Nat → Nat
  | _, 0 => 1
  | n, Nat.succ m => mul (exp n m) n

-- Prove some properties
theorem mul_zero (n : Nat) : mul n 0 = 0 := sorry
theorem zero_mul (n : Nat) : mul 0 n = 0 := sorry
theorem mul_succ (n m : Nat) : mul n (Nat.succ m) = mul n m + n := sorry
theorem mul_comm (n m : Nat) : mul n m = mul m n := sorry

end Hidden
