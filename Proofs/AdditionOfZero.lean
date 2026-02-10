theorem add_zero (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_succ] /-adds 1 to btoh sides-/
    rw [ih] /-then checks with inductive hypothesis-/

theorem add_zero2 (n : Nat) : n + 0  = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_zero]
