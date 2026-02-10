theorem add_zero (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_succ]
    rw [ih]

theorem add_zero2 (n : Nat) : n + 0  = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_zero]
