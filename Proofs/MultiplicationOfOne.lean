theorem multiplicationOfOne (n:Nat) : 1 * n = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw[Nat.mul_succ]
    rw[ih]
