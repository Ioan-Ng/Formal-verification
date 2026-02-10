theorem multiply_Zero (n: Nat) : n * 0 = 0 := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw[Nat.mul_zero]


theorem multiply_Zero2 (n: Nat) : 0 * n = 0 := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw[Nat.mul_succ]
    rw[ih]

/-w[Nat.mul.succ] uses a lemma to rewrite our expression as something useful,
then we use rw[ih] to swap out our inductive hypoethsis for what our
 useful lemma rewrote our expression as and
then it automatically checks rfl on it-/
