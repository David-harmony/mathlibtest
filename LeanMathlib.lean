-- This module serves as the root of the `LeanMathlib` library.
-- Import modules here that should be built as part of the library.
import LeanMathlib.Basic

open Nat (add_assoc add_comm)

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
simp [Nat.add_comm, Nat.add_left_comm]
theorem foo (a : Nat) : a + 1 = Nat.succ a := by rfl
