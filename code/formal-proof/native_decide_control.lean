-- Control for the axioms check: a theorem proved by native_decide, with no import, and its axioms.
-- Run from the package root: lake env lean code/formal-proof/native_decide_control.lean

theorem ctl_native : 123456 * 654321 = 80779853376 := by native_decide
#print axioms ctl_native
