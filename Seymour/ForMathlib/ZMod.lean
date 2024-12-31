import Mathlib.Data.ZMod.Defs


lemma Z2_eq_1_of_ne_0 {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  a.eq_one_of_neq_zero ha
