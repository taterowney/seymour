import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
--import Mathlib.Data.Finset.Card -- some pidgeonholes
import Seymour.ForMathlib.Basic


def Matrix.testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ k : ℕ, k ≤ min m n → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ Set.range SignType.cast


lemma Matrix.isTotallyUnimodular_of_aux {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ}
    (hA : ∀ k : ℕ, k ≤ m → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ Set.range SignType.cast) :
    A.IsTotallyUnimodular := by
  -- rw [Matrix.isTotallyUnimodular_iff]
  -- intro k f g
  -- if hk : k ≤ m then
  --   exact hA k hk f g
  -- else
  --   convert zero_in_set_range_singType_cast
  --   obtain ⟨a, b, hab, hfab⟩ : ∃ a b : Fin k, a ≠ b ∧ f a = f b
  --   · sorry
  --   apply Matrix.det_zero_of_row_eq hab
  --   ext
  --   simp [Matrix.submatrix_apply, hfab]
  intro k f g hf hg
  have hkm : k ≤ m
  · sorry -- from `hf` by https://github.com/leanprover-community/mathlib4/pull/20056/files
  exact hA k hkm f g

lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular = True → A.IsTotallyUnimodular := by
  intro hA
  if hmn : m ≤ n then
    have hm : min m n = m := Nat.min_eq_left hmn
    apply A.isTotallyUnimodular_of_aux
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    convert hA
    exact hm.symm
  else
    push_neg at hmn
    have hn : min m n = n := Nat.min_eq_right hmn.le
    rw [←Matrix.transpose_isTotallyUnimodular_iff]
    apply A.transpose.isTotallyUnimodular_of_aux
    intro k hk f g
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    rw [←Matrix.det_transpose]
    exact hA k (hk.trans_eq hn.symm) g f

theorem Matrix.testTotallyUnimodular_eq_isTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular = True ↔ A.IsTotallyUnimodular := by
  constructor
  · exact A.isTotallyUnimodular_of_testTotallyUnimodular
  · intro hA
    rw [Matrix.isTotallyUnimodular_iff] at hA
    simp only [Matrix.testTotallyUnimodular, and_imp, decide_eq_true_eq, eq_iff_iff, iff_true]
    intro k _ f g
    exact hA k f g
