import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic


variable {X Y F : Type} [DecidableEq X] [DecidableEq Y]

set_option linter.unusedVariables false in
/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot).
This definition makes sense only if `A x y` is nonzero. -/
def Matrix.shortTableauPivot [Field F] (A : Matrix X Y F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of <| fun i j =>
    if j = y then
      if i = x then
        1 / A x y
      else
        - A i y / A x y
    else
      if i = x then
        A x j / A x y
      else
        A i j - A i y * A x j / A x y

open scoped Matrix

-- private def A : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, 3; 4, 5, 6; 7, 8, 9]
-- #eval A.shortTableauPivot 0 0 (by decide)

lemma Matrix.shortTableauPivot_row_pivot [Field F]
    (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y x =
    (fun j : Y => if j = y then 1 / A x y else A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot]

lemma Matrix.shortTableauPivot_row_other [Field F]
    (A : Matrix X Y F) (x : X) (y : Y) (i : X) (hix : i ≠ x) :
    A.shortTableauPivot x y i =
    (fun j : Y => if j = y then - A i y / A x y else A i j - A i y * A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot, hix]

private def Matrix.mulRow [Semiring F]
    (A : Matrix X Y F) (x : X) (c : F) :
    Matrix X Y F :=
  fun i => if i = x then c • A x else A i

private lemma Matrix.IsTotallyUnimodular.mulRow [CommRing F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x : X) {c : F} (hc : c ∈ Set.range SignType.cast) :
    (A.mulRow x c).IsTotallyUnimodular := by
  sorry

/-- Add `c` times the `x`th row to the `r`th row. -/
private def Matrix.addRowMul [Semiring F]
    (A : Matrix X Y F) (x r : X) (c : F) :
    Matrix X Y F :=
  fun i => if i = r then A i + c • A x else A i

private lemma Matrix.IsTotallyUnimodular.addRowMul [CommRing F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x r : X) (c : F) :
    (A.addRowMul x r c).IsTotallyUnimodular := by
  sorry

private def Matrix.addMultiple [Semifield F]
    (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i => if i = x then A x else A i + q i • A x

private lemma Matrix.IsTotallyUnimodular.addMultiple [Field F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x : X) (q : X → F) :
    (A.addMultiple x q).IsTotallyUnimodular := by
  sorry

private def Matrix.getSmallTableau {F : Type}
    (A : Matrix X (X ⊕ Y) F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of (fun i : X => fun j : Y => if j = y then A i (Sum.inl x) else A i (Sum.inr j))

private lemma Matrix.IsTotallyUnimodular.getSmallTableau [CommRing F]
    {A : Matrix X (X ⊕ Y) F} (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.getSmallTableau x y).IsTotallyUnimodular := by
  sorry

private lemma Matrix.shortTableauPivot_eq [Field F]
    (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y =
    (((Matrix.fromCols 1 A).addMultiple x (- A · y / A x y)).getSmallTableau x y).mulRow x (1 / A x y) := by
  ext i j
  if hj : j = y then
    by_cases hi : i = x <;>
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
  else
    if hi : i = x then
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      exact div_eq_inv_mul (A x j) (A x y)
    else
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      ring

/-- Pivoting preserves total unimodularity -/
lemma Matrix.IsTotallyUnimodular.shortTableauPivot [Field F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.shortTableauPivot x y).IsTotallyUnimodular := by
  rw [Matrix.shortTableauPivot_eq]
  have hAxy : 1 / A x y ∈ Set.range SignType.cast
  · rw [inv_eq_self_of_in_set_range_singType_cast] <;> exact hA.apply x y
  exact (((hA.one_fromCols).addMultiple x _).getSmallTableau x y).mulRow x hAxy
