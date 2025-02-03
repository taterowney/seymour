import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular


set_option linter.unusedVariables false in
/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot) -/
def Matrix.shortTableauPivot {X Y R : Type} [Field R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) (hxy : A x y ≠ 0) : -- note: `hxy` is necessary for correctness
    Matrix X Y R :=
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

lemma Matrix.shortTableauPivot_row_pivot {X Y R : Type} [Field R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    A.shortTableauPivot x y hxy x =
    (fun j : Y => if j = y then 1 / A x y else A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot]

lemma Matrix.shortTableauPivot_row_other {X Y R : Type} [Field R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) (hxy : A x y ≠ 0) (i : X) (hix : i ≠ x) :
    A.shortTableauPivot x y hxy i =
    (fun j : Y => if j = y then - A i y / A x y else A i j - A i y * A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot, hix]

/-- Flip signs on `x`th row xor `y`th column; keep the rest of the matrix the same. -/
def Matrix.polarize {X Y R : Type} [Neg R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) :
    Matrix X Y R :=
  Matrix.of <| fun i j =>
    if (i = x) ↔ (j = y) then
      A i j
    else
      - A i j

lemma Matrix.transpose_shortTableauPivot_transpose {X Y R : Type} [Field R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    (Aᵀ.shortTableauPivot y x hxy)ᵀ =
    (A.shortTableauPivot x y hxy).polarize x y := by
  ext i j
  if hjy : j = y then
    if hix : i = x then
      simp [Matrix.shortTableauPivot, Matrix.polarize, hix, hjy]
    else
      simp [Matrix.shortTableauPivot, Matrix.polarize, hix, hjy]
      rw [neg_div, neg_neg]
  else
    if hix : i = x then
      simp [Matrix.shortTableauPivot, Matrix.polarize, hix, hjy]
      rw [neg_div]
    else
      simp [Matrix.shortTableauPivot, Matrix.polarize, hix, hjy]
      rw [mul_comm]

/-- Pivoting preserves total unimodularity -/
lemma Matrix.shortTableauPivot_isTotallyUnimodular {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    (A.shortTableauPivot x y hxy).IsTotallyUnimodular := by
  rw [←Matrix.fromCols_one_isTotallyUnimodular_iff]
  sorry
  -- todo:
  -- 1. adjoin the identity matrix
  -- 2. realize pivot by elementary row operations
  --    * note that the pivot element is ±1, so scaling the pivot row by ±1 is OK
  -- 3. interchange values in the columns corresponding to `x` and `y`
  -- 4. remove the identity matrix
