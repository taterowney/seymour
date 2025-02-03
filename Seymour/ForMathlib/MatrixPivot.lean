import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic


set_option linter.unusedVariables false in
/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot) -/
def Matrix.shortTableauPivot {X Y F : Type} [Field F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (hxy : A x y ≠ 0) : -- note: `hxy` is necessary for correctness
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

lemma Matrix.shortTableauPivot_row_pivot {X Y F : Type} [Field F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    A.shortTableauPivot x y hxy x =
    (fun j : Y => if j = y then 1 / A x y else A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot]

lemma Matrix.shortTableauPivot_row_other {X Y F : Type} [Field F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (hxy : A x y ≠ 0) (i : X) (hix : i ≠ x) :
    A.shortTableauPivot x y hxy i =
    (fun j : Y => if j = y then - A i y / A x y else A i j - A i y * A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot, hix]

/-- Flip signs on `x`th row xor `y`th column; keep the rest of the matrix the same. -/
def Matrix.polarize {X Y F : Type} [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of <| fun i j =>
    if (i = x) ↔ (j = y) then
      A i j
    else
      - A i j

lemma Matrix.transpose_shortTableauPivot_transpose {X Y F : Type} [Field F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (hxy : A x y ≠ 0) :
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

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]

  -- todo:
  -- 1. adjoin the identity matrix
  -- 2. realize pivot by elementary row operations
  --    * note that the pivot element is ±1, so scaling the pivot row by ±1 is OK
  -- 3. interchange values in the columns corresponding to `x` and `y`
  -- 4. remove the identity matrix

/-- Add `c` times the `x`th row to the `r`th row. -/
private def Matrix.addRowMul {F : Type} [Semiring F]
    (A : Matrix X Y F) (x r : X) (c : F) :
    Matrix X Y F :=
  fun i => if i = r then A i + c • A x else A i

private lemma Matrix.IsTotallyUnimodular.addRowMul {F : Type} [CommRing F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x r : X) (c : F) :
    (A.addRowMul x r c).IsTotallyUnimodular := by
  sorry

private def Matrix.addMultiple {F : Type} [Semifield F]
    (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i => if i = x then A x else A i + q i • A x

private lemma Matrix.IsTotallyUnimodular.addMultiple {F : Type} [Field F]
    {A : Matrix X Y F} (hA : A.IsTotallyUnimodular) (x : X) (q : X → F) :
    (A.addMultiple x q).IsTotallyUnimodular := by
  sorry

private def Matrix.getSmallTableau {F : Type}
    (A : Matrix X (X ⊕ Y) F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of (fun i : X => fun j : Y => if j = y then A i (Sum.inl x) else A i (Sum.inr j))

private lemma Matrix.IsTotallyUnimodular.getSmallTableau {F : Type} [CommRing F]
    {A : Matrix X (X ⊕ Y) F} (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.getSmallTableau x y).IsTotallyUnimodular := by
  sorry

private lemma Matrix.shortTableauPivot_eq {F : Type} [Field F]
    (A : Matrix X Y F) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    A.shortTableauPivot x y hxy = ((Matrix.fromCols 1 A).addMultiple x (A · y / A x y)).getSmallTableau x y := by
  sorry

/-- Pivoting preserves total unimodularity -/
lemma Matrix.shortTableauPivot_isTotallyUnimodular {F : Type} [Field F]
    {A : Matrix X Y F} (x : X) (y : Y) (hxy : A x y ≠ 0) (hA : A.IsTotallyUnimodular) :
    (A.shortTableauPivot x y hxy).IsTotallyUnimodular := by
  rw [Matrix.shortTableauPivot_eq]
  exact ((hA.one_fromCols).addMultiple x _).getSmallTableau x y
