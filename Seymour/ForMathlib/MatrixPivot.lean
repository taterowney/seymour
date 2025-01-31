import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular


/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot) -/
def Matrix.ShortTableauPivot {X Y R : Type} [Field R] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y R) (x : X) (y : Y) (hxy : A x y ≠ 0) : -- note: `hxy` is necessary for correctness
    Matrix X Y R :=
  fun i j ↦
    if j = y then
      if i = x then
        - A x y
      else
        - A i y / A x y
    else
      if i = x then
        A x j / A x y
      else
        A i j - A i y * A x j / A x y

/-- Pivoting preserves total unimodularity -/
lemma Matrix.ShortTableauPivot_isTotallyUnimodular {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    (A.ShortTableauPivot x y hxy).IsTotallyUnimodular :=
  sorry
  -- todo:
  -- 1. adjoin the identity matrix
  -- 2. realize pivot by elementary row operations
  --    * note that the pivot element is ±1, so scaling the pivot row by ±1 is OK
  -- 3. interchange values in the columns corresponding to `x` and `y`
  -- 4. remove the identity matrix
