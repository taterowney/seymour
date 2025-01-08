import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual

import Seymour.Basic


section Definition

/-- Vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (α R : Type) [Ring R] where
  X : Type -- row index set
  E : Set α -- column index set
  A : Matrix X E R -- matrix defining a vector matroid
  -- note: in principle, rows can be indexed by any type, not necessarily `Set α`
  -- however, `Set α` is sufficient to get all vector matroids

variable {α R : Type} [Ring R]

/-- Vector matroid corresponding to matrix `A`. -/
def Matrix.toVectorMatroid {X : Type} {E : Set α} (A : Matrix X E R) : VectorMatroid α R :=
  ⟨X, E, A⟩

/-- todo: desc -/
def Matrix.IndepCols {X : Type} {E : Set α} (A : Matrix X E R) (S : Set α) : Prop :=
  ∃ hS : S ⊆ E, LinearIndependent R (A.submatrix id hS.elem).transpose

/-- A set `S` is independent in `M[A]` iff `S` is a linearly independent subset of columns in `A`. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (S : Set α) : Prop :=
  M.A.IndepCols S

/-- Empty set is independent. -/
theorem VectorMatroid.IndepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ := by
  use Set.empty_subset M.E
  exact linearIndependent_empty_type

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.IndepCols_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) :
    M.IndepCols I := by
  obtain ⟨hJ, hM⟩ := hMJ
  use hIJ.trans hJ
  show LinearIndependent R (fun i j => M.A j (hJ.elem (Subtype.map id hIJ i)))
  apply hM.comp
  intro _ _ hf
  apply Subtype.eq
  simpa [Subtype.map] using hf

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.IndepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  sorry

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.IndepCols_maximal (M : VectorMatroid α R) (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols S := by
  sorry

/-- Vector matroid expressed as `IndepMatroid`. -/
def VectorMatroid.IndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.E
  Indep := M.IndepCols
  indep_empty := M.IndepCols_empty
  indep_subset := M.IndepCols_subset
  indep_aug := M.IndepCols_aug
  indep_maximal S _ := M.IndepCols_maximal S
  subset_ground _ := Exists.choose

end Definition

section API

variable {α R : Type} [Ring R]

/-- Vector matroid converted to `Matroid`. -/
def VectorMatroid.toMatroid (M : VectorMatroid α R) : Matroid α :=
  M.IndepMatroid.matroid

@[simp]
lemma VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = M.E :=
  rfl

@[simp]
lemma VectorMatroid.toMatroid_indep (M : VectorMatroid α R) : M.toMatroid.Indep = M.IndepCols :=
  rfl

end API

section EquivalentTransformations

-- todo: section 2.2/6.3 from Oxley: Different matroid representations
-- the following operations on `A` do not change `M[A]`:
-- 2.2.1 Interchange two rows.
-- 2.2.2 Multiply a row by non-zero.
-- 2.2.3 Replace a row by the sum of that row and anotheRepr.
-- 2.2.4 Adjoin or remove a zero row.
-- 2.2.5 Interchange two columns (the labels moving with the columns).
-- 2.2.6 Multiply a column by a non-zero member of F.
-- 2.2.7 Replace each matrix entry by its image under some automorphism of F.

-- todo: if A is non-zero, it can be reduced to [I | D] by a sequence of operations of types 2.2.1-2.2.5

end EquivalentTransformations

section StandardRepr

/-- Standard matrix representation of a vector matroid matroid. -/
structure StandardRepr (α R : Type) [Ring R] where
  /-- row index set -/
  X : Set α
  /-- column index set -/
  Y : Set α
  /-- ability to check if an element belongs to `X` -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- ability to check if an element belongs to `Y` -/
  decmemY : ∀ a, Decidable (a ∈ Y)
  /-- `X` and `Y` are disjoint -/
  hXY : X ⫗ Y
  /-- standard representation matrix -/
  B : Matrix X Y R

variable {α R : Type} [Ring R]

-- Automatically infer decidability when `StandardRepr` is present.
attribute [instance] StandardRepr.decmemX
attribute [instance] StandardRepr.decmemY


/-- Maps a matrix with columns indexed by a sum of two sets to a matrix with columns indexed by union of these sets. -/
def Matrix.glueCols {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (M : Matrix X (X ⊕ Y) R) :
    Matrix X (X ∪ Y).Elem R :=
  Matrix.of (fun i j => M i j.toSum)
-- TODO generalize and move

/-- Vector matroid constructed from standard representation. -/
def StandardRepr.toVectorMatroid [DecidableEq α] (Repr : StandardRepr α R) : VectorMatroid α R :=
  ⟨Repr.X, Repr.X ∪ Repr.Y, (Matrix.fromCols 1 Repr.B).glueCols⟩

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E [DecidableEq α] (Repr : StandardRepr α R) :
    Repr.toVectorMatroid.toMatroid.E = Repr.X ∪ Repr.Y :=
  rfl

/-- Full representation matrix of vector matroid is `[I | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A [DecidableEq α] (Repr : StandardRepr α R) :
    Repr.toVectorMatroid.A = (Matrix.fromCols 1 Repr.B).glueCols :=
  rfl

/-- Set is independent in vector matroid iff corresponding set of columns of `[I | B]` is linearly independent over `R`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_indep [DecidableEq α] (Repr : StandardRepr α R) :
    Repr.toVectorMatroid.toMatroid.Indep = Repr.toVectorMatroid.IndepCols :=
  rfl

/-- todo: desc -/
lemma VectorMatroid.exists_standard_repr [DecidableEq α] (M : VectorMatroid α R) :
    ∃ Repr : StandardRepr α R, M = Repr.toVectorMatroid :=
  sorry

/-- todo: desc -/
lemma VectorMatroid.standard_repr_base [DecidableEq α] {M : VectorMatroid α R} {Repr: StandardRepr α R}
    (h : M = Repr.toVectorMatroid) :
    M.toMatroid.Base Repr.X :=
  sorry

def StandardRepr.dual [DecidableEq α] (Repr : StandardRepr α R) : StandardRepr α R where
  X := Repr.Y
  Y := Repr.X
  decmemX := Repr.decmemY
  decmemY := Repr.decmemX
  hXY := Repr.hXY.symm
  B := -Repr.B.transpose

/-- todo: desc -/
lemma VectorMatroid.dual_standard_repr [DecidableEq α] {M : VectorMatroid α R} {Repr: StandardRepr α R}
    (h : M = Repr.toVectorMatroid) :
    M.toMatroid.dual = Repr.dual.toVectorMatroid.toMatroid :=
  sorry -- Theorem 2.2.8 in Oxley

/-- todo: desc -/
lemma VectorMatroid.dual_exists_standard_repr [DecidableEq α] (M : VectorMatroid α R) :
    ∃ DualRepr : StandardRepr α R, M.toMatroid.dual = DualRepr.toVectorMatroid.toMatroid := by
  have ⟨Repr, hRepr⟩ := M.exists_standard_repr
  use Repr.dual
  exact VectorMatroid.dual_standard_repr hRepr

end StandardRepr
