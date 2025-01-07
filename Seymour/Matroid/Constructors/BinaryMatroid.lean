import Seymour.Basic
import Seymour.Matroid.Constructors.VectorMatroid


/-- Binary matroid is vector matroid of matrix over `Z2`. -/
abbrev BinaryMatroid (α : Type) := VectorMatroid α Z2

/-- Standard matrix representation of binary matroid. -/
structure BinaryMatroid.StandardRepr (α : Type) [DecidableEq α] where
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
  B : Matrix X Y Z2

-- Automatically infer decidability when `StandardRepresentation` is present.
attribute [instance] BinaryMatroid.StandardRepr.decmemX
attribute [instance] BinaryMatroid.StandardRepr.decmemY

/-- Maps a matrix with columns indexed by a sum of two sets to a matrix with columns indexed by union of these sets. -/
def Matrix.GlueColumns {α : Type} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]
    (M : Matrix X (X ⊕ Y) Z2) : Matrix X (X ∪ Y).Elem Z2 :=
  Matrix.of fun i j => M i j.toSum

/-- Binary matroid constructed using standard representation. -/
def BinaryMatroid.ofStandardRepr {α : Type} [DecidableEq α] (R : BinaryMatroid.StandardRepr α) : BinaryMatroid α :=
  ⟨R.X, R.X ∪ R.Y, (Matrix.fromCols 1 R.B).GlueColumns⟩

-- question: introduce API and prove useful properties for standard representation?


section API

/-- Ground set of a binary matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma BinaryMatroid.StandardRepr.E_eq {α : Type} [DecidableEq α] (R : BinaryMatroid.StandardRepr α) :
  (BinaryMatroid.ofStandardRepr R).matroid.E = R.X ∪ R.Y := rfl

/-- Full representation matrix of binary matroid is `[I | B]`. -/
@[simp]
lemma BinaryMatroid.StandardRepr.A_eq {α : Type} [DecidableEq α] (R : BinaryMatroid.StandardRepr α) :
  (BinaryMatroid.ofStandardRepr R).A = (Matrix.fromCols 1 R.B).GlueColumns := rfl

/-- Set is independent in binary matroid iff corresponding set of columns of `[I | B]` is linearly independent over `Z2`. -/
@[simp]
lemma BinaryMatroid.StandardRepr.indep_eq {α : Type} [DecidableEq α] (R : BinaryMatroid.StandardRepr α) :
  (BinaryMatroid.ofStandardRepr R).matroid.Indep = (BinaryMatroid.ofStandardRepr R).IndepCols := rfl

end API
