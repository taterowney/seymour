import Mathlib.Data.Matroid.IndepAxioms

import Seymour.Basic
import Seymour.ForMathlib.SetTheory


section BinaryMatroidStandardRepr

/-- Data describing a binary matroid on the ground set `X ∪ Y` where `X` and `Y` are bundled. -/
structure BinaryMatroidStandardRepr (α : Type) [DecidableEq α] where
  /-- Basis elements → row indices of [`1 | B`] -/
  X : Set α
  /-- Non-basis elements → column indices of `B` -/
  Y : Set α
  /-- Necessary decidability -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- Necessary decidability -/
  decmemY : ∀ a, Decidable (a ∈ Y)
  /-- Basis and nonbasis elements are disjoint -/
  hXY : X ⫗ Y
  /-- The standard representation matrix -/
  B : Matrix X Y Z2

-- Automatically infer decidability when `BinaryMatroidStandardRepr` is present.
attribute [instance] BinaryMatroidStandardRepr.decmemX
attribute [instance] BinaryMatroidStandardRepr.decmemY

variable {α : Type} [DecidableEq α] {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]

/-- Given matrix `B`, whether the set of columns `S` in the (standard) representation [`1 | B`] `Z2`-independent. -/
def Matrix.IndepCols (B : Matrix X Y Z2) (S : Set α) : Prop :=
  ∃ hs : S ⊆ X ∪ Y, LinearIndependent Z2 ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ hs.elem)).transpose


/-- The empty set of columns is linearly independent. -/
theorem Matrix.IndepCols_empty {B : Matrix X Y Z2} : B.IndepCols ∅ := by
  use Set.empty_subset (X ∪ Y)
  exact linearIndependent_empty_type

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem Matrix.IndepCols_subset {B : Matrix X Y Z2} (I J : Set α) (hBJ : B.IndepCols J) (hIJ : I ⊆ J) :
    B.IndepCols I := by
  obtain ⟨hJ, hB⟩ := hBJ
  use hIJ.trans hJ
  show LinearIndependent Z2 (fun i x => Matrix.fromCols 1 B x ((hJ.elem (Subtype.map id hIJ i)).toSum))
  apply hB.comp
  intro _ _ hf
  apply Subtype.eq
  simpa [Subtype.map] using hf

/-- A nonmaximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem Matrix.IndepCols_augment {B : Matrix X Y Z2} (I J : Set α)
    (hBI : B.IndepCols I) (hBI' : ¬Maximal B.IndepCols I) (hBJ : Maximal B.IndepCols J) :
    ∃ x ∈ J \ I, B.IndepCols (x ᕃ I) := by
  sorry

/-- Any set of columns has the maximal subset property. -/
theorem Matrix.IndepCols_maximal {B : Matrix X Y Z2} (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty B.IndepCols S := by
  sorry

/-- Binary matroid given by its standard representation matrix expressed as `IndepMatroid`. -/
def Matrix.toIndepMatroid (B : Matrix X Y Z2) : IndepMatroid α where
  E := X ∪ Y
  Indep := B.IndepCols
  indep_empty := B.IndepCols_empty
  indep_subset := B.IndepCols_subset
  indep_aug := B.IndepCols_augment
  indep_maximal S _ := B.IndepCols_maximal S
  subset_ground _ := Exists.fst

end BinaryMatroidStandardRepr


section OneSum

variable {α : Type} [DecidableEq α]

/-- 1-sum composition of binary matroids defined on the level of `Matrix`. -/
abbrev Matrix.OneSumComposition {β : Type} [Zero β] {X₁ Y₁ X₂ Y₂ : Set α} (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 0 A₂

def BinaryMatroidStandardRepr.OneSumComposition.B (M₁ M₂ : BinaryMatroidStandardRepr α) :=
  (Matrix.OneSumComposition M₁.B M₂.B).toMatrixUnionUnion

/-- 1-sum composition of binary matroids defined on the level of `BinaryMatroidStandardRepr`. -/
def BinaryMatroidStandardRepr.OneSumComposition (M₁ M₂ : BinaryMatroidStandardRepr α)
    (hX₁Y₂ : M₁.X ⫗ M₂.Y) (hY₁X₂ : M₁.Y ⫗ M₂.X) :
    BinaryMatroidStandardRepr α where
  X := M₁.X ∪ M₂.X
  Y := M₁.Y ∪ M₂.Y
  decmemX := inferInstance
  decmemY := inferInstance
  hXY := (by
    rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
    exact ⟨⟨M₁.hXY, hY₁X₂.symm⟩, ⟨hX₁Y₂, M₂.hXY⟩⟩)
  B := (Matrix.OneSumComposition M₁.B M₂.B).toMatrixUnionUnion

/-- Binary matroid `M` is a result of 1-summing `M₁` and `M₂` (should be equivalent to disjoint sums). -/
def BinaryMatroidStandardRepr.IsOneSumOf (M M₁ M₂ : BinaryMatroidStandardRepr α) : Prop :=
  ∃ hX : M.X = M₁.X ∪ M₂.X, ∃ hY : M.Y = M₁.Y ∪ M₂.X,
  sorry
    -- M.B = hX ▸ hY ▸ (BinaryMatroidStandardRepr.OneSumComposition.B M₁ M₂) -- todo: fix type error

end OneSum


section TwoSum

-- todo: etc., see old commits

end TwoSum


section ThreeSum

-- todo: etc., see old commits

end ThreeSum
