import Seymour.ForMathlib.MatrixTU

/-!
This file provides notation used in the project and conversions between set-theoretical and type-theoretical definitions.
-/

/-- The finite field on 2 elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2

/-- The finite field on 3 elements; write `Z3` for "value" type but `Fin 3` for "indexing" type. -/
abbrev Z3 : Type := ZMod 3

/-- Roughly speaking `a ᕃ A` is `A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert

/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr


section utils

variable {α : Type}

lemma nmem_insert {z x : α} {I : Set α} (hx : z ≠ x) (hI : z ∉ I) : z ∉ x ᕃ I := by -- TODO move
  simp_all [Set.insert]

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
def HasSubset.Subset.elem {X Y : Set α} (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion {X Y : Set α} (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
lemma toSum_toUnion {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else if hiY : i.val ∈ Y then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else
    exfalso
    exact i.property.elim hiX hiY

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
`X` and `Y` are disjoint. -/
lemma toUnion_toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem, hXY]

-- TODO do we need API for `Matrix (X₁ ⊕ X₂) (E₁ ∪ E₂).Elem β` instead? Working with the new `VectorMatroid` is hell.

variable {T₁ T₂ S₁ S₂ : Set α} {β : Type}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (C : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((C ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- Convert a matrix over set unions to a block matrix. -/
def Matrix.toMatrixSumSum (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β :=
  ((C ∘ Sum.toUnion) · ∘ Sum.toUnion)

/-- Converting a block matrix to a matrix over set unions and back to a block matrix gives the original matrix, assuming that
both said unions are disjoint. -/
lemma toMatrixUnionUnion_toMatrixSumSum (hT : T₁ ⫗ T₂) (hS : S₁ ⫗ S₂) (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    C.toMatrixUnionUnion.toMatrixSumSum = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toUnion_toSum]

/-- Converting a matrix over set unions to a block matrix and back to a matrix over set unions gives the original matrix. -/
lemma toMatrixSumSum_toMatrixUnionUnion (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    C.toMatrixSumSum.toMatrixUnionUnion = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toSum_toUnion]

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.IsTotallyUnimodular.toMatrixUnionUnion [CommRing β] {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β}
    (hC : C.IsTotallyUnimodular) :
    C.toMatrixUnionUnion.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hC ⊢
  intros
  apply hC

end utils


section TU_tautologies

lemma Matrix.overZ2_isTotallyUnimodular {X Y : Type} (A : Matrix X Y Z2) : A.IsTotallyUnimodular := by
  intro k f g hf hg
  if h0 : (A.submatrix f g).det = 0 then
    use 0
    rewrite [h0]
    rfl
  else
    use 1
    have h1 : (A.submatrix f g).det = 1 := by sorry
    rewrite [h1]
    rfl

lemma Matrix.overZ3_isTotallyUnimodular {X Y : Type} (A : Matrix X Y Z3) : A.IsTotallyUnimodular := by
  intro k f g hf hg
  if h0 : (A.submatrix f g).det = 0 then
    use 0
    rewrite [h0]
    rfl
  else if h1 : (A.submatrix f g).det = 1 then
    use 1
    rewrite [h1]
    rfl
  else
    have h2 : (A.submatrix f g).det = 2 := by sorry
    use -1
    rewrite [h2]
    rfl

example : ¬ (!![2] : Matrix _ _ (ZMod 4)).IsTotallyUnimodular := by
  unfold Matrix.IsTotallyUnimodular
  push_neg
  use 1, id, id, Function.injective_id, Function.injective_id
  decide

end TU_tautologies
