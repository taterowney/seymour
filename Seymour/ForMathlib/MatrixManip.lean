import Seymour.Basic


variable {α X Y R : Type} {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Set α}


/-- todo: desc -/
def Matrix.setUnion_castCols (A : Matrix X (Y₁ ∪ Y₂).Elem R) (hY : Y₁ ∪ Y₂ = Y₀) : Matrix X Y₀ R :=
  Matrix.of fun i j => A i ⟨j.val, hY ▸ j.coe_prop⟩

/-- Concatenate matrices B₁[X × Y₁] and B₂[X × Y₂] with the same rows (X)
  to get a matrix indexed by [X × (Y₁ ∪ Y₂).Elem] -/
def Matrix.setUnion_fromCols [∀ a, Decidable (a ∈ Y₁)] [∀ a, Decidable (a ∈ Y₂)] (A₁ : Matrix X Y₁ R) (A₂ : Matrix X Y₂ R) :
    Matrix X (Y₁ ∪ Y₂).Elem R :=
  Matrix.of fun i j => (Matrix.fromCols A₁ A₂) i j.toSum

/-- Given a matrix with columns indexed by a set union, extract the first set of columns -/
def Matrix.setUnion_toCols₁ (A : Matrix X (Y₁ ∪ Y₂).Elem R) : Matrix X Y₁ R :=
  Matrix.of fun i j => A i (Set.subset_union_left.elem j)

/-- Given a matrix with columns indexed by a set union, extract the second set of columns -/
def Matrix.setUnion_toCols₂ (A : Matrix X (Y₁ ∪ Y₂).Elem R) : Matrix X Y₂ R :=
  Matrix.of fun i j => A i (Set.subset_union_right.elem j)


/-- todo: desc -/
def Matrix.setUnion_castRows (A : Matrix (X₁ ∪ X₂).Elem Y R) (hX : X₁ ∪ X₂ = X₀) : Matrix X₀ Y R :=
  Matrix.of fun i j => A ⟨i.val, hX ▸ i.coe_prop⟩ j

/-- Concatenate matrices A₁[X₁ × Y] and A₂[X₂ × Y] with the same columns (Y)
  to get a matrix indexed by [(X₁ ∪ X₂).Elem × Y] -/
def Matrix.setUnion_fromRows [∀ a, Decidable (a ∈ X₁)] [∀ a, Decidable (a ∈ X₂)] (A₁ : Matrix X₁ Y R) (A₂ : Matrix X₂ Y R) :
    Matrix (X₁ ∪ X₂).Elem Y R :=
  Matrix.of fun i j => (Matrix.fromRows A₁ A₂) i.toSum j

/-- Given a row partitioned matrix extract the first row -/
def Matrix.setUnion_toRows₁ (A : Matrix (X₁ ∪ X₂).Elem Y R) : Matrix X₁ Y R :=
  Matrix.of fun i j => A (Set.subset_union_left.elem i) j

/-- Given a row partitioned matrix extract the second row -/
def Matrix.setUnion_toRows₂ (A : Matrix (X₁ ∪ X₂).Elem Y R) : Matrix X₂ Y R :=
  Matrix.of fun i j => A (Set.subset_union_right.elem i) j

-- todo: simp lemmas?


/-- todo: desc -/
def Matrix.setUnion_fromBlocks
    [∀ a, Decidable (a ∈ X₁)] [∀ a, Decidable (a ∈ X₂)] [∀ a, Decidable (a ∈ Y₁)] [∀ a, Decidable (a ∈ Y₂)]
    (A : Matrix X₁ Y₁ R) (B : Matrix X₁ Y₂ R) (C : Matrix X₂ Y₁ R) (D : Matrix X₂ Y₂ R) :
    Matrix (X₁ ∪ X₂).Elem (Y₁ ∪ Y₂).Elem R :=
  Matrix.setUnion_fromRows (Matrix.setUnion_fromCols A B) (Matrix.setUnion_fromCols C D)

/-- todo: desc -/
def Matrix.setUnion_fromBlocks' {T₁ T₂ : Type}
    [∀ a, Decidable (a ∈ Y₁)] [∀ a, Decidable (a ∈ Y₂)]
    (A : Matrix T₁ Y₁ R) (B : Matrix T₁ Y₂ R) (C : Matrix T₂ Y₁ R) (D : Matrix T₂ Y₂ R) :
    Matrix (T₁ ⊕ T₂) (Y₁ ∪ Y₂).Elem R :=
  Matrix.fromRows (Matrix.setUnion_fromCols A B) (Matrix.setUnion_fromCols C D)

-- todo: simp lemmas? toBlocks?
