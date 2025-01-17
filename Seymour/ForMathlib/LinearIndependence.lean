import Seymour.Matroid.Constructors.VectorMatroid


open scoped Matrix

lemma Matrix.fromCols_zero_linearIndependent {R X Y : Type} [Ring R] (A : Matrix X Y R) (Y₀ : Type) (S : Set X)
    (hA : LinearIndependent R (A.submatrix (Subtype.val : S.Elem → X) id)) :
    LinearIndependent R ((Matrix.fromCols A 0).submatrix (Subtype.val : S.Elem → X) (Sum.inl : Y → Y ⊕ Y₀)) :=
  hA

lemma Matrix.fromRows_zero_linearIndependent {R X Y : Type} [Ring R] (A : Matrix X Y R) (X₀ : Type) (S : Set Y)
    (hA : LinearIndependent R (A.submatrix id (Subtype.val : S.Elem → Y))ᵀ) :
    LinearIndependent R ((Matrix.fromRows A 0).submatrix (Sum.inl : X → X ⊕ X₀) (Subtype.val : S.Elem → Y))ᵀ :=
  hA

set_option maxHeartbeats 0 in -- brace yourself (or rather run overnight)
lemma Matrix.fromRows_zero_indepCols {α R X : Type} [Ring R] {E : Set α} (A : Matrix X E R) (S : Set α) (X₀ : Type)
    (hA : A.IndepCols S) :
    (Matrix.fromRows A (0 : Matrix X₀ E R)).IndepCols S := by
  obtain ⟨hSE, hAS⟩ := hA
  have almost := A.fromRows_zero_linearIndependent X₀ (·.val ∈ S) (by sorry) -- hAS
  simp only [Matrix.IndepCols, hSE, exists_true_left]
  rw [Matrix.transpose_submatrix, Matrix.transpose_fromRows, Matrix.transpose_zero] at almost ⊢
  rw [linearIndependent_iff'ₛ] at almost ⊢
  intro s f g hAsfg i hi
  specialize almost (s.map ⟨(⟨⟨·.val, by aesop⟩, by aesop⟩), (by sorry)⟩)
  specialize almost (f ⟨·.val, by aesop⟩)
  specialize almost (g ⟨·.val, by aesop (simp_config := { maxSteps := 99999999999999999999999 })⟩)
  specialize almost (by sorry) -- hAsfg
  specialize almost (⟨⟨i.val, by aesop⟩, by aesop⟩)
  specialize almost (by aesop)
  exact almost
