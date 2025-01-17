import Seymour.Matroid.Constructors.VectorMatroid


lemma Matrix.fromRows_zero_indepCols {α R X : Type} [Ring R] {E : Set α} (A : Matrix X E R) (S : Set α) (X₀ : Type)
    (hA : A.IndepCols S) :
    (Matrix.fromRows A (0 : Matrix X₀ E R)).IndepCols S := by
  obtain ⟨hSE, hAS⟩ := hA
  simp only [Matrix.IndepCols, hSE, exists_true_left]
  rw [Matrix.transpose_submatrix, linearIndependent_iff'ₛ] at hAS ⊢
  rw [Matrix.transpose_fromRows, Matrix.transpose_zero]
  intro s f g hAsfg
  apply hAS s f g
  ext x
  simp at hAsfg ⊢
  convert congr_fun hAsfg (Sum.inl x) <;> symm <;> apply Finset.sum_apply
