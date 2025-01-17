import Seymour.Matroid.Constructors.VectorMatroid


open scoped Matrix

example {R X X₀ Y : Type} [Ring R] (A : Matrix X Y R) (S : Set Y)
    (hA : LinearIndependent R (A.submatrix id (Subtype.val : S.Elem → Y))ᵀ) :
    LinearIndependent R ((Matrix.fromRows A 0).submatrix (Sum.inl : X → X ⊕ X₀) (Subtype.val : S.Elem → Y))ᵀ := by
  sorry
