import Seymour.Matroid.Constructors.VectorMatroid


variable {α : Type}

/-- Matroid `M` is represented by matrix `A` if vector matroid `M[A]` is exactly `M` -/
def Matroid.IsRepresentedBy {R X : Type} [Ring R] (M : Matroid α) (A : Matrix X M.E R) : Prop :=
  M = (⟨X, M.E, A⟩ : VectorMatroid α R).toMatroid

/-- Matroid `M` can be represented over field `F` if it can be represented by some matrix with entries in `F` -/
def Matroid.IsRepresentableOver (M : Matroid α) (R : Type) [Ring R] : Prop :=
  ∃ M' : VectorMatroid α R, M'.toMatroid = M

/-- Matroid `M` is representable if it is representable over some field -/
def Matroid.IsRepresentable (M : Matroid α) : Prop :=
  ∃ R : Type, ∃ _hR : Ring R, M.IsRepresentableOver R

/-- If a matroid is representable over a field, then its dual is also representable over that field -/
lemma Matroid.IsRepresentable_dual_IsRepresentable {R : Type} [Ring R] {M : Matroid α} :
    M.IsRepresentableOver R → M.dual.IsRepresentableOver R := by
  sorry
  -- todo: want to apply `VectorMatroid.dual_exists_standard_repr`, but this requires `[DecidableEq α]`
