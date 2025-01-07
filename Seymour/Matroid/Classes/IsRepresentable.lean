import Seymour.Matroid.Constructors.VectorMatroid


-- question: Can we use `CommRing`s instead of `Field`s everywhere when talking about representability?
-- answer: Originally there was a `Field` because we needed to invert a matrix; now we can use `Ring`s!

section BasicDefinitions

/-- Matroid `M` is represented by matrix `A` if vector matroid `M[A]` is exactly `M` -/
def Matroid.IsRepresentedBy {α R X : Type} [Ring R] (M : Matroid α) (A : Matrix X M.E R) : Prop :=
  M = (⟨X, M.E, A⟩ : VectorMatroid α R).matroid

/-- Matroid `M` can be represented over field `F` if it can be represented by some matrix with entries in `F` -/
def Matroid.IsRepresentableOver {α : Type} (M : Matroid α) (F : Type) [Ring F] : Prop :=
  ∃ M' : VectorMatroid α F, M'.matroid = M

/-- Matroid `M` is representable if it is representable over some field -/
def Matroid.IsRepresentable {α : Type} (M : Matroid α) : Prop :=
  ∃ F : Type, ∀ _ : Field F, M.IsRepresentableOver F

end BasicDefinitions


section Binary

/-- Matroid `M` is binary if it is representable over Z2 -/
def Matroid.IsBinary {α : Type} (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2

-- todo: connect with binary constructor
-- todo: M.IsBinary iff it can be represented by [I | B] over Z2

end Binary

section MatrixRepresentations

-- todo:
-- let F: field, M: F-representable, p ∈ M, and {p} is not a separator.
-- a) then M can be represented over F by [ A₁ | 0/0/.../1 ] where last column corresponds to p.
-- b) then M can be represented over F by [ 1/0/.../0 | A₁ ] where first column corresponds to p.

end MatrixRepresentations
