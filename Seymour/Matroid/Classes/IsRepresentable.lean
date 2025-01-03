import Seymour.Matroid.Constructors.VectorMatroid


-- question: can we use `CommRing`s instead of `Field`s everywhere when talking about representability?

section BasicDefinitions

/-- Matroid `M` is represented by matrix `A` if vector matroid `M[A]` is exactly `M` -/
def Matroid.IsRepresentedBy {α R X : Type} [CommRing R] (M : Matroid α) (A : Matrix X M.E R) : Prop :=
  M = (⟨X, M.E, A⟩ : VectorMatroid α R).matroid

/-- Matroid `M` can be represented over field `F` if it can be represented by some matrix with entries in `F` -/
def Matroid.IsRepresentableOver {α : Type} (M : Matroid α) (F : Type) [Field F] : Prop :=
  ∃ M' : VectorMatroid α F, M'.matroid = M

/-- Matroid `M` is representable if it is representable over some field -/
def Matroid.IsRepresentable {α : Type} (M : Matroid α) : Prop :=
  ∃ F : Type, ∀ hF : Field F, M.IsRepresentableOver F


section Binary

/-- Matroid `M` is binary if it is representable over Z2 -/
def Matroid.IsBinary {α : Type} (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2

-- todo: connect with binary constructor
-- todo: M.IsBinary iff it can be represented by [I | B] over Z2


section MatrixRepresentations

-- todo:
-- let F: field, M: F-representable, p ∈ M, and {p} is not a separator.
-- a) then M can be represented over F by [ A₁ | 0/0/.../1 ] where last column corresponds to p.
-- b) then M can be represented over F by [ 1/0/.../0 | A₁ ] where first column corresponds to p.
