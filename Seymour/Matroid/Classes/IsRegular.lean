import Seymour.Basic
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Classes.IsRepresentable


/-- Matrix `B` has a TU signing if there is a TU matrix whose entries are the same as in `B` up to signs. -/
def Matrix.IsRegular {X Y : Type} (B : Matrix X Y Z2) :=
  ∃ B' : Matrix X Y ℚ, -- signed version of `B`
    B'.IsTotallyUnimodular ∧ -- signed matrix is TU
    ∀ i j, if B i j = 0 then B' i j = 0 else B' i j = 1 ∨ B' i j = -1 -- `|B'| = |B|`

/-- Binary matroid is regular if its representation matrix has a TU signing -/
def BinaryMatroid.IsRegular {α : Type} [DecidableEq α] (M : BinaryMatroid α) : Prop :=
  M.A.IsRegular

-- question: prove that binary matroid is regular iff its standard representation matrix has a TU signing?
-- question: implement regular matroid constructor from binary matroid + regularity prop?

/-- If matroid is represented by a totally unimodular matrix `A` over `ℚ`, then it is represented by `A` over any field `F`. -/
theorem Matroid.RepresentableTU_RepresentableAnyField {α : Type} {X E : Set α} {A : Matrix X E ℚ}
    (M : Matroid α) (hM : M.IsRepresentedBy A) (hA : A.IsTotallyUnimodular) :
    ∀ F : Type, ∃ hF : Field F, M.IsRepresentableOver F := by
  sorry
  -- todo: show that `A` defines the same matroid over `ℚ` and over `F`
  -- key steps:
  -- * all square submatrices of `A` have `ℚ` determinant `0` or `±1`
  -- * every square submatrix of `A` is `ℚ`-nonsingular iff it is `F`-nonsingular

/-- The following statements are parts of Theorem (9.2.9) from Truemper's book. -/
theorem BinaryMatroid.isRegularIff1 {α : Type} [DecidableEq α] (M : BinaryMatroid α) :
    M.IsRegular ↔ ∃ X, ∃ A : Matrix X M.E ℚ, A.IsTotallyUnimodular ∧ M.matroid.IsRepresentedBy A := by
  sorry

theorem BinaryMatroid.isRegularIff2 {α : Type} [DecidableEq α] (M : BinaryMatroid α) :
    M.IsRegular ↔ ∀ F : Type, ∃ hF : Field F, M.matroid.IsRepresentableOver F := by
  sorry

theorem BinaryMatroid.isRegularIff3 {α : Type} [DecidableEq α] (M : BinaryMatroid α) :
    M.IsRegular ↔ M.matroid.IsRepresentableOver Z2 ∧ M.matroid.IsRepresentableOver (ZMod 3) := by
  sorry

theorem BinaryMatroid.isRegularIff4 {α : Type} [DecidableEq α] (M : BinaryMatroid α) :
    M.IsRegular ↔ M.matroid.IsRepresentableOver (ZMod 3) ∧
    (∀ X' : Type, ∀ A : Matrix X' M.E (ZMod 3), M.matroid.IsRepresentedBy A → A.IsTotallyUnimodular) := by
  sorry

-- todo: corollaries:
-- * if M is regular, every binary representation matrix of M is regular
-- * if M is regular, every minor of M is regular
-- * if M is regular, dual of M is regular

-- todo: more corollaries:
-- * if M is graphic, M is regular
-- * if M is cographic, M is regular

lemma BinaryMatroid_toMatroid_isRegular_iff {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
  (hM : M₁.matroid = M₂.matroid) : M₁.IsRegular ↔ M₂.IsRegular := by
  sorry
