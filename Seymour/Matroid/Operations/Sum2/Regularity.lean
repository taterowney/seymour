import Seymour.ForMathlib.MatrixManip
import Seymour.Matroid.Operations.Sum2.Basic
import Seymour.Matroid.Classes.Regular


variable {α : Type}

section Representations

/-- representation for summands in 2-sum, see Proposition 7.1.24 in Oxley -/
structure TwoSumSummandRepr (M : Matroid α) {p : α} (hp : p ∈ M.E) (R : Type) [Ring R] where
  /-- row index collection -/
  X : Set α
  /-- matrix representation -/
  A : Matrix X M.E R
  /-- the row where the column `p` of `A` contains a one -/
  r : α
  hr : r ∈ X
  /-- column `p` of `A` has a one in row `r` and zeroes everywhere else -/
  hA : A ⟨r, hr⟩ ⟨p, hp⟩ = 1 ∧ ∀ i : X, i ≠ ⟨r, hr⟩ → A i ⟨p, hp⟩ = 0
  /-- additional decidability conditions -/ -- todo: avoid? simplify?
  decmemX : ∀ a, Decidable (a ∈ X)
  deceqr : ∀ a, Decidable (a = r)

-- Automatically infer decidability when `StandardRepr` is present.
attribute [instance] TwoSumSummandRepr.decmemX
attribute [instance] TwoSumSummandRepr.deceqr

/-- todo: desc -/
def TwoSumSummandRepr.col_p {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E} (S : TwoSumSummandRepr M hp R) :
    Matrix S.X ({p} : Set α) R :=
  Matrix.of fun i j => S.A i ⟨j, Set.mem_of_eq_of_mem j.property hp⟩

/-- todo: desc -/
def TwoSumSummandRepr.row_p {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E} (S : TwoSumSummandRepr M hp R) :
    Matrix ({S.r} : Set α) M.E R :=
  Matrix.of fun _i j => S.A ⟨S.r, S.hr⟩ j
  -- alt, with i: Matrix.of fun i j => S.A ⟨i, Set.mem_of_eq_of_mem i.property S.hr⟩ j

/-- todo: desc -/
def TwoSumSummandRepr.row_p_del_1 {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E} (S : TwoSumSummandRepr M hp R) :
    Matrix ({S.r} : Set α) (M.E \ {p}).Elem R :=
  Matrix.of fun _i j => S.A ⟨S.r, S.hr⟩ ⟨j, Set.mem_of_mem_diff j.property⟩
  -- alt, with i: Matrix.of fun i j => S.A ⟨i.val, Set.mem_of_eq_of_mem i.property S.hr⟩ ⟨j, Set.mem_of_mem_diff j.property⟩

/-- todo: desc -/
def TwoSumSummandRepr.A_del_col_p {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E} (S : TwoSumSummandRepr M hp R) :
    Matrix S.X (M.E \ {p}).Elem R :=
  Matrix.of fun i j => S.A i ⟨j, Set.mem_of_mem_diff j.property⟩

/-- todo: desc -/
def TwoSumSummandRepr.A_block {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E} (S : TwoSumSummandRepr M hp R) :
    Matrix (S.X \ {S.r}).Elem (M.E \ {p}).Elem R :=
  Matrix.of fun i j => S.A ⟨i, Set.mem_of_mem_diff i.property⟩ ⟨j, Set.mem_of_mem_diff j.property⟩

/-- todo: desc -/
def TwoSumSummandRepr.A_block_p_zero {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E}
    (S : TwoSumSummandRepr M hp R) (Y : Set α) [∀ a, Decidable (a ∈ Y)] (t : α) [∀ a, Decidable (a ∈ ({t} : Set α))] :
    Matrix (S.X \ {S.r} ∪ {t} ∪ Y).Elem (M.E \ {p}).Elem R :=
  Matrix.fromRowsSetUnion
    (Matrix.fromRowsSetUnion S.A_block (S.row_p_del_1.reindex (Equiv.ofUnique _ _) (Equiv.setCongr rfl))) 0

-- todo: move
lemma set_union_union_eq_rev {α : Type} (X Y Z : Set α) : X ∪ Y ∪ Z = Z ∪ Y ∪ X := by
  rw [Set.union_assoc, Set.union_comm, Set.union_comm Y Z]

/-- todo: desc -/
def TwoSumSummandRepr.A_zero_p_block {R : Type} [Ring R] {M : Matroid α} {p : α} {hp : p ∈ M.E}
    (S : TwoSumSummandRepr M hp R) (Y : Set α) [∀ a, Decidable (a ∈ Y)] (t : α) [∀ a, Decidable (a ∈ ({t} : Set α))] :
    Matrix (Y ∪ {t} ∪ S.X \ {S.r}).Elem (M.E \ {p}).Elem R :=
  Matrix.castRowsSetUnion (S.A_block_p_zero Y t) (set_union_union_eq_rev (S.X \ {S.r}) {t} Y)

/-- todo: desc -/
lemma TwoSumSummandRepr.twoSumGround_eq {M₁ M₂ : Matroid α} {p : α} (hp₁ : p ∈ M₁.E) (hp₂ : p ∈ M₂.E)
    (assumptions : TwoSumAssumptions M₁ M₂) :  M₁.E \ {p} ∪ M₂.E \ {p} = twoSumGround M₁ M₂ := by
  have ⟨p', hp'⟩ := assumptions.inter_singleton
  have hpp' : p ∈ ({p'} : Set α) := hp' ▸ Set.mem_inter hp₁ hp₂
  rw [←Set.union_diff_distrib, twoSumGround, hp', hpp']

/-- todo: desc -/ -- glue representations of M₁ and M₂ as shown in fig. 7.6(a) in Oxley, then delete column of {p}
def TwoSumSummandRepr.compose {R : Type} [Ring R] {M₁ M₂ : Matroid α} {p : α} {hp₁ : p ∈ M₁.E} {hp₂ : p ∈ M₂.E}
    [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)] -- todo: avoid?
    (S₁ : TwoSumSummandRepr M₁ hp₁ R) (S₂ : TwoSumSummandRepr M₂ hp₂ R) (assumptions : TwoSumAssumptions M₁ M₂) :
    Matrix ((S₁.X \ {S₁.r}) ∪ {S₁.r} ∪ (S₂.X \ {S₂.r})).Elem (twoSumGround M₁ M₂) R :=
  Matrix.castColsSetUnion
    (Matrix.fromColsSetUnion (S₁.A_block_p_zero (S₂.X \ {S₂.r}) S₁.r) (S₂.A_zero_p_block (S₁.X \ {S₁.r}) S₁.r))
    (twoSumGround_eq hp₁ hp₂ assumptions)

/-- todo: desc -/
lemma TwoSumSummandRepr.exists {R : Type} [Ring R] {M : Matroid α} {p : α}
    (hp : p ∈ M.E) (hM : M.IsRepresentableOver R) :
    ∃ S : TwoSumSummandRepr M hp R, M.IsRepresentedBy S.A :=
  sorry
  -- todo: use standard matrix representation where rows correspond to a base that includes `p`

/-- todo: desc -/
lemma TwoSumSummandRepr.twoSum_repr {R : Type} [Ring R] {M₁ M₂ : Matroid α} {p : α} {hp₁ : p ∈ M₁.E} {hp₂ : p ∈ M₂.E}
    [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)] -- todo: avoid?
    (assumptions : TwoSumAssumptions M₁ M₂) (S₁ : TwoSumSummandRepr M₁ hp₁ R) (S₂ : TwoSumSummandRepr M₂ hp₂ R) :
    assumptions.build2sum.IsRepresentedBy (S₁.compose S₂ assumptions) :=
  sorry

end Representations


section Regularity

/-- todo: desc -/
lemma Matroid2sum_isRegular_isRegular {M₁ M₂ : Matroid α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    assumptions.build2sum.IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, rfl⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, rfl⟩ := hM₂ F hF
  sorry

/-- todo: desc -/
lemma Matroid2sum_isRegular_left {M₁ M₂ : Matroid α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hM : assumptions.build2sum.IsRegular) :
    M₁.IsRegular :=
  sorry

/-- todo: desc -/
lemma Matroid2sum_isRegular_right {M₁ M₂ : Matroid α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hM : assumptions.build2sum.IsRegular) :
    M₂.IsRegular :=
  sorry

/-- todo: desc -/
lemma Matroid2sum_IsRegular_both {M₁ M₂ : Matroid α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hM : assumptions.build2sum.IsRegular) :
    M₁.IsRegular ∧ M₂.IsRegular :=
  ⟨Matroid2sum_isRegular_left assumptions hM, Matroid2sum_isRegular_right assumptions hM⟩

end Regularity
