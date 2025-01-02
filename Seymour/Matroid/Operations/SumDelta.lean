import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.Restrict
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Sum

import Seymour.ForMathlib.SetTheory
import Seymour.Matroid.Notions.DisjointCircuitFamily
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Operations.Sum2


section DefinitionCircuitAxioms

-- todo: replace axiom statements by circuit axioms

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids -/
def BinaryMatroid.DeltaSum.E {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : Set α := (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)

/-- Circuits in `M₁ Δ M₂` are nonempty subsets of the ground set of form `X₁ Δ X₂`
    where `X₁`, `X₂` are disjoint unions of circuits in `M₁`, `M₂`, resp -/
def BinaryMatroid.DeltaSum.CircuitForm.prop {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C X₁ X₂ : Set α) : Prop :=
  C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) ∧ M₁.matroid.UnionDisjointCircuits X₁ ∧ M₂.matroid.UnionDisjointCircuits X₂

/-- A set satisfies circuit form if for some `X₁` and `X₂` it has the form above -/
def BinaryMatroid.DeltaSum.CircuitForm {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  C.Nonempty ∧ C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ ∧ ∃ X₁ X₂, BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂

/-- A set of circuit form is nonempty -/
lemma BinaryMatroid.DeltaSum.CircuitForm.nonempty {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C) : C.Nonempty := hC.1

/-- A set of circuit form is a subset of the ground set -/
lemma BinaryMatroid.DeltaSum.CircuitForm.subset_ground {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C) : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ := hC.2.1

/-- A set of circuit form is the symmetric difference of `X₁` and `X₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.eq_symmDiff {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) : C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) := hC.1

/-- A set of circuit form is related to a union of disjoint circuits of `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.udc_left {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) : M₁.matroid.UnionDisjointCircuits X₁ := hC.2.1

/-- A set of circuit form is related to a union of disjoint circuits of `M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.udc_right {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) : M₂.matroid.UnionDisjointCircuits X₂ := hC.2.2

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively -/
def BinaryMatroid.DeltaSum.CircuitPred {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : CircuitPredicate α :=
  fun C => Minimal (BinaryMatroid.DeltaSum.CircuitForm M₁ M₂) C

/-- In circuit construction of Δ-sum, empty set is not circuit -/
lemma BinaryMatroid.DeltaSum.CircuitPred.not_circuit_empty {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ¬BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ ∅ := by
  unfold BinaryMatroid.DeltaSum.CircuitPred Minimal CircuitForm CircuitForm.prop
  simp only [Set.not_nonempty_empty, Set.empty_subset, true_and, false_and, exists_const,
    exists_and_left, Set.le_eq_subset, Set.subset_empty_iff, implies_true, and_true,
    not_false_eq_true]

/-- In circuit construction of Δ-sum, no circuit is strict subset of another circuit -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_not_ssubset {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).circuit_not_ssubset := by
  intro C C' hC hC'
  sorry

/-- In circuit construction of Δ-sum, circuit predicate satisfies axiom (C3) -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_c3 {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).axiom_c3 := by
  intro X C F z hz
  sorry

/-- In circuit construction of Δ-sum, set of all circuit-independent sets has the maximal subset prop -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_maximal {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).circuit_maximal (BinaryMatroid.DeltaSum.E M₁ M₂) := by
  intro X hXE
  sorry

/-- In circuit construction of Δ-sum, every circuit is subset of ground set -/
lemma BinaryMatroid.DeltaSum.CircuitPred.subset_ground {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ∀ C, CircuitPred M₁ M₂ C → C ⊆ E M₁ M₂ :=
  fun _ hC => hC.1.subset_ground

/-- Construction of Δ-sum via circuits -/
def BinaryMatroid.DeltaSum.CircuitMatroid {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : CircuitMatroid α where
  E := BinaryMatroid.DeltaSum.E M₁ M₂
  CircuitPred := BinaryMatroid.DeltaSum.CircuitPred M₁ M₂
  not_circuit_empty := BinaryMatroid.DeltaSum.CircuitPred.not_circuit_empty M₁ M₂
  circuit_not_ssubset := BinaryMatroid.DeltaSum.CircuitPred.circuit_not_ssubset M₁ M₂
  circuit_c3 :=  BinaryMatroid.DeltaSum.CircuitPred.circuit_c3 M₁ M₂
  circuit_maximal :=  BinaryMatroid.DeltaSum.CircuitPred.circuit_maximal M₁ M₂
  subset_ground := BinaryMatroid.DeltaSum.CircuitPred.subset_ground M₁ M₂


section API

/-- Matroid corresponding to Δ-sum -/
def BinaryMatroid.DeltaSum.matroid {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : Matroid α :=
  (BinaryMatroid.DeltaSum.CircuitMatroid M₁ M₂).matroid

@[simp]
lemma BinaryMatroid.DeltaSum.E_eq {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
  (BinaryMatroid.DeltaSum.matroid M₁ M₂).E = (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) := rfl

@[simp]
lemma BinaryMatroid.DeltaSum.CircuitPred_iff {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
  (BinaryMatroid.DeltaSum.CircuitMatroid M₁ M₂).CircuitPred = BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ := rfl

@[simp]
lemma BinaryMatroid.DeltaSum.circuit_iff {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) {C : Set α} :
    (BinaryMatroid.DeltaSum.matroid M₁ M₂).Circuit C ↔ BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  unfold matroid
  rw [CircuitMatroid.circuit_iff]
  exact ⟨fun ⟨_, hC⟩ => hC, fun hC => ⟨hC.subset_ground, hC⟩⟩


section MatrixCharacterization

/-- Sets that are circuits in `M₁` or `M₂` -/
def BinaryMatroid.JointCircuits {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :=
  {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C}

/-- Matrix whose rows are incidence vectors of all circuits in `M₁` and `M₂` -/
def BinaryMatroid.JointCircuitMatrix {α : Type} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroid α) :
    Matrix {C : Set α // M₁.matroid.Circuit C ∨ M₂.matroid.Circuit C} (M₁.E ∪ M₂.E : Set α) Z2 :=
  Matrix.of fun C e => (if (e : α) ∈ (C : Set α) then 1 else 0)
  -- todo: use `M₁.JointCircuitRows M₂` as first dimension of matrix;
  -- compiler doesn't "see through" definition and complains about form mismatch

/-- If `A` is a matrix over GF(2) whose columns are indexed by the elements of `M₁.E ∪ M₂.E`
    and whose rows consist of the incidence vectors of all the circuits of `M₁` and all the circuits of `M₂`, then
    `M₁ Δ M₂ = (M[A])* \ (M₁.E ∩ M₂.E)` -/
lemma BinaryMatroid.DeltaSum.matrix_iff {α : Type} [DecidableEq α] [∀ a : α, ∀ A : Set α, Decidable (a ∈ A)]
    (M₁ M₂ : BinaryMatroid α) :
    BinaryMatroid.DeltaSum.matroid M₁ M₂ = (M₁.JointCircuitMatrix M₂).VectorMatroid.matroid.dual.restrict (BinaryMatroid.DeltaSum.E M₁ M₂) := by
  sorry -- see Lemma 9.3.1 in Oxley


section PropertiesGroundSet

/-- Ground set of Δ-sum is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.E.disjoint_inter {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    Disjoint (BinaryMatroid.DeltaSum.E M₁ M₂) (M₁.E ∩ M₂.E) :=
  Set.disjoint_sdiff_left

/-- Ground sets minus their intersection are disjoint sets -/
lemma BinaryMatroid.DeltaSum.disjoint_grounds_diff_inter {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    Disjoint (M₁.E \ (M₁.E ∩ M₂.E)) (M₂.E \ (M₁.E ∩ M₂.E)) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff


section CircuitFormExamples

/-- Nonempty union of disjoint circuits of `M₁` satisfies circuit form of `M₁ Δ M₂  -/
lemma BinaryMatroid.DeltaSum.CircuitForm_left {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCnempty : C.Nonempty) (hCE : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂) (hC : M₁.matroid.UnionDisjointCircuits C) :
    BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C := by
  constructor
  · exact hCnempty
  constructor
  · exact hCE
  use C, ∅
  exact ⟨
    (by rw [Set.union_empty, Set.inter_empty, Set.diff_empty]),
    hC,
    Matroid.UnionDisjointCircuits.empty M₂.matroid,
  ⟩

/-- Nonempty union of disjoint circuits of `M₂` satisfies circuit form of `M₁ Δ M₂  -/
lemma BinaryMatroid.DeltaSum.CircuitForm_right {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCnempty : C.Nonempty) (hCE : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂) (hC : M₂.matroid.UnionDisjointCircuits C) :
    BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C := by
  constructor
  · exact hCnempty
  constructor
  · exact hCE
  use ∅, C
  exact ⟨
    (by rw [Set.empty_union, Set.empty_inter, Set.diff_empty]),
    Matroid.UnionDisjointCircuits.empty M₁.matroid,
    hC,
  ⟩


section CircuitForm1

/-- Form 1 of circuits in `M₁ Δ M₂`: circuits of `M₁` that are disjoint with `M₁.E ∩ M₂.E` -/
def BinaryMatroid.DeltaSum.CircuitForm1 {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  M₁.matroid.Circuit C ∧ Disjoint C (M₁.E ∩ M₂.E)

/-- Circuit of form 1 is a circuit in `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.circuit_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : M₁.matroid.Circuit C := hC.1

/-- Circuit of form 1 is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.disjoint_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : Disjoint C (M₁.E ∩ M₂.E) := hC.2

/-- Circuit of form 1 lies in `M₁.E ∪ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.subset_union {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_left hC.circuit_M₁.subset_ground M₂.E

/-- Circuit of form 1 lies in ground set of `M₁ Δ M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.subset_ground {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ :=
  Set.subset_diff.mpr ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of form 1 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.subset_M₁_diff_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : C ⊆ M₁.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.mpr ⟨hC.circuit_M₁.subset_ground, hC.disjoint_inter⟩

/-- Circuit of form 1 is disjoint with `M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.disjoint_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : Disjoint C M₂.E := by
  have hM₁M₂ := BinaryMatroid.DeltaSum.disjoint_grounds_diff_inter M₁ M₂
  have hCM₂ := Set.disjoint_of_subset_left hC.subset_M₁_diff_inter hM₁M₂
  have hCM₂ := Set.disjoint_union_right.mpr ⟨hCM₂, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_right] at hCM₂
  exact hCM₂

/-- Circuit of form 1 satisfies circuit form of `M₁ Δ M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.circuit_form {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C := by
  exact BinaryMatroid.DeltaSum.CircuitForm_left hC.circuit_M₁.nonempty hC.subset_ground
    (Matroid.UnionDisjointCircuits.circuit hC.circuit_M₁)

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.disjoint_circuit_pred {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) (hM₁M₂ : Disjoint M₁.E M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hC'C
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, hC'E, X₁, X₂, hC'X₁X₂, hX₁udc, hX₂udc⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hM₁M₂).inter_eq, Set.diff_empty] at hC'X₁X₂

    have hC'M₁ : C' ⊆ M₁.E := hC'C.trans hC.subset_ground
    have hC'M₂ := Set.disjoint_of_subset_left hC'M₁ hM₁M₂
    have hX₂C' : X₂ ⊆ C' := Set.subset_union_right.trans hC'X₁X₂.symm.subset
    have hX₂empty : X₂ = ∅ := Set.subset_eq_empty (hC'M₂ hX₂C' hX₂udc.subset_ground) rfl
    rw [hX₂empty, Set.union_empty] at hC'X₁X₂

    rw [hC'X₁X₂] at hC'C hC'nempty ⊢

    have hX₁dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₁.matroid X₁) hX₁udc hC'nempty
    exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₁ hX₁dep hC'C

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm1.sum2_circuit_pred {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C) (hM₁M₂ : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hC'C
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, hC'E, X₁, X₂, hC'X₁X₂, hX₁udc, hX₂udc⟩ := hC'

    apply Matroid.UnionDisjointCircuits.dep_or_empty at hX₂udc
    cases hX₂udc with
    | inl hX₂dep =>
        have hX₂eq : X₂ = M₁.E ∩ M₂.E := by
          have hSDsubM₁ := ((symmDiff_def_alt X₁ X₂) ▸ hC'X₁X₂) ▸ (hC'C.trans hC.subset_ground)
          have hX₂M₁ := M₁.E_eq ▸ (symmDiff_subset_ground_right hSDsubM₁ hX₁udc.subset_ground)
          have hX₂sub_inter := Set.subset_inter hX₂M₁ hX₂dep.subset_ground
          have hInterFinite := Set.finite_of_encard_eq_coe hM₁M₂.hInter
          have hEncardInterLeX₂ := le_of_eq_of_le hM₁M₂.hInter (Set.one_le_encard_iff_nonempty.mpr hX₂dep.nonempty)
          exact Set.Finite.eq_of_subset_of_encard_le hInterFinite hX₂sub_inter hEncardInterLeX₂
        have ⟨p, hp⟩ := hM₁M₂.inter_singleton
        have hX₂loop : M₂.matroid.Loop p := ⟨Matroid.TwoSum.Assumptions.inter_singleton_mem_M₂ hp, hp ▸ hX₂eq ▸ hX₂dep⟩
        exfalso
        exact (hM₁M₂.inter_singleton_not_loop_M₂ hp) hX₂loop
    | inr hX₂empty =>
        rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hC'X₁X₂
        rw [hC'X₁X₂] at hC'C hC'nempty ⊢
        have hX₁dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₁.matroid X₁) hX₁udc hC'nempty
        exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₁ hX₁dep hC'C


section CircuitForm2

/-- Form 2 of circuits in `M₁ Δ M₂`: circuits of `M₂` that are disjoint with `M₁.E ∩ M₂.E` -/
def BinaryMatroid.DeltaSum.CircuitForm2 {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  M₂.matroid.Circuit C ∧ Disjoint C (M₁.E ∩ M₂.E)

/-- Circuit of form 2 is a circuit in `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.circuit_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : M₂.matroid.Circuit C := hC.1

/-- Circuit of form 2 is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.disjoint_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : Disjoint C (M₁.E ∩ M₂.E) := hC.2

/-- Circuit of form 2 lies in `M₁.E ∪ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.subset_union {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_right hC.circuit_M₂.subset_ground M₁.E

/-- Circuit of form 2 lies in ground set of `M₁ Δ M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.subset_ground {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ :=
  Set.subset_diff.mpr ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of form 2 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.subset_M₂_diff_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : C ⊆ M₂.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.mpr ⟨hC.circuit_M₂.subset_ground, hC.disjoint_inter⟩

/-- Circuit of form 2 is disjoint with `M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.disjoint_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : Disjoint C M₁.E := by
  have hM₁M₂ := BinaryMatroid.DeltaSum.disjoint_grounds_diff_inter M₁ M₂
  have hCM₂ := Set.disjoint_of_subset_right hC.subset_M₂_diff_inter hM₁M₂
  have hCM₂ := Set.disjoint_union_right.mpr ⟨hCM₂.symm, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_left] at hCM₂
  exact hCM₂

/-- Circuit of form 2 satisfies circuit form of `M₁ Δ M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.circuit_form {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C := by
  exact BinaryMatroid.DeltaSum.CircuitForm_right hC.circuit_M₂.nonempty hC.subset_ground
    (Matroid.UnionDisjointCircuits.circuit hC.circuit_M₂)

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` are disjoint -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.disjoint_circuit_pred {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) (hM₁M₂ : Disjoint M₁.E M₂.E) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hC'C
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, hC'E, X₁, X₂, hC'X₁X₂, hX₁udc, hX₂udc⟩ := hC'
    rw [(Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hM₁M₂).inter_eq, Set.diff_empty] at hC'X₁X₂

    have hC'M₂ : C' ⊆ M₂.E := hC'C.trans hC.subset_ground
    have hC'M₁ := Set.disjoint_of_subset_right hC'M₂ hM₁M₂
    have hX₁C' : X₁ ⊆ C' := Set.subset_union_left.trans hC'X₁X₂.symm.subset
    have hX₁empty : X₁ = ∅ := Set.subset_eq_empty (hC'M₁.symm hX₁C' hX₁udc.subset_ground) rfl
    rw [hX₁empty, Set.empty_union] at hC'X₁X₂

    rw [hC'X₁X₂] at hC'C hC'nempty ⊢

    have hX₂dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid X₂) hX₂udc hC'nempty
    exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₂ hX₂dep hC'C

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm2.sum2_circuit_pred {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C) (hM₁M₂ : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hC'C
    obtain ⟨hC, hCE⟩ := hC
    unfold CircuitForm at hC'
    obtain ⟨hC'nempty, hC'E, X₁, X₂, hC'X₁X₂, hX₁udc, hX₂udc⟩ := hC'

    apply Matroid.UnionDisjointCircuits.dep_or_empty at hX₁udc
    cases hX₁udc with
    | inl hX₁dep =>
        have hX₁eq : X₁ = M₁.E ∩ M₂.E := by
          have hSDsubM₂ := ((symmDiff_def_alt X₁ X₂) ▸ hC'X₁X₂) ▸ (hC'C.trans hC.subset_ground)
          have hX₁M₂ := M₂.E_eq ▸ (symmDiff_subset_ground_left hSDsubM₂ hX₂udc.subset_ground)
          have hX₁sub_inter := Set.subset_inter hX₁dep.subset_ground hX₁M₂
          have hInterFinite := Set.finite_of_encard_eq_coe hM₁M₂.hInter
          have hEncardInterLeX₁ := le_of_eq_of_le hM₁M₂.hInter (Set.one_le_encard_iff_nonempty.mpr hX₁dep.nonempty)
          exact Set.Finite.eq_of_subset_of_encard_le hInterFinite hX₁sub_inter hEncardInterLeX₁
        have ⟨p, hp⟩ := hM₁M₂.inter_singleton
        have hX₁loop : M₁.matroid.Loop p := ⟨Matroid.TwoSum.Assumptions.inter_singleton_mem_M₁ hp, hp ▸ hX₁eq ▸ hX₁dep⟩
        exfalso
        exact (hM₁M₂.inter_singleton_not_loop_M₁ hp) hX₁loop
    | inr hX₁empty =>
        rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hC'X₁X₂
        rw [hC'X₁X₂] at hC'C hC'nempty ⊢
        have hX₂dep := (Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid X₂) hX₂udc hC'nempty
        exact (Matroid.Circuit.circuit_iff_def.mp hC).2 X₂ hX₂dep hC'C


section CircuitForm3

/-- Form 3 of circuits in `M₁ Δ M₂`:
    sets `C₁ Δ C₂` where `C₁` and `C₂` are circuits in `M₁` and M₂`, respectively,
    with `C₁ ∩ (M₁.E ∩ M₂.E)` and `C₂ ∩ (M₁.E ∩ M₂.E)` being the same one-element set.
    Here we use equivalent definition by denoting `p` the single element in `C₁ ∩ C₂` and
    expressing `C₁` and `C₂` via `p`, `C`, and ground sets of `M₁` and `M₂`. -/
def BinaryMatroid.DeltaSum.CircuitForm3 {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) (p : α)
    : Prop :=
  M₁.matroid.Circuit ((C ∩ M₁.E) ∪ {p}) ∧
  M₂.matroid.Circuit ((C ∩ M₂.E) ∪ {p}) ∧
  C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂

/-- Existential version of form 3 of circuits -/
def BinaryMatroid.DeltaSum.CircuitForm3.exists {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  ∃ p ∈ M₁.E ∩ M₂.E, BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p

/-- Circuit of form 3 yields a circuit in `M₁` after intersecting it with `M₁.E` and adding `p` -/
def BinaryMatroid.DeltaSum.CircuitForm3.to_circuit_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : M₁.matroid.Circuit ((C ∩ M₁.E) ∪ {p}) := hC.1

/-- Circuit of form 3 yields a circuit in `M₂` after intersecting it with `M₁.E` and adding `p` -/
def BinaryMatroid.DeltaSum.CircuitForm3.to_circuit_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : M₂.matroid.Circuit ((C ∩ M₂.E) ∪ {p}) := hC.2.1

/-- Circuit of form 3 is subset of ground set of `M₁ Δ M₂` -/
def BinaryMatroid.DeltaSum.CircuitForm3.subset_ground {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ := hC.2.2

/-- Singleton element in definition of circuit form 3 lies in `M₁.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.singleton_subset_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : {p} ⊆ M₁.E :=
  (Set.union_subset_iff.mp hC.to_circuit_M₁.subset_ground).2

/-- Singleton element in definition of circuit form 3 lies in `M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.singleton_subset_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : {p} ⊆ M₂.E :=
  (Set.union_subset_iff.mp hC.to_circuit_M₂.subset_ground).2

/-- Singleton element in definition of circuit form 3 lies in `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.singleton_subset_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : {p} ⊆ M₁.E ∩ M₂.E :=
  Set.subset_inter hC.singleton_subset_M₁ hC.singleton_subset_M₂

/-- Circuit of form 3 lies in `M₁.E ∪ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.subset_union {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : C ⊆ M₁.E ∪ M₂.E :=
  sub_union_diff_sub_union hC.subset_ground

/-- Circuit of form 3 is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint C (M₁.E ∩ M₂.E) :=
  Set.disjoint_of_subset_left hC.subset_ground (BinaryMatroid.DeltaSum.E.disjoint_inter M₁ M₂)

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₁_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₁.E) (M₁.E ∩ M₂.E) :=
  hC.disjoint_inter.inter_left M₁.E

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with `M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₁_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₁.E) M₂.E := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_assoc, ←Set.disjoint_iff_inter_eq_empty]
  exact hC.disjoint_inter

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with its intersection with `M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₁_inter_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₁.E) (C ∩ M₂.E) :=
  Set.disjoint_of_subset_right Set.inter_subset_right hC.disjoint_inter_M₁_M₂

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₂_inter {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₂.E) (M₁.E ∩ M₂.E) :=
  hC.disjoint_inter.inter_left M₂.E

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with `M₁.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₂_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₂.E) M₁.E := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_assoc, ←Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
  exact hC.disjoint_inter

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with its intersection with `M₁.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₂_inter_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    {C : Set α} {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₂.E) (C ∩ M₁.E) :=
  hC.disjoint_inter_M₁_inter_M₂.symm

/-- Circuit of form 3 has nonempty intersection with `M₁.E` provided {p} is not a circuit in `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.inter_M₁_nonempty {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hp : ¬M₁.matroid.Circuit {p}) : (C ∩ M₁.E).Nonempty := by
  by_contra hCM₁empty
  push_neg at hCM₁empty
  have hCM₁ := hC.to_circuit_M₁
  rw [hCM₁empty, Set.empty_union] at hCM₁
  exact hp hCM₁

/-- Circuit of form 3 has nonempty intersection with `M₂.E` provided {p} is not a circuit in `M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.inter_M₂_nonempty {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hp : ¬M₂.matroid.Circuit {p}) : (C ∩ M₂.E).Nonempty := by
  by_contra hCM₂empty
  push_neg at hCM₂empty
  have hCM₂ := hC.to_circuit_M₂
  rw [hCM₂empty, Set.empty_union] at hCM₂
  exact hp hCM₂

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with `{p}` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₁_p {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₁.E) {p} :=
  Set.disjoint_of_subset_right hC.singleton_subset_inter hC.disjoint_inter_M₁_inter

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with `{p}` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.disjoint_inter_M₂_p {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : Disjoint (C ∩ M₂.E) {p} :=
  Set.disjoint_of_subset_right hC.singleton_subset_inter hC.disjoint_inter_M₂_inter

/-- Circuit of form 3 is equal to symmetric difference of circuits in its definition -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.eq_symmDiff {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α} {p : α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) : C = symmDiff ((C ∩ M₁.E) ∪ {p}) ((C ∩ M₂.E) ∪ {p}) := by
  rw [symmDiff_def,
      Set.union_diff_distrib, ←Set.diff_diff,
      hC.disjoint_inter_M₁_inter_M₂.sdiff_eq_left,
      hC.disjoint_inter_M₁_p.sdiff_eq_left,
      Set.diff_eq_empty.mpr Set.subset_union_right, Set.union_empty,
      Set.union_diff_distrib, ←Set.diff_diff,
      hC.disjoint_inter_M₂_inter_M₁.sdiff_eq_left,
      hC.disjoint_inter_M₂_p.sdiff_eq_left,
      Set.diff_eq_empty.mpr Set.subset_union_right, Set.union_empty]
  exact (sub_parts_eq hC.subset_union).symm

/-- Circuit of form 3 satisfies circuit form of `M₁ Δ M₂` provided it is nonempty -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.circuit_form {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hCnempty : C.Nonempty) :
    BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C := by
  constructor
  · exact hCnempty
  constructor
  · exact hC.subset_ground
  use C ∩ M₁.E ∪ {p}, C ∩ M₂.E ∪ {p}
  exact ⟨
    symmDiff_def_alt _ _ ▸ hC.eq_symmDiff,
    Matroid.UnionDisjointCircuits.circuit hC.to_circuit_M₁,
    Matroid.UnionDisjointCircuits.circuit hC.to_circuit_M₂,
  ⟩

/-- Under 2-sum assumptions, `{p}` in definition of circuits of form 3 is exactly `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.sum2_singleton_eq {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hM₁M₂ : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid) :
    M₁.E ∩ M₂.E = {p} := by
  have hInterCard := VectorMatroid.E_eq M₁ ▸ VectorMatroid.E_eq M₂ ▸ hM₁M₂.hInter
  have hInterFinite := Set.finite_of_encard_eq_coe hInterCard
  have hInterCardLeSingleton := ((Set.encard_singleton p).symm ▸ hInterCard).le
  exact (Set.Finite.eq_of_subset_of_encard_le hInterFinite hC.singleton_subset_inter hInterCardLeSingleton).symm

/-- Circuit of form 3 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma BinaryMatroid.DeltaSum.CircuitForm3.sum2_circuit_pred {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    {p : α} (hC : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p) (hM₁M₂ : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid) :
    BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  have hp := hC.sum2_singleton_eq hM₁M₂
  have hCnempty := (hM₁M₂.inter_singleton_not_loop_M₁ hp)
  rw [Matroid.Loop.iff_circuit M₁.matroid] at hCnempty
  apply hC.inter_M₁_nonempty at hCnempty
  apply Set.Nonempty.left at hCnempty

  constructor
  · exact hC.circuit_form hCnempty
  · intro D hD hDC
    have ⟨hDnempty, hDE, X₁, X₂, ⟨hDX₁X₂, hX₁udc, hX₂udc⟩⟩ := hD
    have ⟨hCM₁p, hCM₂p, hCE⟩ := hC

    have hX₁X₂ := Set.inter_subset_inter hX₁udc.subset_ground hX₂udc.subset_ground
    rw [M₁.E_eq, M₂.E_eq, hp] at hX₁X₂

    have hX₁C₁ : X₁ ⊆ C ∩ M₁.E ∪ {p} := by
      rw [(Set.diff_union_inter X₁ X₂).symm]
      rw [←symmDiff_def_alt, symmDiff_def] at hDX₁X₂
      simp only [Set.sup_eq_union] at hDX₁X₂
      have hX₁mX₂C := (hDX₁X₂ ▸ Set.subset_union_left).trans hDC
      have hX₁mX₂M₁ := Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₁udc.subset_ground X₂)
      have hX₁mX₂CiM₁ := Set.subset_inter hX₁mX₂C hX₁mX₂M₁
      exact Set.union_subset_union hX₁mX₂CiM₁ hX₁X₂

    have hX₂C₂ : X₂ ⊆ C ∩ M₂.E ∪ {p} := by
      rw [(Set.diff_union_inter X₂ X₁).symm]
      rw [←symmDiff_def_alt, symmDiff_def] at hDX₁X₂
      simp only [Set.sup_eq_union] at hDX₁X₂
      have hX₂mX₁C := (hDX₁X₂ ▸ Set.subset_union_right).trans hDC
      have hX₂mX₁M₂ := Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₂udc.subset_ground X₁)
      have hX₁mX₂CiM₁ := Set.subset_inter hX₂mX₁C hX₂mX₁M₂
      exact Set.union_subset_union hX₁mX₂CiM₁ (Set.inter_comm X₁ X₂ ▸ hX₁X₂)

    cases Matroid.UnionDisjointCircuits.dep_or_empty M₁.matroid X₁ hX₁udc with
    | inl hX₁dep =>
        have hX₁C₁ := (Matroid.Circuit.circuit_iff_def.mp hCM₁p).2 X₁ hX₁dep hX₁C₁
        cases Matroid.UnionDisjointCircuits.dep_or_empty M₂.matroid X₂ hX₂udc with
        | inl hX₂dep =>
            have hX₂C₂ := (Matroid.Circuit.circuit_iff_def.mp hCM₂p).2 X₂ hX₂dep hX₂C₂
            have hX₁X₂p : X₁ ∩ X₂ = {p} := by
              apply Set.Subset.antisymm hX₁X₂
              exact Set.subset_inter (Set.union_subset_iff.mp hX₁C₁).2 (Set.union_subset_iff.mp hX₂C₂).2
            have hCD := Set.union_subset_union hX₁C₁ hX₂C₂
            have hCD : (C ∩ M₁.E ∪ {p} ∪ (C ∩ M₂.E ∪ {p})) \ {p} ⊆ (X₁ ∪ X₂) \ {p} := Set.diff_subset_diff_left hCD
            rw [Set.union_diff_distrib, Set.union_diff_right, Set.union_diff_right,
                Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₁_inter),
                Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₂_inter),
                sub_parts_eq hC.subset_union, ←hX₁X₂p, ←hDX₁X₂] at hCD
            exact hCD
        | inr hX₂empty =>
            rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hDX₁X₂
            rw [hDX₁X₂] at hDnempty
            have hpX₁ := hDX₁X₂ ▸ (Set.union_subset_iff.mp hX₁C₁).2
            have hDp := hp ▸ Set.disjoint_of_subset_left hDE (BinaryMatroid.DeltaSum.E.disjoint_inter M₁ M₂)
            exact False.elim (hDp hpX₁ Set.Subset.rfl rfl)
    | inr hX₁empty =>
        rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hDX₁X₂
        have hX₂dep := Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid X₂ hX₂udc (hDX₁X₂ ▸ hDnempty)
        have hX₂C₂ := (Matroid.Circuit.circuit_iff_def.mp hCM₂p).2 X₂ hX₂dep hX₂C₂
        have hpX₂ := hDX₁X₂ ▸ (Set.union_subset_iff.mp hX₂C₂).2
        have hDp := hp ▸ Set.disjoint_of_subset_left hDE (BinaryMatroid.DeltaSum.E.disjoint_inter M₁ M₂)
        exact False.elim (hDp hpX₂ Set.Subset.rfl rfl)


section CircuitPredCircuit

/-- If `C` satisfies circuit predicate and is a union of disjoint circuits of `M₁`, then `C` is a circuit of `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCpred : BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C) (hCudc : M₁.matroid.UnionDisjointCircuits C) :
    M₁.matroid.Circuit C := by
  have ⟨⟨hCnempty, hCE, _⟩, hCmin⟩ := hCpred
  constructor
  · exact Matroid.UnionDisjointCircuits.nonempty_dep M₁.matroid C hCudc hCnempty
  · intro D hD hDC
    have ⟨D', hD', hD'D⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hD
    have hD'form : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ D' := ⟨
      hD', (Set.subset_diff.mp ((hD'D.trans hDC).trans hCE)).2
    ⟩
    specialize hCmin hD'form.circuit_form (hD'D.trans hDC)
    exact hCmin.trans hD'D

/-- If `C` satisfies circuit predicate and is a union of disjoint circuits of `M₂`, then `C` is a circuit of `M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCpred : BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C) (hCudc : M₂.matroid.UnionDisjointCircuits C) :
    M₂.matroid.Circuit C := by
  have ⟨⟨hCnempty, hCE, _⟩, hCmin⟩ := hCpred
  constructor
  · exact Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid C hCudc hCnempty
  · intro D hD hDC
    have ⟨D', hD', hD'D⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hD
    have hD'form : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ D' := ⟨
      hD', (Set.subset_diff.mp ((hD'D.trans hDC).trans hCE)).2
    ⟩
    specialize hCmin hD'form.circuit_form (hD'D.trans hDC)
    exact hCmin.trans hD'D


section SpecialCase1Sum

/-- Dependent set in disjoint sum is depenent in one of summand matroids -/
lemma Matroid.disjointSum_dep_iff {α : Type} {M N : Matroid α} {h D} :
    (M.disjointSum N h).Dep D ↔ (M.Dep (D ∩ M.E) ∨ N.Dep (D ∩ N.E)) ∧ D ⊆ M.E ∪ N.E := by
  constructor
  · intro hD
    constructor
    · have hDE := Matroid.disjointSum_ground_eq ▸ hD.subset_ground
      apply Matroid.Dep.not_indep at hD
      rw [Matroid.disjointSum_indep_iff] at hD
      push_neg at hD
      if hDM : M.Indep (D ∩ M.E) then
        if hDN : N.Indep (D ∩ N.E) then
          exact False.elim (hD hDM hDN hDE)
        else
          exact Or.inr ⟨hDN, Set.inter_subset_right⟩
      else
        exact Or.inl ⟨hDM, Set.inter_subset_right⟩
    · exact Matroid.disjointSum_ground_eq ▸ hD.subset_ground
  · intro ⟨hD, hDE⟩
    cases hD with
    | inl hDM => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDM) (Matroid.disjointSum_indep_iff.mp hD).1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩
    | inr hDN => exact ⟨
        fun hD => False.elim ((Matroid.Dep.not_indep hDN) (Matroid.disjointSum_indep_iff.mp hD).2.1),
        Matroid.disjointSum_ground_eq ▸ hDE
      ⟩

/-- Circuit in disjoint sum is circuit in one of summand matroids -/
lemma Matroid.disjointSum_circuit_iff {α : Type} (M N : Matroid α) (h : Disjoint M.E N.E) {C : Set α} :
    (M.disjointSum N h).Circuit C ↔ M.Circuit C ∨ N.Circuit C := by
  constructor
  · intro ⟨hCdep, hCmin⟩
    have ⟨hC, hCE⟩ := Matroid.disjointSum_dep_iff.mp hCdep
    cases hC with
    | inl hCM =>
        have hCMMeq : C ∩ M.E ∩ M.E = C ∩ M.E := Set.inter_eq_left.mpr Set.inter_subset_right
        have hCinterM : (M.disjointSum N h).Dep (C ∩ M.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inl (hCMMeq.symm ▸ hCM),
          inter_subset_parent_left hCE
        ⟩
        have hCMeq : C = C ∩ M.E := Set.Subset.antisymm (hCmin hCinterM Set.inter_subset_left) Set.inter_subset_left

        left
        constructor
        · exact hCMeq ▸ hCM
        · intro D hD hDC
          have hDM : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDM : D = D ∩ M.E := Set.Subset.antisymm hDM Set.inter_subset_left
          have hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inl (hDM ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
    | inr hCN =>
        have hCNNeq : C ∩ N.E ∩ N.E = C ∩ N.E := Set.inter_eq_left.mpr Set.inter_subset_right
        have hCinterN : (M.disjointSum N h).Dep (C ∩ N.E) := Matroid.disjointSum_dep_iff.mpr ⟨
          Or.inr (hCNNeq.symm ▸ hCN),
          inter_subset_parent_left hCE
        ⟩
        have hCMeq : C = C ∩ N.E := Set.Subset.antisymm (hCmin hCinterN Set.inter_subset_left) Set.inter_subset_left

        right
        constructor
        · exact hCMeq ▸ hCN
        · intro D hD hDC
          have hDN : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDN : D = D ∩ N.E := Set.Subset.antisymm hDN Set.inter_subset_left
          have hDdep : (M.disjointSum N h).Dep D := Matroid.disjointSum_dep_iff.mpr ⟨
            Or.inr (hDN ▸ hD),
            hDC.trans hCE
          ⟩
          exact hCmin hDdep hDC
  · intro hC
    cases hC with
    | inl hCM =>
        have hCMeq : C = C ∩ M.E := Set.left_eq_inter.mpr hCM.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inl (hCMeq ▸ hCM.dep), (hCM.subset_ground).trans Set.subset_union_left⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          have ⟨hD, hDE⟩ := hD
          have hDMeq : D ⊆ D ∩ M.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCMeq.symm))
          have hDMeq : D = D ∩ M.E := Set.Subset.antisymm hDMeq Set.inter_subset_left
          have hDNeq : D ∩ N.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDMeq.symm) h)
          rw [←hDMeq, hDNeq] at hD
          cases hD with
          | inl hD => exact hCM.2 hD hDC
          | inr hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
    | inr hCN =>
        have hCNeq : C = C ∩ N.E := Set.left_eq_inter.mpr hCN.subset_ground
        constructor
        · rw [Matroid.disjointSum_dep_iff]
          exact ⟨Or.inr (hCNeq ▸ hCN.dep), (hCN.subset_ground).trans Set.subset_union_right⟩
        · intro D hD hDC
          rw [Matroid.disjointSum_dep_iff] at hD
          have ⟨hD, hDE⟩ := hD
          have hDNeq : D ⊆ D ∩ N.E := Set.subset_inter Set.Subset.rfl (hDC.trans (Set.inter_eq_left.mp hCNeq.symm))
          have hDNeq : D = D ∩ N.E := Set.Subset.antisymm hDNeq Set.inter_subset_left
          have hDMeq : D ∩ M.E = ∅ := Disjoint.inter_eq (Set.disjoint_of_subset_left (Set.inter_eq_left.mp hDNeq.symm) h.symm)
          rw [←hDNeq, hDMeq] at hD
          cases hD with
          | inl hD => exact False.elim (Set.Nonempty.ne_empty (Matroid.Dep.nonempty hD) rfl)
          | inr hD => exact hCN.2 hD hDC

/-- If two sets are disjoint, then any set is disjoint with their intersection -/
lemma disjoint_inter_disjoint {α : Type} {A B : Set α} (C : Set α) (h : Disjoint A B) : Disjoint C (A ∩ B) := by
  rw [h.inter_eq]
  exact Set.disjoint_empty C

/-- If `M₁.E ∩ M₂.E = ∅`, then `M₁ Δ M₂ = M₁ ⊕ M₂` -/
lemma BinaryMatroid.DeltaSum.SpecialCase1Sum {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁M₂ : Disjoint M₁.E M₂.E) : Matroid.disjointSum M₁.matroid M₂.matroid hM₁M₂ = BinaryMatroid.DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_eq_all_circuits]
  constructor
  · rw [Matroid.disjointSum_ground_eq,
        VectorMatroid.E_eq, VectorMatroid.E_eq,
        BinaryMatroid.DeltaSum.E_eq, hM₁M₂.inter_eq, Set.diff_empty]
  · intro C hCE
    rw [Matroid.disjointSum_ground_eq, VectorMatroid.E_eq, VectorMatroid.E_eq] at hCE
    rw [Matroid.disjointSum_circuit_iff, BinaryMatroid.DeltaSum.circuit_iff]
    constructor
    · intro hCcirc
      cases hCcirc with
      | inl hCM₁ =>
          have hC : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ C := ⟨hCM₁, disjoint_inter_disjoint C hM₁M₂⟩
          exact hC.disjoint_circuit_pred hM₁M₂
      | inr hCM₂ =>
          have hC : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ C := ⟨hCM₂, disjoint_inter_disjoint C hM₁M₂⟩
          exact hC.disjoint_circuit_pred hM₁M₂
    · intro hC
      have ⟨⟨hCnempty, hCE, X₁, X₂, hCX₁X₂, hX₁udc, hX₂udc⟩, hCmin⟩ := hC
      if hX₂empty : X₂ = ∅ then
          left
          rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCX₁X₂
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ hC (hCX₁X₂ ▸ hX₁udc)
      else
        if hX₁empty : X₁ = ∅ then
          right
          rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCX₁X₂
          exact BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ hC (hCX₁X₂ ▸ hX₂udc)
        else
          apply Set.nonempty_iff_ne_empty.mpr at hX₁empty
          apply Set.nonempty_iff_ne_empty.mpr at hX₂empty

          have hX₁E : X₁ ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ := by
            rw [BinaryMatroid.DeltaSum.E, hM₁M₂.inter_eq, Set.diff_empty]
            exact Set.subset_union_of_subset_left hX₁udc.subset_ground M₂.E

          have hX₁X₂ := Set.disjoint_of_subset hX₁udc.subset_ground hX₂udc.subset_ground hM₁M₂
          rw [hX₁X₂.inter_eq, Set.diff_empty] at hCX₁X₂

          specialize hCmin (BinaryMatroid.DeltaSum.CircuitForm_left hX₁empty hX₁E hX₁udc)
          specialize hCmin (hCX₁X₂.symm ▸ Set.subset_union_left)
          apply Set.ssubset_of_ssubset_of_subset (hCX₁X₂ ▸ ssubset_disjoint_union_nonempty hX₁X₂ hX₂empty) at hCmin
          exact False.elim ((HasSSubset.SSubset.ne hCmin) rfl)


section SpecialCase2Sum

/-- If `M₁` and `M₂` satisfy the 2-sum assumptions, then `M₁ Δ M₂ = M₁ ⊕₂ M₂` -/
lemma BinaryMatroid.DeltaSum.SpecialCase2Sum {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (Assumptions : Matroid.TwoSum.Assumptions M₁.matroid M₂.matroid) :
    Matroid.TwoSum.matroid Assumptions = BinaryMatroid.DeltaSum.matroid M₁ M₂ := by
  rw [Matroid.eq_iff_eq_all_circuits]
  constructor
  · exact rfl
  · intro C hCE
    rw [Matroid.TwoSum.circuit_iff, BinaryMatroid.DeltaSum.circuit_iff]
    unfold Matroid.TwoSum.E
    rw [Matroid.TwoSum.E_eq] at hCE
    rw [VectorMatroid.E_eq, VectorMatroid.E_eq] at hCE ⊢
    constructor
    · intro ⟨_hCE, hC⟩
      unfold Matroid.TwoSum.CircuitPred at hC
      cases hC with
      | inl hC => exact CircuitForm1.sum2_circuit_pred hC Assumptions
      | inr hC => cases hC with
        | inl hC => exact CircuitForm2.sum2_circuit_pred hC Assumptions
        | inr hC =>
            obtain ⟨p, hp⟩ := Assumptions.inter_singleton
            have hCcf3 : BinaryMatroid.DeltaSum.CircuitForm3 M₁ M₂ C p := ⟨
              M₁.E_eq ▸ hp ▸ hC.to_circuit_M₁,
              M₂.E_eq ▸ hp ▸ hC.to_circuit_M₂,
              hCE,
            ⟩
            exact hCcf3.sum2_circuit_pred Assumptions
    · intro hC
      constructor
      · exact hCE
      · have ⟨⟨hCnempty, _hCE, X₁, X₂, hCX₁X₂, hX₁udc, hX₂udc⟩, hCmin⟩ := hC
        if hX₂empty : X₂ = ∅ then
          left
          rw [hX₂empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCX₁X₂
          exact ⟨BinaryMatroid.DeltaSum.CircuitPred_udc_M₁ hC (hCX₁X₂ ▸ hX₁udc), (Set.subset_diff.mp hCE).2⟩
        else
          right
          if hX₁empty : X₁ = ∅ then
            left
            rw [hX₁empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCX₁X₂
            exact ⟨BinaryMatroid.DeltaSum.CircuitPred_udc_M₂ hC (hCX₁X₂ ▸ hX₂udc), (Set.subset_diff.mp hCE).2⟩
          else
            right
            apply Set.nonempty_iff_ne_empty.mpr at hX₁empty
            apply Set.nonempty_iff_ne_empty.mpr at hX₂empty
            have hX₁dep := Matroid.UnionDisjointCircuits.nonempty_dep M₁.matroid X₁ hX₁udc hX₁empty
            have hX₂dep := Matroid.UnionDisjointCircuits.nonempty_dep M₂.matroid X₂ hX₂udc hX₂empty

            obtain ⟨p, hp⟩ := M₁.E_eq ▸ M₂.E_eq ▸ Assumptions.inter_singleton
            have hX₁X₂p := hp ▸ Set.inter_subset_inter hX₁udc.subset_ground hX₂udc.subset_ground

            have hpX₁ : {p} ⊆ X₁ := by
              -- todo: clean up
              by_contra hnpX₁
              rw [Set.singleton_subset_iff] at hnpX₁
              have hX₁p : Disjoint X₁ {p} := Set.disjoint_singleton_right.mpr hnpX₁
              have hpInter : p ∉ X₁ ∩ X₂ := fun h => hnpX₁ (Set.mem_of_mem_inter_left h)
              have hpInter2 : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl hpInter).symm
              have hX₁X₂ : X₁ ∩ X₂ = ∅ := by
                by_contra h
                cases Set.subset_singleton_iff_eq.mp hX₁X₂p with
                | inl t => exact h t
                | inr t => exact hpInter2 t
              have hX₁inter : Disjoint X₁ (M₁.E ∩ M₂.E) := hp ▸ hX₁p
              have hX₁C : X₁ ⊆ C := (Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂) ▸ Set.subset_union_left
              have ⟨Y₁, hY₁, hY₁X₁⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hX₁dep
              have hY₁inter := Set.disjoint_of_subset_left hY₁X₁ hX₁inter
              have hY₁cf1 : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ Y₁ := ⟨hY₁, hY₁inter⟩
              specialize hCmin hY₁cf1.circuit_form (hY₁X₁.trans hX₁C)
              have hCeq : C = X₁ := Set.Subset.antisymm (hCmin.trans hY₁X₁) hX₁C
              have hCeq2 := Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂
              have hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_iff_inter_eq_empty.mpr hX₁X₂
              rw [hCeq] at hCeq2
              have hX₂ := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.mp hCeq2.symm)).mp hX₁X₂.symm
              exact Set.not_nonempty_empty (hX₂ ▸ hX₂empty)

            have hpX₂ : {p} ⊆ X₂ := by
              -- todo: clean up
              by_contra hnpX₂
              rw [Set.singleton_subset_iff] at hnpX₂
              have hX₂p : Disjoint X₂ {p} := Set.disjoint_singleton_right.mpr hnpX₂
              have hpInter : p ∉ X₁ ∩ X₂ := fun h => hnpX₂ (Set.mem_of_mem_inter_right h)
              have hpInter2 : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl hpInter).symm
              have hX₁X₂ : X₁ ∩ X₂ = ∅ := by
                by_contra h
                cases Set.subset_singleton_iff_eq.mp hX₁X₂p with
                | inl t => exact h t
                | inr t => exact hpInter2 t
              have hX₂inter : Disjoint X₂ (M₁.E ∩ M₂.E) := hp ▸ hX₂p
              have hX₂C : X₂ ⊆ C := (Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂) ▸ Set.subset_union_right
              have ⟨Y₂, hY₂, hY₂X₂⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hX₂dep
              have hY₂inter := Set.disjoint_of_subset_left hY₂X₂ hX₂inter
              have hY₂cf1 : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ Y₂ := ⟨hY₂, hY₂inter⟩
              specialize hCmin hY₂cf1.circuit_form (hY₂X₂.trans hX₂C)
              have hCeq : C = X₂ := Set.Subset.antisymm (hCmin.trans hY₂X₂) hX₂C
              have hCeq2 := Set.diff_empty ▸ hX₁X₂ ▸ hCX₁X₂
              rw [hCeq, Set.union_comm] at hCeq2
              have hX₁X₂ : Disjoint X₁ X₂ := Set.disjoint_iff_inter_eq_empty.mpr hX₁X₂
              have hX₁ := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.mp hCeq2.symm)).mp hX₁X₂
              exact Set.not_nonempty_empty (hX₁ ▸ hX₁empty)

            have hpX₁X₂ : X₁ ∩ X₂ = {p} := Set.Subset.antisymm hX₁X₂p (Set.subset_inter hpX₁ hpX₂)

            have hX₁C₁ : X₁ ⊆ C ∩ M₁.E ∪ {p} := by
              -- todo: neat, but unused
              rw [(Set.diff_union_inter X₁ X₂).symm]
              rw [←symmDiff_def_alt, symmDiff_def] at hCX₁X₂
              simp only [Set.sup_eq_union] at hCX₁X₂
              have hX₁mX₂C := hCX₁X₂ ▸ Set.subset_union_left
              have hX₁mX₂M₁ := M₁.E_eq ▸ Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₁udc.subset_ground X₂)
              have hX₁mX₂CiM₁ := Set.subset_inter hX₁mX₂C hX₁mX₂M₁
              exact Set.union_subset_union hX₁mX₂CiM₁ hX₁X₂p

            have hX₂C₂ : X₂ ⊆ C ∩ M₂.E ∪ {p} := by
              -- todo: neat, but unused
              rw [(Set.diff_union_inter X₂ X₁).symm]
              rw [←symmDiff_def_alt, symmDiff_def] at hCX₁X₂
              simp only [Set.sup_eq_union] at hCX₁X₂
              have hX₂mX₁C := hCX₁X₂ ▸ Set.subset_union_right
              have hX₂mX₁M₂ := M₂.E_eq ▸ Set.diff_subset_iff.mpr (Set.subset_union_of_subset_right hX₂udc.subset_ground X₁)
              have hX₁mX₂CiM₁ := Set.subset_inter hX₂mX₁C hX₂mX₁M₂
              exact Set.union_subset_union hX₁mX₂CiM₁ (Set.inter_comm X₁ X₂ ▸ hX₁X₂p)

            have hC₁eqX₁ : C ∩ M₁.E ∪ {p} = X₁ := by
              -- todo: clean up
              rw [hpX₁X₂] at hCX₁X₂
              have t1 : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congrFun (congrArg Union.union hCX₁X₂) {p}
              rw [Set.diff_union_self] at t1
              have t2 : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
              rw [Set.union_eq_left.mpr t2] at t1

              have a2 : (C ∪ {p}) ∩ M₁.E = (X₁ ∪ X₂) ∩ M₁.E := congrFun (congrArg Inter.inter t1) M₁.E
              have a3 : (X₁ ∪ X₂) ∩ M₁.E = X₁ ∩ M₁.E ∪ X₂ ∩ M₁.E := Set.union_inter_distrib_right X₁ X₂ M₁.E
              have a4 : X₁ ∩ M₁.E = X₁ := (Set.left_eq_inter.mpr hX₁udc.subset_ground).symm
              have a5 : X₂ ∩ M₁.E ⊆ M₂.E ∩ M₁.E := Set.inter_subset_inter_left M₁.E hX₂udc.subset_ground
              have a5' := (Set.inter_comm M₁.E M₂.E) ▸ a5
              have a6 : M₁.E ∩ M₂.E ⊆ X₁ := hp ▸ hpX₁
              have a7 : X₂ ∩ M₁.E ⊆ X₁ := a5'.trans a6

              have b : X₁ ∪ X₂ ∩ M₁.E = X₁ := Set.union_eq_self_of_subset_right a7

              have t3 : (C ∪ {p}) ∩ M₁.E = C ∩ M₁.E ∪ {p} ∩ M₁.E := Set.union_inter_distrib_right C {p} M₁.E
              have t4 : {p} ⊆ M₁.E := singleton_inter_subset_left hp
              have t5 : {p} ∩ M₁.E = {p} := (Set.left_eq_inter.mpr t4).symm
              rw [t5] at t3

              rw [←t3, a2, a3, a4, b]

            have hC₂eqX₂ : C ∩ M₂.E ∪ {p} = X₂ := by
              -- todo: clean up
              rw [hpX₁X₂] at hCX₁X₂
              have t1 : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congrFun (congrArg Union.union hCX₁X₂) {p}
              rw [Set.diff_union_self] at t1
              have t2 : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
              rw [Set.union_eq_left.mpr t2] at t1

              have a2 : (C ∪ {p}) ∩ M₂.E = (X₁ ∪ X₂) ∩ M₂.E := congrFun (congrArg Inter.inter t1) M₂.E
              have a3 : (X₁ ∪ X₂) ∩ M₂.E = X₁ ∩ M₂.E ∪ X₂ ∩ M₂.E := Set.union_inter_distrib_right X₁ X₂ M₂.E
              have a4 : X₂ ∩ M₂.E = X₂ := (Set.left_eq_inter.mpr hX₂udc.subset_ground).symm
              have a5 : X₁ ∩ M₂.E ⊆ M₁.E ∩ M₂.E := Set.inter_subset_inter_left M₂.E hX₁udc.subset_ground
              have a6 : M₁.E ∩ M₂.E ⊆ X₂ := hp ▸ hpX₂
              have a7 : X₁ ∩ M₂.E ⊆ X₂ := a5.trans a6

              have b : X₁ ∩ M₂.E ∪ X₂ = X₂ := Set.union_eq_self_of_subset_left a7

              have t3 : (C ∪ {p}) ∩ M₂.E = C ∩ M₂.E ∪ {p} ∩ M₂.E := Set.union_inter_distrib_right C {p} M₂.E
              have t4 : {p} ⊆ M₂.E := singleton_inter_subset_right hp
              have t5 : {p} ∩ M₂.E = {p} := (Set.left_eq_inter.mpr t4).symm
              rw [t5] at t3

              rw [←t3, a2, a3, a4, b]

            have hX₁circ : M₁.matroid.Circuit X₁ := by
              constructor
              · exact hX₁dep
              · intro Y₁ hY₁ hY₁X₁
                if hpY₁ : {p} ⊆ Y₁ then
                  have t1 : ∃ Z₁, M₁.matroid.Circuit Z₁ ∧ {p} ⊆ Z₁ ∧ Z₁ ⊆ Y₁ := sorry
                  obtain ⟨Z₁, hZ₁, hpZ₁, hZ₁Y₁⟩ := t1
                  have t2 : CircuitForm M₁ M₂ ((Z₁ ∪ X₂) \ (Z₁ ∩ X₂)) := sorry
                  specialize hCmin t2 sorry
                  sorry
                else
                  rw [Set.singleton_subset_iff] at hpY₁
                  have hY₁p : Disjoint Y₁ {p} := Set.disjoint_singleton_right.mpr hpY₁
                  have ⟨D, hD, hDY₁⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hY₁
                  have hDp : Disjoint D {p} := Set.disjoint_of_subset_left hDY₁ hY₁p
                  have hDcf1 : BinaryMatroid.DeltaSum.CircuitForm1 M₁ M₂ D := ⟨hD, hp ▸ hDp⟩
                  have hDC : D ⊆ C := by
                    have hDX₁ := hDY₁.trans hY₁X₁
                    have hDX₁X₂ : D ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_left hDX₁ X₂
                    have hDX₁X₂p : D ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hDX₁X₂ fun a => hpY₁ (hDY₁ a)
                    rw [hCX₁X₂, hpX₁X₂]
                    exact hDX₁X₂p
                  specialize hCmin hDcf1.circuit_form hDC
                  have hCeqD := Set.Subset.antisymm hCmin hDC

                  have hDinterM₂ : (C ∩ M₂.E).Nonempty := by
                    rw [hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_inter_distrib_right]
                    if hX₂p : X₂ ⊆ {p} then
                      have hX₂dep := hX₂dep.superset hX₂p (singleton_inter_subset_right hp)
                      have t1 : M₂.matroid.Circuit {p} := ⟨
                        hX₂dep,
                        by
                          intro Q hQ hQp
                          simp only [Set.le_eq_subset] at hQp
                          rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                          exact le_of_eq_of_le (id (Eq.symm hQp)) fun ⦃a⦄ a => a
                      ⟩
                      have t2 := Assumptions.inter_singleton_not_loop_M₂ hp
                      rw [Matroid.Loop.iff_circuit] at t2
                      exfalso
                      exact t2 t1
                    else
                      rw [←Set.diff_nonempty] at hX₂p
                      have t1 : {p} ⊆ M₂.E := singleton_inter_subset_right hp
                      have t2 : X₂ ⊆ M₂.E := hX₂dep.subset_ground
                      have t3 : X₂ \ {p} ⊆ M₂.E := diff_subset_parent t2
                      have t4 : X₂ \ {p} ∩ M₂.E = X₂ \ {p} := (Set.left_eq_inter.mpr t3).symm
                      exact Set.Nonempty.inr (t4.symm ▸ hX₂p)
                  have hDM₂ : Disjoint D M₂.E := hDcf1.disjoint_M₂
                  rw [hCeqD] at hDinterM₂
                  exact False.elim (Set.not_nonempty_empty (hDM₂.inter_eq ▸ hDinterM₂))

            have hX₂circ : M₂.matroid.Circuit X₂ := by
              constructor
              · exact hX₂dep
              · intro Y₂ hY₂ hY₂X₂
                if hpY₂ : {p} ⊆ Y₂ then
                  sorry
                else
                  rw [Set.singleton_subset_iff] at hpY₂
                  have hY₂p : Disjoint Y₂ {p} := Set.disjoint_singleton_right.mpr hpY₂
                  have ⟨D, hD, hDY₂⟩ := Matroid.Circuit.dep_iff_has_circuit.mp hY₂
                  have hDp : Disjoint D {p} := Set.disjoint_of_subset_left hDY₂ hY₂p
                  have hDcf2 : BinaryMatroid.DeltaSum.CircuitForm2 M₁ M₂ D := ⟨hD, hp ▸ hDp⟩
                  have hDC : D ⊆ C := by
                    have hDX₂ := hDY₂.trans hY₂X₂
                    have hDX₁X₂ : D ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hDX₂ X₁
                    have hDX₁X₂p : D ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hDX₁X₂ fun a => hpY₂ (hDY₂ a)
                    rw [hCX₁X₂, hpX₁X₂]
                    exact hDX₁X₂p
                  specialize hCmin hDcf2.circuit_form hDC
                  have hCeqD := Set.Subset.antisymm hCmin hDC

                  have hDinterM₂ : (C ∩ M₁.E).Nonempty := by
                    rw [hCX₁X₂, hpX₁X₂, Set.union_diff_distrib, Set.union_inter_distrib_right]
                    if hX₁p : X₁ ⊆ {p} then
                      have hX₁dep := hX₁dep.superset hX₁p (singleton_inter_subset_left hp)
                      have t1 : M₁.matroid.Circuit {p} := ⟨
                        hX₁dep,
                        by
                          intro Q hQ hQp
                          simp only [Set.le_eq_subset] at hQp
                          rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                          exact le_of_eq_of_le (id (Eq.symm hQp)) fun ⦃a⦄ a => a
                      ⟩
                      have t2 := Assumptions.inter_singleton_not_loop_M₁ hp
                      rw [Matroid.Loop.iff_circuit] at t2
                      exfalso
                      exact t2 t1
                    else
                      rw [←Set.diff_nonempty] at hX₁p
                      have t1 : {p} ⊆ M₁.E := singleton_inter_subset_left hp
                      have t2 : X₁ ⊆ M₁.E := hX₁dep.subset_ground
                      have t3 : X₁ \ {p} ⊆ M₁.E := diff_subset_parent t2
                      have t4 : X₁ \ {p} ∩ M₁.E = X₁ \ {p} := (Set.left_eq_inter.mpr t3).symm
                      exact Set.Nonempty.inl (t4.symm ▸ hX₁p)
                  have hDM₂ : Disjoint D M₁.E := hDcf2.disjoint_M₁
                  rw [hCeqD] at hDinterM₂
                  exact False.elim (Set.not_nonempty_empty (hDM₂.inter_eq ▸ hDinterM₂))

            exact ⟨hp ▸ hC₁eqX₁ ▸ hX₁circ, hp ▸ hC₂eqX₂ ▸ hX₂circ, hCE⟩


section SpecialCase3Sum

/-- Assumptions for Δ-sum  -/
structure BinaryMatroid.DeltaSum.ThreeSumAssumptions {α : Type} [DecidableEq α] (M₁ M₂ : BinaryMatroid α) where
  /-- `M₁` and `M₂` are finite -/
  hM₁_finite : M₁.E.Finite
  hM₂_finite : M₂.E.Finite
  /-- `M₁` and `M₂` contain at least 7 elements -/
  hM₁_card : M₁.E.encard ≥ 7
  hM₂_card : M₂.E.encard ≥ 7
  /-- `M₁` and `M₂` meet at a set `T` that is a triangle in both -/
  hT : (M₁.E ∩ M₂.E).encard = 3
  hTM₁ : M₁.matroid.Circuit (M₁.E ∩ M₂.E)
  hTM₂ : M₂.matroid.Circuit (M₁.E ∩ M₂.E)
  /-- Neither `M₁` nor `M₂` has a cocircuit contained in `T` -/
  hT_no_sub_cocircuit : ∀ T' ⊆ M₁.E ∩ M₂.E, ¬M₁.matroid.dual.Circuit T' ∧ ¬M₂.matroid.dual.Circuit T'

-- todo: Lemma 9.3.3 from Oxley
-- todo: Lemma 9.3.4 from Oxley
