import Seymour.Matroid.Classes.Binary
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Operations.SumDelta.DisjointCircuitFamily


variable {α : Type}


section BasicDefinitions

/-- Ground set of Δ-sum is symmetric difference of ground sets of summand matroids -/
def BinaryMatroid.DeltaSum.E (M₁ M₂ : BinaryMatroid α) : Set α := (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)

/-- Circuits in `M₁ Δ M₂` are nonempty subsets of the ground set of form `X₁ Δ X₂`
    where `X₁`, `X₂` are disjoint unions of circuits in `M₁`, `M₂`, resp -/
def BinaryMatroid.DeltaSum.CircuitForm.prop (M₁ M₂ : BinaryMatroid α) (C X₁ X₂ : Set α) : Prop :=
  C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) ∧ M₁.toMatroid.IsUnionDisjointCircuits X₁ ∧ M₂.toMatroid.IsUnionDisjointCircuits X₂

/-- A set satisfies circuit form if for some `X₁` and `X₂` it has the form above -/
def BinaryMatroid.DeltaSum.CircuitForm (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  C.Nonempty ∧ C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ ∧ ∃ X₁ X₂, BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where X₁ and X₂ is a disjoint union of circuits of M₁ and M₂, respectively -/
def BinaryMatroid.DeltaSum.CircuitPred (M₁ M₂ : BinaryMatroid α) : CircuitPredicate α :=
  Minimal (BinaryMatroid.DeltaSum.CircuitForm M₁ M₂)

end BasicDefinitions


section BasicProperties

/-- Ground set of Δ-sum is disjoint with `M₁.E ∩ M₂.E` -/
lemma BinaryMatroid.DeltaSum.E.disjoint_inter (M₁ M₂ : BinaryMatroid α) :
    BinaryMatroid.DeltaSum.E M₁ M₂ ⫗ M₁.E ∩ M₂.E :=
  Set.disjoint_sdiff_left

/-- Ground sets minus their intersection are disjoint sets -/
lemma BinaryMatroid.DeltaSum.disjoint_grounds_diff_inter (M₁ M₂ : BinaryMatroid α) :
    M₁.E \ (M₁.E ∩ M₂.E) ⫗ M₂.E \ (M₁.E ∩ M₂.E) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff

/-- A set of circuit form is nonempty -/
lemma BinaryMatroid.DeltaSum.CircuitForm.nonempty {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C) : C.Nonempty :=
  hC.left

/-- A set of circuit form is a subset of the ground set -/
lemma BinaryMatroid.DeltaSum.CircuitForm.subset_ground {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm M₁ M₂ C) : C ⊆ BinaryMatroid.DeltaSum.E M₁ M₂ :=
  hC.right.left

/-- A set of circuit form is the symmetric difference of `X₁` and `X₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.eq_symmDiff {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) :
    C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) :=
  hC.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₁` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.udc_left {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) :
    M₁.toMatroid.IsUnionDisjointCircuits X₁ :=
  hC.right.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₂` -/
lemma BinaryMatroid.DeltaSum.CircuitForm.prop.udc_right {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : BinaryMatroid.DeltaSum.CircuitForm.prop M₁ M₂ C X₁ X₂) :
    M₂.toMatroid.IsUnionDisjointCircuits X₂ :=
  hC.right.right

end BasicProperties


section CircuitAxioms

/-- In circuit construction of Δ-sum, empty set is not circuit -/
lemma BinaryMatroid.DeltaSum.CircuitPred.not_circuit_empty (M₁ M₂ : BinaryMatroid α) :
    ¬BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ ∅ := by
  unfold BinaryMatroid.DeltaSum.CircuitPred Minimal CircuitForm CircuitForm.prop
  simp only [Set.not_nonempty_empty, Set.empty_subset, true_and, false_and, exists_const,
    exists_and_left, Set.le_eq_subset, Set.subset_empty_iff, implies_true, and_true,
    not_false_eq_true]

/-- In circuit construction of Δ-sum, no circuit is strict subset of another circuit -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_not_ssubset (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).circuit_not_ssubset := by
  intro C C' hC hC'
  sorry

/-- In circuit construction of Δ-sum, circuit predicate satisfies axiom (C3) -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_c3 (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).axiom_c3 := by
  intro X C F z hz
  sorry

/-- In circuit construction of Δ-sum, set of all circuit-independent sets has the maximal subset prop -/
lemma BinaryMatroid.DeltaSum.CircuitPred.circuit_maximal (M₁ M₂ : BinaryMatroid α) :
    (BinaryMatroid.DeltaSum.CircuitPred M₁ M₂).circuit_maximal (BinaryMatroid.DeltaSum.E M₁ M₂) := by
  intro X hXE
  sorry

/-- In circuit construction of Δ-sum, every circuit is subset of ground set -/
lemma BinaryMatroid.DeltaSum.CircuitPred.subset_ground {M₁ M₂ : BinaryMatroid α} (C : Set α) (hC : CircuitPred M₁ M₂ C) :
    C ⊆ E M₁ M₂ :=
  hC.left.subset_ground

end CircuitAxioms


section API

/-- Construction of Δ-sum via circuits -/
def BinaryMatroid.DeltaSum.CircuitMatroid (M₁ M₂ : BinaryMatroid α) : CircuitMatroid α where
  E := BinaryMatroid.DeltaSum.E M₁ M₂
  CircuitPred := BinaryMatroid.DeltaSum.CircuitPred M₁ M₂
  not_circuit_empty := BinaryMatroid.DeltaSum.CircuitPred.not_circuit_empty M₁ M₂
  circuit_not_ssubset := BinaryMatroid.DeltaSum.CircuitPred.circuit_not_ssubset M₁ M₂
  circuit_c3 :=  BinaryMatroid.DeltaSum.CircuitPred.circuit_c3 M₁ M₂
  circuit_maximal :=  BinaryMatroid.DeltaSum.CircuitPred.circuit_maximal M₁ M₂
  subset_ground := BinaryMatroid.DeltaSum.CircuitPred.subset_ground

/-- Matroid corresponding to Δ-sum -/
def BinaryMatroid.DeltaSum.matroid (M₁ M₂ : BinaryMatroid α) : Matroid α :=
  (BinaryMatroid.DeltaSum.CircuitMatroid M₁ M₂).matroid

@[simp]
lemma BinaryMatroid.DeltaSum.E_eq (M₁ M₂ : BinaryMatroid α) :
  (BinaryMatroid.DeltaSum.matroid M₁ M₂).E = (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) := rfl

@[simp]
lemma BinaryMatroid.DeltaSum.CircuitPred_iff (M₁ M₂ : BinaryMatroid α) :
  (BinaryMatroid.DeltaSum.CircuitMatroid M₁ M₂).CircuitPred = BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ := rfl

@[simp]
lemma BinaryMatroid.DeltaSum.circuit_iff (M₁ M₂ : BinaryMatroid α) {C : Set α} :
    (BinaryMatroid.DeltaSum.matroid M₁ M₂).Circuit C ↔ BinaryMatroid.DeltaSum.CircuitPred M₁ M₂ C := by
  unfold matroid
  rw [CircuitMatroid.circuit_iff]
  exact ⟨And.right, fun hC => ⟨hC.subset_ground, hC⟩⟩

end API
