import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.IndepAxioms

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Notions.Circuit


/-- Matroid defined by circuit axioms. -/
structure CircuitMatroid (α : Type) where
  /-- The ground set -/
  (E : Set α)
  /-- The circuit predicate -/
  (CircuitPred : CircuitPredicate α)
  /-- Empty set is not a circuit -/
  (not_circuit_empty : CircuitPred.not_circuit_empty)
  /-- No circuit is a subset of another circuit -/
  (circuit_not_ssubset : CircuitPred.circuit_not_ssubset)
  /-- Condition (C3) from Bruhn et al. -/
  (circuit_c3 : CircuitPred.axiom_c3)
  /-- Corresponding family of independent sets satisfies the maximal subset property -/
  (circuit_maximal : CircuitPred.circuit_maximal E)
  /-- Every circuit is a subset of the ground set -/
  (subset_ground : CircuitPred.subset_ground E) -- question: unused?

variable {α : Type}

/-- Corresponding independence predicate of circuit matroid. -/
def CircuitMatroid.IndepPred (M : CircuitMatroid α) :
    IndepPredicate α :=
  M.CircuitPred.toIndepPredicate M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I1): empty set is independent. -/
lemma CircuitMatroid.indep_empty (M : CircuitMatroid α) :
    M.IndepPred.indep_empty :=
  CircuitPredicate.toIndepPredicate.indep_empty M.not_circuit_empty M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I2): subsets of independent sets are independent. -/
lemma CircuitMatroid.indep_subset (M : CircuitMatroid α) :
    M.IndepPred.indep_subset :=
  CircuitPredicate.toIndepPredicate.indep_subset M.CircuitPred M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I3): independent sets have augmentation property. -/
lemma CircuitMatroid.indep_aug (M : CircuitMatroid α) :
    M.IndepPred.indep_aug :=
  CircuitPredicate.toIndepPredicate.indep_aug M.circuit_maximal M.circuit_c3

/-- Corresponding independence predicate of circuit matroid satisfies (IM): independent sets have maximal property. -/
lemma CircuitMatroid.indep_maximal (M : CircuitMatroid α) :
    M.IndepPred.indep_maximal M.E :=
  CircuitPredicate.toIndepPredicate.indep_maximal M.CircuitPred M.E

/-- Corresponding independence predicate of circuit matroid satisfies (IE): independent sets are subsets of ground set. -/
lemma CircuitMatroid.indep_subset_ground (M : CircuitMatroid α) :
    M.IndepPred.subset_ground M.E :=
  CircuitPredicate.toIndepPredicate.subset_ground M.CircuitPred M.E

/-- `IndepMatroid` corresponding to circuit matroid. -/
def CircuitMatroid.toIndepMatroid (M : CircuitMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.IndepPred
  indep_empty := M.indep_empty
  indep_subset := M.indep_subset
  indep_aug := M.indep_aug
  indep_maximal := M.indep_maximal
  subset_ground := M.indep_subset_ground

/-- Circuit matroid converted to `Matroid`. -/
def CircuitMatroid.toMatroid (M : CircuitMatroid α) : Matroid α := M.toIndepMatroid.matroid

/-- Registered conversion from `CircuitMatroid` to `Matroid`. -/
instance : Coe (CircuitMatroid α) (Matroid α) where
  coe := CircuitMatroid.toMatroid

lemma CircuitMatroid.maximal_iff (M : CircuitMatroid α) (B : Set α) :
    Maximal (fun K : Set α => M.IndepPred K ∧ K ⊆ M.E) B ↔ Maximal M.IndepPred B :=
  ⟨fun hB => ⟨hB.left.left, fun _ hA hBA => hB.right ⟨hA, hA.left⟩ hBA⟩,
   fun hB => ⟨⟨hB.left, hB.left.left⟩, fun _ hA => hB.right hA.left⟩⟩

@[simp] lemma CircuitMatroid.toMatroid_E (M : CircuitMatroid α) : M.toMatroid.E = M.E :=
  rfl

@[simp] lemma CircuitMatroid.toMatroid_indep (M : CircuitMatroid α) : M.toMatroid.Indep = M.IndepPred :=
  rfl

@[simp] lemma CircuitMatroid.toMatroid_circuit_iff (M : CircuitMatroid α) {C : Set α} :
    M.toMatroid.Circuit C ↔ (C ⊆ M.E ∧ M.CircuitPred C) := by
  constructor
  · intro hC
    constructor
    · exact hC.subset_ground
    obtain ⟨⟨hCdep, hCE⟩, hCmin⟩ := hC
    obtain ⟨D, ⟨_, ⟨⟨hDindep, hDC⟩, hDmax⟩⟩⟩ :=
      M.circuit_maximal C hCE ∅ (CircuitPredicate.toIndepPredicate.indep_empty M.not_circuit_empty M.E) (Set.empty_subset C)
    have hDneqC : D ≠ C := by
      intro hDeqC
      rw [←hDeqC] at hCdep
      exact hCdep hDindep
    have hDssubC := Set.ssubset_iff_subset_ne.mpr ⟨hDC, hDneqC⟩
    obtain ⟨x, hxC, hxnD⟩ := Set.exists_of_ssubset hDssubC
    have hDextC : x ᕃ D = C := sorry
    sorry -- todo: finish
  · intro ⟨_, hC⟩
    constructor
    · unfold Matroid.Dep
      rw [CircuitMatroid.toMatroid_indep]
      constructor
      · unfold IndepPred CircuitPredicate.toIndepPredicate
        push_neg
        intro _
        use C
      · exact M.subset_ground C hC
    · intro D ⟨hDdep, hDE⟩ hDC
      rw [CircuitMatroid.toMatroid_indep] at hDdep
      unfold IndepPred CircuitPredicate.toIndepPredicate at hDdep
      push_neg at hDdep
      obtain ⟨C', hC'D, hC'⟩ := hDdep hDE
      have hC'nssubC := M.circuit_not_ssubset C C' hC hC'
      exact eq_of_subset_of_not_ssubset (hC'D.trans hDC) hC'nssubC ▸ hC'D

/-- todo: desc -/
lemma CircuitMatroid.toMatroid_eq_toMatroid {M₁ M₂ : CircuitMatroid α} (hMM : M₁.CircuitPred = M₂.CircuitPred) :
    M₁.toMatroid = M₂.toMatroid := by
  ext
  · sorry -- TODO is it intentional that `M₁.E = M₂.E` is not assumed?
  · sorry

/-- todo: desc -/
lemma CircuitMatroid.toMatroid_eq_toMatroid_iff (M₁ M₂ : CircuitMatroid α) :
    M₁.toMatroid = M₂.toMatroid ↔ M₁.E = M₂.E ∧ ∀ C ⊆ M₁.E, M₁.CircuitPred = M₂.CircuitPred :=
  sorry
