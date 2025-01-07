import Seymour.Matroid.Notions.Circuit


variable {α : Type}


section DisjointCircuitFamily

/-- Family of disjoint circuits of matroid `M`. -/
structure DisjointCircuitFamily (M : Matroid α) where
  /-- Indexing set -/
  Idx : Set α
  -- question: upgrade from indexing by Set α to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  -- note: if we know that `C` is a disjoint union of circuits of `M`,
  -- then wlog we can choose `Idx` to be set of representatives of those circuits
  /-- Set family indexed by `Idx` -/
  F : Idx → Set α
  /-- All sets in family are circuits in `M` -/
  hCircuit : ∀ x, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  hDisjoint : ∀ x y, x ≠ y → Disjoint (F x) (F y)

/-- Shorthand for union of sets in `DisjointCircuitFamily`. -/
def DisjointCircuitFamily.union {M : Matroid α} (F : DisjointCircuitFamily M) : Set α :=
  Set.iUnion F.F

/-- Every element in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.mem_subset_ground {M : Matroid α} (F : DisjointCircuitFamily M) (x : F.Idx) :
    F.F x ⊆ M.E :=
  (F.hCircuit x).subset_ground

/-- Union of sets in `DisjointCircuitFamily` is subset of ground set. -/
lemma DisjointCircuitFamily.union_subset_ground {M : Matroid α} (F : DisjointCircuitFamily M) :
    F.union ⊆ M.E := by
  simp only [union, Set.iUnion_coe_set, Set.iUnion_subset_iff]
  exact fun i i_1 => mem_subset_ground F (Subtype.mk i i_1)

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma DisjointCircuitFamily.union_indep_empty {M : Matroid α} (F : DisjointCircuitFamily M) :
    M.Indep F.union → F.union = ∅ := by
  intro hFindep
  by_contra hFnempty
  have hx : ∃ x, (F.F x).Nonempty := by
    by_contra h
    push_neg at h
    unfold union at hFnempty
    simp_all only [Set.iUnion_coe_set, Set.iUnion_empty, not_true_eq_false]
  obtain ⟨x, hx⟩ := hx
  have hFxdep := Matroid.Dep.not_indep (F.hCircuit x).1
  have hFxsubF : F.F x ⊆ F.union := Set.subset_iUnion_of_subset x Set.Subset.rfl
  have hFxindep := Matroid.Indep.subset hFindep hFxsubF
  exact hFxdep hFxindep

/-- Nonempty union of disjoint circuits is dependent. -/
lemma DisjointCircuitFamily.union_nonempty_dep {M : Matroid α} (F : DisjointCircuitFamily M) :
    F.union.Nonempty → M.Dep F.union := by
  intro hF
  by_contra h
  exact Set.not_nonempty_empty (F.union_indep_empty (Matroid.indep_of_not_dep h F.union_subset_ground) ▸ hF)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma DisjointCircuitFamily.dep_or_empty {M : Matroid α} (F : DisjointCircuitFamily M) :
    M.Dep F.union ∨ F.union = ∅ := by
  if h: M.Indep F.union then
    exact Or.inr (F.union_indep_empty h)
  else
    exact Or.inl ⟨h, F.union_subset_ground⟩

/-- Empty family of disjoint circuits. -/
def DisjointCircuitFamily.Empty (M : Matroid α) :
    DisjointCircuitFamily M where
  Idx := ∅
  F := fun _ => ∅
  hCircuit := fun x => False.elim x.2
  hDisjoint := fun x => False.elim x.2

/-- Union of sets in empty family is empty. -/
lemma DisjointCircuitFamily.Empty_union {M : Matroid α} :
    (DisjointCircuitFamily.Empty M).union = ∅ := Set.iUnion_empty

/-- Family of one circuit, indexed by one element --- that circuit. -/
def DisjointCircuitFamily.One {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    DisjointCircuitFamily M where
  Idx := {p}
  F := fun _ => C
  hCircuit := fun _ => hC
  hDisjoint := fun x y hxy => False.elim ((x.2 ▸ y.2 ▸ (Subtype.coe_ne_coe.mpr hxy)) rfl)

/-- Union of sets in family of one circuit is that circuit. -/
lemma DisjointCircuitFamily.One_union {M : Matroid α} {C : Set α} (p : α) (hC : M.Circuit C) :
    (DisjointCircuitFamily.One p hC).union = C := by
  simp only [One, union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

end DisjointCircuitFamily


section UnionDisjointCircuits

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
def Matroid.UnionDisjointCircuits (M : Matroid α) (C : Set α) : Prop :=
  ∃ F : DisjointCircuitFamily M, C = F.union

/-- Empty set is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.empty (M : Matroid α) :
    M.UnionDisjointCircuits ∅ := by
  use DisjointCircuitFamily.Empty M
  exact DisjointCircuitFamily.Empty_union.symm

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.UnionDisjointCircuits.indep_empty (M : Matroid α) (X : Set α) :
    M.UnionDisjointCircuits X → M.Indep X → X = ∅ :=
  fun ⟨F, hXF⟩ hXindep => F.union_indep_empty (hXF ▸ hXindep) ▸ hXF

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.UnionDisjointCircuits.nonempty_dep (M : Matroid α) (X : Set α) :
    M.UnionDisjointCircuits X → X.Nonempty → M.Dep X :=
  fun ⟨F, hXF⟩ hXnempty => hXF ▸ F.union_nonempty_dep (hXF ▸ hXnempty)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma Matroid.UnionDisjointCircuits.dep_or_empty (M : Matroid α) (X : Set α) :
    M.UnionDisjointCircuits X → (M.Dep X ∨ X = ∅) :=
  fun ⟨F, hXF⟩ => hXF ▸ F.dep_or_empty

/-- One circuit is disjoint union of circuits. -/
lemma Matroid.UnionDisjointCircuits.circuit {M : Matroid α} {C : Set α} (hC : M.Circuit C) :
    M.UnionDisjointCircuits C := by
  obtain ⟨x, _hxC⟩ := Matroid.Circuit.nonempty hC
  use DisjointCircuitFamily.One x hC
  exact (DisjointCircuitFamily.One_union x hC).symm

/-- Union of disjoint circuits is subset of ground set. -/
lemma Matroid.UnionDisjointCircuits.subset_ground (M : Matroid α) (X : Set α) :
    M.UnionDisjointCircuits X → X ⊆ M.E :=
  fun ⟨F, hXF⟩ => hXF ▸ F.union_subset_ground

end UnionDisjointCircuits
