import Seymour.Matroid.Notions.Circuit


variable {α : Type}


section DisjointCircuitFamily

/-- Family of disjoint circuits of matroid `M`. -/
structure Matroid.disjointCircuitFamily (M : Matroid α) where
  /-- Indexing set -/
  ι : Set α
  -- question: upgrade from indexing by Set α to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  -- note: if we know that `C` is a disjoint union of circuits of `M`,
  -- then wlog we can choose `ι` to be set of representatives of those circuits
  /-- Set family indexed by `ι` -/
  F : ι → Set α
  /-- All sets in family are circuits in `M` -/
  AllCircuits : ∀ x : ι, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  AllDisjoint : ∀ x y : ι, x ≠ y → F x ⫗ F y

/-- Shorthand for union of sets in `M.disjointCircuitFamily`. -/
def Matroid.disjointCircuitFamily.union {M : Matroid α} (F : M.disjointCircuitFamily) : Set α :=
  Set.iUnion F.F

/-- Every element in `M.disjointCircuitFamily` is subset of ground set. -/
lemma Matroid.disjointCircuitFamily.mem_subset_ground {M : Matroid α} (F : M.disjointCircuitFamily) (x : F.ι) :
    F.F x ⊆ M.E :=
  (F.AllCircuits x).subset_ground

/-- Union of sets in `M.disjointCircuitFamily` is subset of ground set. -/
lemma Matroid.disjointCircuitFamily.union_subset_ground {M : Matroid α} (F : M.disjointCircuitFamily) :
    F.union ⊆ M.E := by
  simp only [Matroid.disjointCircuitFamily.union, Set.iUnion_coe_set, Set.iUnion_subset_iff]
  exact fun i hi => mem_subset_ground F ⟨i, hi⟩

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.disjointCircuitFamily.union_indep_empty {M : Matroid α} (F : M.disjointCircuitFamily) (hMF : M.Indep F.union):
    F.union = ∅ := by
  by_contra
  obtain ⟨x, hx⟩ : ∃ x, (F.F x).Nonempty
  · by_contra!
    simp_all only [Matroid.disjointCircuitFamily.union, Set.iUnion_coe_set, Set.iUnion_empty, not_true_eq_false]
  apply (F.AllCircuits x).left.not_indep
  have F_x_sub_F_union : F.F x ⊆ F.union := Set.subset_iUnion_of_subset x Set.Subset.rfl
  exact hMF.subset F_x_sub_F_union

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.disjointCircuitFamily.union_nonempty_dep {M : Matroid α} (F : M.disjointCircuitFamily) (hF : F.union.Nonempty) :
    M.Dep F.union := by
  by_contra contr
  exact Set.not_nonempty_empty (F.union_indep_empty (Matroid.indep_of_not_dep contr F.union_subset_ground) ▸ hF)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma Matroid.disjointCircuitFamily.dep_or_empty {M : Matroid α} (F : M.disjointCircuitFamily) :
    M.Dep F.union ∨ F.union = ∅ := by
  if hMF : M.Indep F.union then
    exact Or.inr (F.union_indep_empty hMF)
  else
    exact Or.inl ⟨hMF, F.union_subset_ground⟩

/-- Empty family of disjoint circuits. -/
def Matroid.emptyDisjointCircuitFamily (M : Matroid α) :
    M.disjointCircuitFamily where
  ι := ∅
  F _ := ∅
  AllCircuits x := x.property.elim
  AllDisjoint x := x.property.elim

/-- Union of sets in empty family is empty. -/
lemma Matroid.emptyDisjointCircuitFamily_union (M : Matroid α) :
    M.emptyDisjointCircuitFamily.union = ∅ :=
  Set.iUnion_empty

/-- Family of one circuit, indexed by one element --- that circuit. -/
def Matroid.Circuit.singleDisjointCircuitFamily {M : Matroid α} {C : Set α} (hC : M.Circuit C) (p : α) :
    M.disjointCircuitFamily where
  ι := {p}
  F _ := C
  AllCircuits _ := hC
  AllDisjoint x y hxy := ((x.property ▸ y.property ▸ Subtype.coe_ne_coe.← hxy) rfl).elim

/-- Union of sets in family of one circuit is that circuit. -/
lemma Matroid.Circuit.singleDisjointCircuitFamily_union {M : Matroid α} {C : Set α} (hC : M.Circuit C) (p : α) :
    (hC.singleDisjointCircuitFamily p).union = C := by
  simp only [Matroid.Circuit.singleDisjointCircuitFamily, Matroid.disjointCircuitFamily.union, Set.iUnion_coe_set,
    Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

end DisjointCircuitFamily


section UnionDisjointCircuits

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
def Matroid.IsUnionDisjointCircuits (M : Matroid α) (C : Set α) : Prop :=
  ∃ F : M.disjointCircuitFamily, F.union = C

/-- Empty set is disjoint union of circuits. -/
lemma Matroid.emptyUnionDisjointCircuits (M : Matroid α) :
    M.IsUnionDisjointCircuits ∅ :=
  ⟨M.emptyDisjointCircuitFamily, M.emptyDisjointCircuitFamily_union⟩

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.IsUnionDisjointCircuits.indep_empty {M : Matroid α} {X : Set α}
    (hMX : M.IsUnionDisjointCircuits X) (hMX' : M.Indep X) :
    X = ∅ :=
  have ⟨F, hXF⟩ := hMX
  F.union_indep_empty (hXF ▸ hMX') ▸ hXF.symm

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.IsUnionDisjointCircuits.nonempty_dep {M : Matroid α} {X : Set α}
    (hMX : M.IsUnionDisjointCircuits X) (hX : X.Nonempty) :
    M.Dep X :=
  have ⟨F, hXF⟩ := hMX
  hXF ▸ F.union_nonempty_dep (hXF ▸ hX)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma Matroid.IsUnionDisjointCircuits.dep_or_empty {M : Matroid α} {X : Set α} (hMX : M.IsUnionDisjointCircuits X) :
    M.Dep X ∨ X = ∅ :=
  have ⟨F, hXF⟩ := hMX
  hXF ▸ F.dep_or_empty

/-- One circuit is disjoint union of circuits. -/
lemma Matroid.Circuit.isUnionDisjointCircuits {M : Matroid α} {C : Set α} (hC : M.Circuit C) :
    M.IsUnionDisjointCircuits C :=
  have ⟨x, _⟩ := hC.nonempty
  ⟨hC.singleDisjointCircuitFamily x, hC.singleDisjointCircuitFamily_union x⟩

/-- Union of disjoint circuits is subset of ground set. -/
lemma Matroid.IsUnionDisjointCircuits.subset_ground {M : Matroid α} {X : Set α} (hMX : M.IsUnionDisjointCircuits X) :
    X ⊆ M.E :=
  have ⟨F, hXF⟩ := hMX
  hXF ▸ F.union_subset_ground

end UnionDisjointCircuits
