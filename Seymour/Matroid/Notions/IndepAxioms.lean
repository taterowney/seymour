import Mathlib.Data.Matroid.Basic
import Seymour.Basic


/-- Independence predicate, defines which sets are independent. -/
abbrev IndepPredicate (α : Type) := Set α → Prop


variable {α : Type}

/-- Independence predicate of matroid. -/
def Matroid.IndepPredicate (M : Matroid α) : IndepPredicate α := M.Indep


section IndepAxioms

/-- Axiom (I1): empty set is independent. -/
def IndepPredicate.indep_empty (P : IndepPredicate α) : Prop := P ∅
alias IndepPredicate.Bruhni1 := IndepPredicate.indep_empty

/-- Axiom (I2): subset of independent set is independent. -/
def IndepPredicate.indep_subset (P : IndepPredicate α) : Prop := ∀ I J, P J → I ⊆ J → P I
alias IndepPredicate.BruhnI2 := IndepPredicate.indep_subset

/-- Axiom (I3): augmentation property. -/
def IndepPredicate.indep_aug (P : IndepPredicate α) : Prop :=
  ∀ I B, P I → ¬Maximal P I → Maximal P B → ∃ x ∈ B \ I, P (x ᕃ I)
alias IndepPredicate.BruhnI3 := IndepPredicate.indep_aug

/-- Axiom (IM): set of all independent sets has the maximal subset property. -/
def IndepPredicate.indep_maximal (P : IndepPredicate α) (E : Set α) : Prop :=
  ∀ X : Set α, X ⊆ E → Matroid.ExistsMaximalSubsetProperty P X
alias IndepPredicate.BruhnIM := IndepPredicate.indep_maximal

/-- Every independent set is a subset of the ground set. -/
def IndepPredicate.subset_ground (P : IndepPredicate α) (E : Set α) : Prop := ∀ C : Set α, P C → C ⊆ E
alias IndepPredicate.BruhnCE := IndepPredicate.subset_ground

end IndepAxioms


section MatroidIndepAxioms

/-- Independence predicate of matroid satisfies (I1): empty set is independent. -/
lemma Matroid.indep_empty (M : Matroid α) :
    M.IndepPredicate.indep_empty :=
  M.empty_indep

/-- Independence predicate of matroid satisfies (I2): subset of independent set is independent. -/
lemma Matroid.indep_subset (M : Matroid α) :
    M.IndepPredicate.indep_subset :=
  fun _ _ => Matroid.Indep.subset

/-- Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indep_aug (M : Matroid α) :
    M.IndepPredicate.indep_aug :=
  fun _ _ hI nonmaximal_M_I maximal_M_I' => Indep.exists_insert_of_not_maximal M hI nonmaximal_M_I maximal_M_I'

/-- (Alternative proof.) Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indep_aug_alt (M : Matroid α) :
    M.IndepPredicate.indep_aug := by
  -- Follows part of proof from Theorem 4.1 (i) from Bruhn et al.
  intro I I' hI nonmaximal_M_I maximal_M_I'
  have ⟨B, hIB, maximal_B⟩ := M.maximality M.E Set.Subset.rfl I hI (Matroid.Indep.subset_ground hI)
  if hBI : (B \ I).Nonempty then
    obtain ⟨x, hx⟩ := hBI
    if hxI' : x ∈ I' then
      exact ⟨x,
        Set.mem_diff_of_mem hxI' (Set.not_mem_of_mem_diff hx),
        Matroid.Indep.subset maximal_B.left.left (Set.insert_subset (Set.mem_of_mem_diff hx) hIB),
      ⟩
    else
      have hB : Maximal M.Indep B :=
        ⟨maximal_B.left.left, fun C hC hBC => maximal_B.right ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
      unfold Matroid.IndepPredicate at maximal_M_I'
      rw [←Matroid.base_iff_maximal_indep] at maximal_M_I' hB
      obtain ⟨y, hy, hMyBx⟩ := M.base_exchange B I' hB maximal_M_I' x (Set.mem_diff_of_mem (Set.mem_of_mem_diff hx) hxI')
      exact ⟨y,
        Set.mem_diff_of_mem (Set.mem_of_mem_diff hy) (fun a => (Set.not_mem_of_mem_diff hy) (hIB a)),
        Matroid.Indep.subset (Matroid.Base.indep hMyBx)
          (Set.insert_subset_insert (Set.subset_diff_singleton hIB (Set.not_mem_of_mem_diff hx))),
      ⟩
  else
    have I_eq_B : I = B := Set.union_empty I ▸ (Set.not_nonempty_iff_eq_empty.→ hBI) ▸ Set.union_diff_cancel hIB
    have maximal_B : Maximal M.Indep B :=
      ⟨maximal_B.left.left, fun _ hC hBC => maximal_B.right ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
    exact (nonmaximal_M_I (I_eq_B ▸ maximal_B)).elim

/-- Independence predicate of matroid satisfies (IM): set of all independent sets has the maximal subset property. -/
lemma Matroid.indep_maximal (M : Matroid α) :
    M.IndepPredicate.indep_maximal M.E :=
  M.maximality

/-- Every independent set is a subset of the ground set. -/
lemma Matroid.indep_subset_ground (M : Matroid α) :
    M.IndepPredicate.subset_ground M.E :=
  fun _ => Matroid.Indep.subset_ground

end MatroidIndepAxioms
