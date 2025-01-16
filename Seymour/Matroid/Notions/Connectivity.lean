import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.Loop
import Seymour.Matroid.Notions.Coloop


variable {α : Type}

/-- Connectivity relation, aka ξ in Oxley's book -/
def Matroid.ConnectivityRelation {α : Type} (M : Matroid α) (e f : α) : Prop :=
  e = f ∨ ∃ C, C ⊆ M.E ∧ M.Circuit C ∧ e ∈ C ∧ f ∈ C

/-- Connectivity relation is an equivalence relation on M.E -/
lemma Matroid.connectivityRelation_is_equiv_rel {α : Type} (M : Matroid α) :
    ∀ e f : α, M.ConnectivityRelation e f → M.ConnectivityRelation f e := by
  intro e f hef
  cases hef with
  | inl hef => exact Or.inl hef.symm
  | inr hef =>
    right
    obtain ⟨C, _, _, _, _⟩ := hef
    use C

/-- Component is an equivalence class under the connectivity relation, i.e., a ξ-equivalence class -/
def Matroid.Component {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f ↔ f ∈ X

/-- Separator is a union of components -/
def Matroid.Separator {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f → f ∈ X

/-- Every component is a separator -/
lemma Matroid.separator_component {α : Type} (M : Matroid α) {X : Set α} (hX : M.Component X) :
    M.Separator X :=
  fun e he f hf hef => (hX e he f hf).→ hef

/-- Every loop is a separator -/
lemma Matroid.separator_loop {α : Type} {M : Matroid α} {x : α} (hx : M.Loop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
    obtain ⟨C, hCE, circC, heC, hfC⟩ := hfC
    rw [hex, ←Set.singleton_subset_iff] at heC
    rw [Matroid.loop_iff_circuit] at hx
    apply Matroid.Circuit.not_ssubset_circuit hx at circC
    rw [Set.ssubset_def] at circC
    push_neg at circC
    exact circC heC hfC

/-- Every coloop is a separator -/
lemma Matroid.separator_coloop {α : Type} {M : Matroid α} {x : α} (hx : M.Coloop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
    rw [Matroid.coloop_iff_in_no_circuit] at hx
    obtain ⟨_hxE, hxC⟩ := hx
    obtain ⟨C, _hCE, hCcirc, heC, hfC⟩ := hfC
    rw [hex, ←Set.singleton_subset_iff] at heC
    specialize hxC C hCcirc
    tauto

/-- Every singleton separator is a loop or a coloop -/
lemma Matroid.singleton_separator_loop_coloop {α : Type} {M : Matroid α} {x : α} (hx : x ∈ M.E) :
    M.Separator {x} → M.Loop x ∨ M.Coloop x := by
  intro sep_x
  by_contra! contr
  obtain ⟨notLoop, notColoop⟩ := contr
  rw [Matroid.loop_iff_circuit] at notLoop
  rw [Matroid.coloop_iff_in_no_circuit] at notColoop
  push_neg at notColoop
  specialize notColoop hx
  obtain ⟨C, hC, hxC⟩ := notColoop
  obtain ⟨f, hfC, hfx⟩ : ∃ f ∈ C, f ≠ x
  · by_contra! hf
    have hCx : ∀ f ∈ C, f ∈ ({x} : Set α)
    · by_contra! hg
      obtain ⟨f', hf'⟩ := hg
      exact (hf f' hf'.left ▸ hf'.right) rfl
    have x_sub_C : {x} ⊆ C := Set.singleton_subset_iff.← hxC
    have hCeqx : {x} = C := x_sub_C.antisymm hf
    rw [hCeqx] at notLoop
    exact notLoop hC
  have hCE := hC.subset_ground
  exact hfx (sep_x x rfl f (hCE hfC) (Or.inr ⟨C, hCE, hC, hxC, hfC⟩))

/-- Singleton element is a separator iff it is a loop or a coloop -/
lemma Matroid.singleton_separator_iff {α : Type} {M : Matroid α} (x : α) :
    x ∈ M.E ∧ M.Separator {x} ↔ M.Loop x ∨ M.Coloop x := by
  constructor
  · intro hxE
    exact M.singleton_separator_loop_coloop hxE.left hxE.right
  · intro hxx
    cases hxx with
    | inl xLoop => exact ⟨xLoop.left, Matroid.separator_loop xLoop⟩
    | inr xColoop => exact ⟨xColoop.left, Matroid.separator_coloop xColoop⟩
