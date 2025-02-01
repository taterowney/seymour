import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.Loop
import Seymour.Matroid.Notions.Coloop


variable {α : Type}

section SimpleConnectivity

/-- The connectivity relation, aka ξ in Oxley's book -/
def Matroid.ConnectivityRelation (M : Matroid α) (e f : α) : Prop :=
  e = f ∨ ∃ C : Set α, C ⊆ M.E ∧ M.Circuit C ∧ e ∈ C ∧ f ∈ C

/-- The connectivity relation is reflexive -/
@[refl]
lemma Matroid.ConnectivityRelation.refl (M : Matroid α) {e : α} :
    M.ConnectivityRelation e e :=
  Or.inl rfl

/-- The connectivity relation is symmetric -/
@[symm]
lemma Matroid.ConnectivityRelation.symm (M : Matroid α) {e f : α} :
    M.ConnectivityRelation e f → M.ConnectivityRelation f e := by
  intro hef
  cases hef with
  | inl hef => exact Or.inl hef.symm
  | inr hef =>
    right
    obtain ⟨C, _, _, _, _⟩ := hef
    use C

/-- The connectivity relation is transitive -/
@[trans]
lemma Matroid.ConnectivityRelation.trans (M : Matroid α) {e f g : α} :
    M.ConnectivityRelation e f → M.ConnectivityRelation f g → M.ConnectivityRelation e g := by
  intro hef hfg
  cases hef with
  | inl hef => exact hef ▸ hfg
  | inr hef =>
    cases hfg with
    | inl hfg => exact Or.inr (hfg ▸ hef)
    | inr hfg =>
      obtain ⟨C₁, hC₁, hMC₁, heC₁, hfC₁⟩ := hef
      obtain ⟨C₂, hC₂, hMC₂, hfC₂, hgC₂⟩ := hfg
      right
      -- todo: see proof of Lemma 7 in Bruhn Wollman 2011 (page 5)
      -- note: that proof uses matroid contraction
      sorry

/-- A component is an equivalence class under the connectivity relation, i.e., a ξ-equivalence class -/
def Matroid.Component (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f ↔ f ∈ X

/-- A separator is a union of components -/
def Matroid.Separator (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f → f ∈ X

/-- Every component is a separator -/
lemma Matroid.separator_component (M : Matroid α) {X : Set α} (hX : M.Component X) :
    M.Separator X :=
  fun e he f hf hef => (hX e he f hf).→ hef

/-- Every loop is a separator -/
lemma Matroid.separator_loop {M : Matroid α} {x : α} (hx : M.Loop x) :
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
lemma Matroid.separator_coloop {M : Matroid α} {x : α} (hx : M.Coloop x) :
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
lemma Matroid.singleton_separator_loop_coloop {M : Matroid α} {x : α} (hx : x ∈ M.E) :
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
lemma Matroid.singleton_separator_iff {M : Matroid α} (x : α) :
    x ∈ M.E ∧ M.Separator {x} ↔ M.Loop x ∨ M.Coloop x := by
  constructor
  · intro hxE
    exact M.singleton_separator_loop_coloop hxE.left hxE.right
  · intro hxx
    cases hxx with
    | inl xLoop => exact ⟨xLoop.left, Matroid.separator_loop xLoop⟩
    | inr xColoop => exact ⟨xColoop.left, Matroid.separator_coloop xColoop⟩

end SimpleConnectivity


section FiniteConnectivity

def Matroid.finiteConnectivity {M : Matroid α} (hM : M.Finite) {X : Set α} (hX : X ⊆ M.E) : ℕ :=
  sorry -- todo: r(X) + r(E - X) - r(M), see Oxley

end FiniteConnectivity


section InfiniteConnectivity

lemma bruhn_wollan_14_a {M : Matroid α} {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J) :
    ∀ F₁ ⊆ I ∪ J, ∀ F₂ ⊆ I ∪ J, M.Base ((I ∪ J) \ F₁) → M.Base ((I ∪ J) \ F₂) → F₁.encard = F₂.encard := by
  intro F₁ hF₁ F₂ hF₂ hMF₁ hMF₂ -- TODO why not arguments?
  sorry

def Matroid.delUnionIndep {M : Matroid α} {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J) : ℕ∞ :=
  sorry
  -- todo: min {|F| : F ⊆ I ∪ J, (I ∪ J) \ F ∈ I}, or ∞ if no such F exists, see Bruhn Wollan 2011

def Matroid.Connectivity' (M : Matroid α) {X : Set α} {B B' : Set α} (hB : M.Basis B X) (hB' : M.Basis B' (M.E \ X)) : ℕ∞ :=
  M.delUnionIndep hB.indep hB'.indep

def Matroid.connectivity (M : Matroid α) {X : Set α} : X ⊆ M.E → ℕ∞ :=
  sorry
  -- todo: choice of B and B' is arbitrary by Lemma 14 in Bruhn Wollan 2011

-- TODO rename
def Matroid.kSeparation (M : Matroid α) {X : Set α} (hX : X ⊆ M.E) (k : ℕ) : Prop :=
  M.connectivity hX < k ∧ X.encard ≥ k ∧ (M.E \ X).encard ≥ k

-- TODO rename
def Matroid.kConnected (M : Matroid α) (k : ℕ) : Prop :=
  ∀ X, ∃ hX : X ⊆ M.E, ∀ ℓ : ℕ, 1 < ℓ → ℓ < k → ¬(M.kSeparation hX ℓ)

end InfiniteConnectivity
