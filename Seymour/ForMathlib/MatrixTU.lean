import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.ForMathlib.FunctionDecompose

-- TODO name and home
lemma llll {α β : Type*} [Fintype α] [Fintype β] {n : ℕ} (_ : Fintype.card α < n) (_ : n ≤ Fintype.card α + Fintype.card β) :
    ∃ b : Finset β, Fintype.card (α ⊕ b) = n := by
  have beta' : n - Fintype.card α ≤ Fintype.card β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - Fintype.card α :=
    (Finset.exists_subset_card_eq beta').imp (by simp)
  use s
  rw [Fintype.card_sum, Fintype.card_coe, hs]
  omega


variable {R : Type*}

lemma zero_in_set_range_singType_cast [LinearOrderedRing R] : (0 : R) ∈ Set.range SignType.cast :=
  ⟨0, rfl⟩

lemma in_set_range_singType_cast_mul_in_set_range_singType_cast [LinearOrderedRing R] {a b : R}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  sorry

lemma in_set_range_singType_cast_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ Set.range SignType.cast ↔ |a| ∈ Set.range SignType.cast := by
  sorry

variable {X₁ X₂ Y₁ Y₂ : Type*}

lemma Matrix.fromBlocks_submatrix [Zero R] (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R)
    {α : Type*} (f : α → X₁ ⊕ X₂) (g : α → Y₁ ⊕ Y₂) :
    (fromBlocks A₁ 0 0 A₂).submatrix f g =
    (fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : α × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
        ((·.val.snd) : { y₁ : α × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : α × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂)
        ((·.val.snd) : { y₂ : α × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
      )
    ).submatrix f.decomposeSum g.decomposeSum := by
  rw [
    f.eq_comp_decomposeSum,
    g.eq_comp_decomposeSum,
    ←Matrix.submatrix_submatrix]
  aesop

lemma Matrix.IsTotallyUnimodular.comp_rows [CommRing R] {A : Matrix X₁ Y₁ R}
    (hA : A.IsTotallyUnimodular) (e : X₂ → X₁) :
    Matrix.IsTotallyUnimodular (A ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  exact hA k (e ∘ f) g

lemma Matrix.IsTotallyUnimodular.comp_cols [CommRing R] {A : Matrix X₁ Y₁ R}
    (hA : A.IsTotallyUnimodular) (e : Y₂ → Y₁) :
    Matrix.IsTotallyUnimodular (A · ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  exact hA k f (e ∘ g)

--set_option maxHeartbeats 1200000 in
lemma Matrix.fromBlocks_isTotallyUnimodular [LinearOrderedCommRing R]
    [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
    {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R} (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  -- different proof strategy attempted: https://github.com/madvorak/matrix-tu-experimental/blob/main/MatrixTuExperimental.lean
  intro k f g hf hg
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hA₁ hA₂
  rw [Matrix.fromBlocks_submatrix]
  -- look at sizes of submatrices in blocks
  if hxy : Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd }
         = Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }
         ∧ Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }
         = Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
  then -- the square case
    -- bijections between indexing types of equal cardinalities
    let e₁ : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≃ { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } :=
      Fintype.equivOfCardEq hxy.1
    let e₂ : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } ≃ { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } :=
      Fintype.equivOfCardEq hxy.2
/-
    ` f :  [k] -> X₁ ⊕ X₂ `
    ` g :  [k] -> Y₁ ⊕ Y₂ `

    ` f₁ :  ₖX₁ -> X₁ `
    ` f₂ :  ₖX₂ -> X₂ `
    ` g₁ :  ₖY₁ -> Y₁ `
    ` g₂ :  ₖY₂ -> Y₂ `

    ` ₖX₁ ⊕ ₖX₂ = [k] = ₖY₁ ⊕ ₖY₂ `

    ` e₁ :  ₖX₁ ≃ ₖY₁ `
    ` e₂ :  ₖX₂ ≃ ₖY₂ `

    ` g₁ ∘ e₁ :  ₖX₁ -> Y₁ `
    ` g₂ ∘ e₂ :  ₖX₂ -> Y₂ `

    ` (g₁ ∘ e₁) | (g₂ ∘ e₂) :  [k] -> Y₁ ⊕ Y₂ `   (same type as `f` is)
-/
    have hAfg : -- relating submatrices in blocks to submatrices of `A₁` and `A₂`
      (fromBlocks
        (A₁.submatrix
          ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
          ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
        ) 0 0
        (A₂.submatrix
          ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂)
          ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
        )
      ).submatrix f.decomposeSum g.decomposeSum
      =
      (fromBlocks
        (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0 0
        (A₂.submatrix (·.val.snd) ((·.val.snd) ∘ e₂))
      ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
    · ext
      simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
        Matrix.submatrix, Matrix.of_apply]
      split <;> split <;> simp
    -- absolute value of determinant was preserved by previous mappings,
    -- and we now express it as a product of determinants of submatrices in blocks
    rw [hAfg, in_set_range_singType_cast_iff_abs, Matrix.abs_det_submatrix_equiv_equiv, Matrix.det_fromBlocks_zero₁₂,
      ←in_set_range_singType_cast_iff_abs]
    -- determinants of submatrices in blocks are `0` or `±1` by TUness of `A₁` and `A₂`
    apply in_set_range_singType_cast_mul_in_set_range_singType_cast
    · apply hA₁
    · apply hA₂
  else -- the submatrix of `A₁` or the submatrix of `A₂` is non-square
    -- actually both submatrices are non-square
    obtain ⟨cardine₁, cardine₂⟩ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≠
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ∧
        Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } ≠
        Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
    · rw [not_and_or] at hxy
      have hk₁ := Fintype.card_fin k ▸ Fintype.card_congr f.decomposeSum
      have hk₂ := Fintype.card_fin k ▸ Fintype.card_congr g.decomposeSum
      rw [Fintype.card_sum] at hk₁ hk₂
      cases hxy <;> omega
    clear hxy
    convert zero_in_set_range_singType_cast
    if hxy₁ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } <
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } then
      -- we need new indexing type
      -- `X' = { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ part of { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }`
      -- of the same cardinality as `{ y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }`
      -- then the bottom left blocks will be all `0`s, hence we can multiply the two determinants, and the top left block will
      -- have at least one row made of `0`s, hence its determinant is `0`
      have hY₁ : Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ≤
          Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } + Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }
      · sorry -- RHS is `k`
      obtain ⟨X', hX'⟩ := llll hxy₁ hY₁
      let e₁ := Fintype.equivOfCardEq hX'
      have hY₂ : Fintype.card { y // y ∉ X' } = Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
      · sorry -- kinda complement to `hX'`
      let e₂ := Fintype.equivOfCardEq hY₂
      let e₀ :
          { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ (X' ⊕ { x // x ∉ X' }) ≃
          ({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X') ⊕ { x // x ∉ X' } :=
        (Equiv.sumAssoc ..).symm
      let e' : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } ≃ X' ⊕ { x // x ∉ X' } :=
        (Equiv.sumCompl (· ∈ X')).symm
/-
    ` f :  [k] -> X₁ ⊕ X₂ `
    ` g :  [k] -> Y₁ ⊕ Y₂ `

    ` f₁ :  ₖX₁ -> X₁ `
    ` f₂ :  ₖX₂ -> X₂ `
    ` g₁ :  ₖY₁ -> Y₁ `
    ` g₂ :  ₖY₂ -> Y₂ `

    ` ₖX₁ ⊕ ₖX₂ = [k] = ₖY₁ ⊕ ₖY₂ `

    Here we have ` |ₖX₁| < |ₖY₁| ` and so ` |ₖX₂| > |ₖY₂| `

    We choose X' so that ` |ₖX₁ ⊕ X'| = |ₖY₁| `(hX') and therefore ` |ₖX₂ \ X'| = |ₖY₂| `(hY₂)

    ` e₁ :  ₖX₁ ⊕ X' ≃ ₖY₁ `
    ` e₂ :  ₖX₂ \ X' ≃ ₖY₂ `

    ` e₀ :  ₖX₁ ⊕ (X' ⊕ (ₖX₂ \ X')) ≃ (ₖX₁ ⊕ X') ⊕ (ₖX₂ \ X') `

    ` e' :  ₖX₂ ≃ X' ⊕ (ₖX₂ \ X') `

    ` I | e' :  ₖX₁ ⊕ ₖX₂ ≃ ₖX₁ ⊕ (X' ⊕ (ₖX₂ \ X')) `

    ` e₀ ∘ (I | e') :  [k] ≃ (ₖX₁ ⊕ X') ⊕ (ₖX₂ \ X') `
-/
      let _e : Fin k ≃ ({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X') ⊕ { x // x ∉ X' } :=
        (f.decomposeSum.trans ((Equiv.refl _).sumCongr e')).trans e₀
      sorry
    else
      sorry -- both inequalities are opposite (and strict) here
