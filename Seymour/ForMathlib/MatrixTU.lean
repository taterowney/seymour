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

set_option maxHeartbeats 1200000 in
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
  then -- square case
    -- bijections between indexing types of equal cardinalities
    let e₁ : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≃ { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } :=
      Fintype.equivOfCardEq hxy.1
    let e₂ : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } ≃ { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } :=
      Fintype.equivOfCardEq hxy.2
    -- relating submatrices in blocks to submatrices of `A₁` and `A₂`
    have hAfg :
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
      -- `X₁' = { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ part of { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }`
      -- of the same cardinality as `{ y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }`
      -- then the bottom left blocks will be all `0`s, hence we can multiply the two determinants, and the top left block will
      -- have at least one row made of `0`s, hence its determinant is `0`
      have hY₁ : Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ≤
          Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } + Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }
      · sorry -- RHS is `k`
      obtain ⟨X', hX'⟩ := llll hxy₁ hY₁
      let e₁ := Fintype.equivOfCardEq hX'
      have hY₂ : Fintype.card { y // y ∉ X' } = Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
      · sorry -- kinda complement to `hY₁'`
      let e₂ := Fintype.equivOfCardEq hY₂
      have hAfg' :
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
          ) 0 0
          (A₂.submatrix
            ((·.val.snd) : { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } → X₂)
            ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
          )
        ) =
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
          ) 0 0
          (A₂.submatrix
            ((·.casesOn (·.val.val.snd) (·.val.val.snd)) : { x₁ // x₁ ∈ X' } ⊕ { x₂ // x₂ ∉ X' } → X₂)
            ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
          )
        ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
      · ext i j
        cases hi : i <;> cases hj : j <;> simp -- TODO refactor
        rename_i i' j'
        if hi' : i' ∈ X' then
          simp only [hi', Set.mem_range, ne_eq, Equiv.sumCompl_apply_symm_of_pos]
        else
          simp only [hi', Set.mem_range, ne_eq, Equiv.sumCompl_apply_symm_of_neg, not_false_eq_true]
      rw [hAfg', ←abs_eq_zero]
      have hAfg'' :
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
          ) 0 0
          (A₂.submatrix
            ((·.casesOn (·.val.val.snd) (·.val.val.snd)) : { x₁ // x₁ ∈ X' } ⊕ { x₂ // x₂ ∉ X' } → X₂)
            ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
          )
        ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
        =
        (fromBlocks
          ((fromRows A₁ 0).submatrix
            ((·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·)) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X' → X₁ ⊕ X')
            ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
          )
          ((fromRows 0 A₂).submatrix
            (·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·.val.val.snd))
            ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
          )
          0
          (A₂.submatrix
            ((·.val.val.snd) : { x₂ // x₂ ∉ X' } → X₂)
            ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
          )
        ).submatrix ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm (Equiv.refl _)
      · sorry
      rw [hAfg'']
      have hAfg''' :
        (
          (fromBlocks
            ((fromRows A₁ 0).submatrix
              ((·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·)) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X' → X₁ ⊕ X')
              ((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁)
            )
            ((fromRows 0 A₂).submatrix
              (·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·.val.val.snd))
              ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
            )
            0
            (A₂.submatrix
              ((·.val.val.snd) : { x₂ // x₂ ∉ X' } → X₂)
              ((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂)
            )
          ).submatrix ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm (Equiv.refl _)
        ).submatrix f.decomposeSum g.decomposeSum
        =
        (
          (fromBlocks
            ((fromRows A₁ 0).submatrix
              ((·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·)) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X' → X₁ ⊕ X')
              (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
            )
            ((fromRows 0 A₂).submatrix
              (·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·.val.val.snd))
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
            0
            (A₂.submatrix
              ((·.val.val.snd) : { x₂ // x₂ ∉ X' } → X₂)
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
          ).submatrix ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm (Equiv.refl _)
        ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
      · sorry
      rw [hAfg''']
      have hAfg'''' :
        (
          (fromBlocks
            ((fromRows A₁ 0).submatrix
              ((·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·)) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X' → X₁ ⊕ X')
              (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
            )
            ((fromRows 0 A₂).submatrix
              (·.casesOn (Sum.inl ·.val.snd) (Sum.inr ·.val.val.snd))
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
            0
            (A₂.submatrix
              ((·.val.val.snd) : { x₂ // x₂ ∉ X' } → X₂)
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
          ).submatrix ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm (Equiv.refl _)
        ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
        =
        (
          (fromBlocks
            (A₁.submatrix
              ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
              (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
            ) 0 0
            ((fromRows 0 A₂).submatrix
              ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
          ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
        ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
      · sorry
      rw [hAfg'''']
      have hAfg''''' :
        (
          (fromBlocks
            (A₁.submatrix
              ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
              (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
            ) 0 0
            ((fromRows 0 A₂).submatrix
              ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
          ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
        ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
        =
        (
          (
            (fromBlocks
              (A₁.submatrix
                ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
                (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
              ) 0 0
              ((fromRows 0 A₂).submatrix
                ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
                (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
              )
            ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
          ).submatrix
            (Equiv.refl _)
            ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _).symm).trans (Equiv.sumAssoc ..).symm :
                { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
                  (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
        ).submatrix
          f.decomposeSum
          ((g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm)).trans
            ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))))
      · sorry
      rw [hAfg''''', Matrix.abs_det_submatrix_equiv_equiv] -- , Matrix.det_fromBlocks_zero₂₁
      have hAfg'''''' :
        (
          (fromBlocks
            (A₁.submatrix
              ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
              (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
            ) 0 0
            ((fromRows 0 A₂).submatrix
              ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
              (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
            )
          ).submatrix (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm (Equiv.refl _)
        ).submatrix
          (Equiv.refl _)
          ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _).symm).trans (Equiv.sumAssoc ..).symm :
              { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
                (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
        =
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
          ) 0 0
          ((fromRows 0 A₂).submatrix
            ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
            (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
          )
        ).submatrix
          (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm
          ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _).symm).trans (Equiv.sumAssoc ..).symm :
            { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
              (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
      · sorry
      rw [hAfg'''''']
      have hAfg''''''' :
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
          ) 0 0
          ((fromRows 0 A₂).submatrix
            ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
            (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
          )
        ).submatrix
          (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm
          ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _).symm).trans (Equiv.sumAssoc ..).symm :
            { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
              (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
        =
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
          ) 0 0
          ((fromRows 0 A₂).submatrix
            ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
            (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
          )
        ).submatrix
          (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm
          (((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm :
            { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
              (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
      · sorry
      rw [hAfg''''''']
      have hAfg'''''''' :
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
          ) 0 0
          ((fromRows 0 A₂).submatrix
            ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
            (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
          )
        ).submatrix
          (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm
          (((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm :
            { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd } →
              (({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x // x ∈ X' }) ⊕ { x // x ∉ X' }))
        =
        (fromBlocks
          (A₁.submatrix
            ((·.val.snd) : { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } → X₁)
            (((·.val.snd) : { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } → Y₁) ∘ e₁)
          ) 0 0
          ((fromRows 0 A₂).submatrix
            ((·.casesOn (Sum.inl ·) (Sum.inr ·.val.val.snd)) : X' ⊕ { x₂ // x₂ ∉ X' } → X' ⊕ X₂)
            (((·.val.snd) : { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd } → Y₂) ∘ e₂)
          )
        ).submatrix
          ((Equiv.refl _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _)).symm)
          ((Equiv.sumAssoc ..).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl _))).symm
      · sorry
      rw [hAfg'''''''']
      sorry
    else
      sorry -- both inequalities are opposite (and strict) here
