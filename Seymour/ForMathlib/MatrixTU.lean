import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.ForMathlib.Basic
import Seymour.ForMathlib.FunctionDecompose


variable {R X₁ Y₁ X₂ Y₂ : Type*}

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

variable [LinearOrderedCommRing R]
  [Fintype X₁] [DecidableEq X₁] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype X₂] [DecidableEq X₂] [Fintype Y₂] [DecidableEq Y₂]

--set_option maxHeartbeats 205000 in
lemma Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_isTotallyUnimodular_of_card_le
    {A₁ : Matrix X₁ Y₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix X₂ Y₂ R} (hA₂ : A₂.IsTotallyUnimodular)
    {k : ℕ} {f : Fin k → X₁ ⊕ X₂} {g : Fin k → Y₁ ⊕ Y₂}
    (hkfg :
      Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≤
      Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }) :
    ((fromBlocks A₁ 0 0 A₂).submatrix f g).det ∈
      Set.range SignType.cast := by
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
    rw [hAfg,
    -- absolute value of determinant was preserved by previous mappings,
      in_set_range_singType_cast_iff_abs, Matrix.abs_det_submatrix_equiv_equiv,
    -- we now express it as a product of determinants of submatrices in blocks
      Matrix.det_fromBlocks_zero₁₂, ←in_set_range_singType_cast_iff_abs]
    -- determinants of submatrices in blocks are `∈ Set.range SignType.cast` by TUness of `A₁` and `A₂`
    apply in_set_range_singType_cast_mul_in_set_range_singType_cast
    · apply hA₁
    · apply hA₂
  else -- the submatrix of `A₁` or the submatrix of `A₂` is non-square (in fact, both)
    convert zero_in_set_range_singType_cast
    have hxy₁ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } <
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }
    · rw [not_and_or] at hxy
      have hk₁ := Fintype.card_fin k ▸ Fintype.card_congr f.decomposeSum
      have hk₂ := Fintype.card_fin k ▸ Fintype.card_congr g.decomposeSum
      rw [Fintype.card_sum] at hk₁ hk₂
      cases hxy <;> omega
      -- we need new indexing type
      -- `X' = { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ part of { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }`
      -- of the same cardinality as `{ y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }`
      -- then the bottom left blocks will be all `0`s, hence we can multiply the two determinants, and the top left block will
      -- have at least one row made of `0`s, hence its determinant is `0`
    have hkY₁ :
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ≤
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } +
        Fintype.card { x₂ : Fin k × X₂ // f x₂.fst = Sum.inr x₂.snd }
    · convert_to Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } ≤ Fintype.card (Fin k)
      · rw [←Fintype.card_sum]
        exact Fintype.card_congr f.decomposeSum.symm
      apply Fintype.card_le_of_embedding
      use (·.val.fst)
      intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ _
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      simp_all only [Sum.inl.injEq]
    obtain ⟨X', hX', hY₁⟩ := finset_of_cardinality_between hxy₁ hkY₁
    let e₁ := Fintype.equivOfCardEq hX'
    have hY₂ : Fintype.card { y // y ∉ X' } = Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
    · suffices :
          Fintype.card { y // y ∉ X' } + Fintype.card ({ x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ X') =
          Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd } +
          Fintype.card { y₂ : Fin k × Y₂ // g y₂.fst = Sum.inr y₂.snd }
      · omega
      convert Eq.refl (Fintype.card (Fin k))
      · rw [Fintype.card_sum, add_comm, add_assoc, ←Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl (· ∈ X')),
            ←Fintype.card_sum]
        exact Fintype.card_congr f.decomposeSum.symm
      · rw [←Fintype.card_sum]
        exact Fintype.card_congr g.decomposeSum.symm
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
      ).submatrix f.decomposeSum g.decomposeSum
      =
      (fromBlocks
        (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0)
        (fromRows 0 (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)))
        0
        (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂))
      ).submatrix
        ((f.decomposeSum.trans ((Equiv.refl _).sumCongr e')).trans e₀)
        (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
    · ext
      simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
        Matrix.submatrix, Matrix.of_apply, e₀, e']
      split
      · split <;> simp [Equiv.sumCompl, Equiv.sumAssoc, Matrix.fromBlocks, Matrix.fromRows]
      · split <;>
          simp only [Matrix.fromBlocks, Matrix.fromRows, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr,
            Equiv.sumAssoc, Equiv.sumCompl, Equiv.coe_fn_symm_mk, Set.mem_range, Matrix.zero_apply] <;> split <;>
          simp
    rw [hAfg', ←abs_eq_zero, Matrix.abs_det_submatrix_equiv_equiv, abs_eq_zero]
    convert_to
      (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0).det * (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)).det
        = 0
    · convert Matrix.det_fromBlocks_zero₂₁
        (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0)
        (fromRows 0 (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)))
        (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂))
    convert zero_mul _
    apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr (Classical.choice hY₁))
    intro
    rfl

lemma Matrix.fromBlocks_isTotallyUnimodular {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular :=
  fun k f g _ _ =>
    if hxy₀ :
        Fintype.card { x₁ : Fin k × X₁ // f x₁.fst = Sum.inl x₁.snd } ≤
        Fintype.card { y₁ : Fin k × Y₁ // g y₁.fst = Sum.inl y₁.snd }
    then
      Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_isTotallyUnimodular_of_card_le hA₁ hA₂ hxy₀
    else by
      rw [←Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
      apply Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_isTotallyUnimodular_of_card_le
      · rwa [←Matrix.transpose_isTotallyUnimodular_iff] at hA₁
      · rwa [←Matrix.transpose_isTotallyUnimodular_iff] at hA₂
      omega

#print axioms Matrix.fromBlocks_isTotallyUnimodular
