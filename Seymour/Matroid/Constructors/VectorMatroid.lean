import Mathlib.Data.Matroid.IndepAxioms
import Seymour.Basic


/-- Vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (α R : Type) [Ring R] where
  X : Type -- row index set
  E : Set α -- column index set
  A : Matrix X E R -- matrix defining a vector matroid
  -- note: in principle, rows can be indexed by any type, not necessarily `Set α`
  -- however, `Set α` is sufficient to get all vector matroids

variable {α R : Type} [Ring R]

/-- Vector matroid corresponding to matrix `A`. -/
def Matrix.VectorMatroid {X : Type} {E : Set α} (A : Matrix X E R) : VectorMatroid α R :=
  ⟨X, E, A⟩

/-- todo: desc -/
def Matrix.IndepCols {X : Type} {E : Set α} (A : Matrix X E R) (S : Set α) : Prop :=
  ∃ hS : S ⊆ E, LinearIndependent R (A.submatrix id hS.elem).transpose

/-- A set `S` is independent in `M[A]` iff `S` is a subset of linearly independent columns in `A`. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (S : Set α) : Prop :=
  ∃ hS : S ⊆ M.E, LinearIndependent R (M.A.submatrix id hS.elem).transpose

/-- Empty set is independent. -/
theorem VectorMatroid.IndepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ := by
  use Set.empty_subset M.E
  exact linearIndependent_empty_type

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.IndepCols_subset (M : VectorMatroid α R)
    (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) : M.IndepCols I := by
  obtain ⟨hJ, hM⟩ := hMJ
  use hIJ.trans hJ
  show LinearIndependent R (fun i j => M.A j (hJ.elem (Subtype.map id hIJ i)))
  apply hM.comp
  intro _ _ hf
  apply Subtype.eq
  simpa [Subtype.map] using hf

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.IndepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  sorry

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.IndepCols_maximal (M : VectorMatroid α R) (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols S := by
  sorry

/-- Vector matroid expressed as `IndepMatroid`. -/
def VectorMatroid.IndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.E
  Indep := M.IndepCols
  indep_empty := M.IndepCols_empty
  indep_subset := M.IndepCols_subset
  indep_aug := M.IndepCols_aug
  indep_maximal S _ := M.IndepCols_maximal S
  subset_ground _ := fun ⟨h, _⟩ => h

/-- Vector matroid converted to `Matroid`. -/
def VectorMatroid.matroid (M : VectorMatroid α R) : Matroid α :=
  M.IndepMatroid.matroid

@[simp]
lemma VectorMatroid.E_eq (M : VectorMatroid α R) : M.matroid.E = M.E :=
  rfl

@[simp]
lemma VectorMatroid.indep_eq (M : VectorMatroid α R) : M.matroid.Indep = M.IndepCols :=
  rfl


-- todo: section 6.3 from Oxley: Different matroid representations
