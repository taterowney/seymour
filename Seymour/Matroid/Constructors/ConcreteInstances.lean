import Seymour.Matroid.Classes.Binary
import Seymour.Matroid.Classes.Regular

-- TODO construct directly via `VectorMatroid Z2`
noncomputable def MatroidR10 : StandardRepr (Fin 10) Z2 where
  X := (·.val < 5)
  Y := (·.val ≥ 5)
  decmemX _ := Classical.propDecidable _
  decmemY _ := Classical.propDecidable _
  hXY := by
    rw [Set.disjoint_left]
    intro _ hX hY
    rw [Set.mem_def] at hX hY
    omega
  B := !![1, 0, 0, 1, 1; 1, 1, 0, 0, 1; 0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 1, 1, 1, 1, 1].submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩)
  inh := by
    use 0
    show 0 < 5
    decide

-- todo: lemma MatroidR10.IsRegular
