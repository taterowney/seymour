# Matroid Decomposition Theorem Verification

The goal of this project is to formally verify Seymour's decomposition theorem for regular matroids in Lean 4.

## Blueprint

- You can find the blueprint on the [GitHub Pages site](https://ivan-sergeyev.github.io/seymour/)
- Quick link to the [dependency graph](https://ivan-sergeyev.github.io/seymour/blueprint/dep_graph_document.html)
- Quick link to the [documentation](https://ivan-sergeyev.github.io/seymour/docs/Seymour/BinaryMatroid.html)

## References

- [K. Truemper – Matroid Decomposition](https://www2.math.ethz.ch/EMIS/monographs/md/)
- [J. Oxley – Matroid Theory](https://doi.org/10.1093/acprof:oso/9780198566946.001.0001)
- [J. Geelen, B. Gerards – Regular matroid decomposition via signed graphs](https://www.math.uwaterloo.ca/~jfgeelen/Publications/regular.pdf)
- S. R. Kingan - On Seymour's decomposition theorem ([arxiv](https://arxiv.org/abs/1403.7757), [paper](https://doi.org/10.1007/s00026-015-0261-1))
- H. Bruhn et al. - Axioms for infinite matroids ([arxiv](https://arxiv.org/abs/1003.3919), [paper](https://doi.org/10.1016/j.aim.2013.01.011))

## Used tools and projects

- Uses [LeanProject](https://github.com/pitmonticone/LeanProject) template
- Uses [Leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool
- Uses [doc-gen4](https://github.com/leanprover/doc-gen4) tool
- Imports [Mathlib](https://github.com/leanprover-community/mathlib4) library

## Code style

If you contribute to the project, do not worry about code style too much.
We will accept your PR regardless of style; Martin will eventually adjust it.
None of the style rules is enforced by a linter.
The guideline below is written primarily to assist you in reading the code.

### Lines

- Lines should not be longer than 128 characters (see the vertical ruler in VS Code).
- Starting a proof on a new line is recommended even in cases where the entire proof fits into the same line with the statement.
- Make 2 empty lines between imports and the content of the file.
- Make 1 empty line between declarations of any kind.
- Make 2 empty lines between the end of a section and what follows.
- Each file ends with a linebreak.

### Indentation

- We use the same indentation as Mathlib.
  - Subitem is indented by 2 spaces.
  - Continuation of the same item after a linebreak is 4 spaces.
- Orphaning parentheses is allowed.
- Deviations from the style are welcome if they hint some metaïnformation.

### Naming

- Use `camelCase` and `PascalCase` and `snake_case` the same way Mathlib uses them.
- Data variables (both in arguments and local variables) are always denoted by a single letter, possibly with other stuff after it like lower index or apostrophe.
- Prop variables (both in arguments and local variables) are always denoted by multiple letters, possibly with other stuff after them like lower index or apostrophe.
  - prefix `h` means "the statement is anything about the following variables"
  - absence of `h` means that the statement is spelled out, not only the variables that appear in it
  - writing names like `h₁` or `h'` or `this'` is strongly discouraged
- Never name anything `this` or standalone `h` (neither for data nor for propositions), but leaving automatically named stuff with `this` or `h` is encouraged if the term is not explicitly reffered to later.
- Examples:

  `intro a b a_lt_b hab`
  - `a` carries data (e.g. an integer)
  - `b` carries data (e.g. an integer)
  - `a_lt_b` carries a proof of `a < b`
  - `hab` carries any information about `a` and `b`

  `intro M hM hM'`
  - `M` carries data (e.g. a matroid)
  - `hM` carries any information about `M`
  - `hM'` carries another information about `M`

  `intro M M' hM hM'`
  - `M` carries data (e.g. a matroid)
  - `M'` carries data (e.g. a matroid)
  - `hM` carries any information about `M`
  - `hM'` carries any information about `M'`

  `intro M₁ M₂ hM₁ hM₂ hMM`
  - `M₁` carries data (e.g. a matroid)
  - `M₂` carries data (e.g. a matroid)
  - `hM₁` carries any information about `M₁`
  - `hM₂` carries any information about `M₂`
  - `hMM` carries any information about both `M₁` and `M₂` (indices after `hMM` are not needed)

  `intro x y x_eq_y h1 h1'`
  - `x` carries data (e.g. an integer)
  - `y` carries data (e.g. an integer)
  - `x_eq_y` carries a proof of `x = y`
  - `h1` carries any information involving the number `1`
  - `h1'` carries another information involving the number `1`

### Global variables

- Only implicit and typeclass arguments may be put into `variable`, never explicit arguments. Example and a non-example:
  
  `variable {R : Type} [R : Ring] (a : R)`

  While `{R : Type} [R : Ring]` in encouraged, the last one `(a : R)` is not allowed.
  This way, when you call a function or lemma, you can be sure that all required arguments are visible at the lines of given function or lemma.
- We use global variables sparingly — only for arguments that are used by the entire file or section.

### Spaces with brackets

- There is always a space before a bracket (of any kind) opens and after it closes. Example:
  
  `foo {R : Type} [R : Ring] (a b : R) : ⟨a, b⟩ ∈ S`
- Space after a brace opens and before a brace closes is written only in the set builder and in `Subtype` declaration. Examples:
  
  `{ x : X | Foo x }`

  `{ x₁ : α × β₁ // f x₁.fst = Sum.inl x₁.snd }`
