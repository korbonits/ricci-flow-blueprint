# Third-party code

`RicciFlowBlueprint/GramSchmidtOrtho.lean` and
`RicciFlowBlueprint/OrthonormalFrame.lean` are **not original to this project.**
They are ported from Mathlib pull request
[#26221](https://github.com/leanprover-community/mathlib4/pull/26221)
("Mr. Covariant Derivatives"), branch `grunweg/mathlib4:MR-covariant-derivatives`,
which is open and unmerged as of 2026-09-07.

Copyright (c) 2025 Michael Rothgang. Authors: Patrick Massot, Michael Rothgang.
Licensed under Apache License 2.0; the full text is in `LICENSE-Apache-2.0`.
The upstream copyright headers are retained in both files.

Changes made when porting:

* the Lean module system (`module`, `public import`, `@[expose] public section`)
  is not used in this project, so those constructs were removed;
* `Mathlib.Geometry.Manifold.VectorBundle.SmoothSection` is deprecated upstream
  and was replaced by `...VectorBundle.ContMDiffSection`;
* duplicate `[WellFoundedLT ι]` instance binders were dropped from
  `gramSchmidt` and `gramSchmidtNormed` (a linter that did not exist when the
  branch was written now rejects them);
* four proofs were repaired against six months of Mathlib drift
  (`gramSchmidt_zero`, an injectivity step, and two places where dot notation on
  `ContMDiffWithinAt` no longer resolves and the prefix form is needed);
* `contMDiffOn_iff_coeff'` was **removed**. Upstream marks it
  `-- unused, just stating for convenience/nice API` and leaves it `sorry`.
  Nothing this project uses depends on it, and this project admits no `sorry`.

**These files should be deleted the moment #26221, or a split-out of it,
lands in Mathlib.**
