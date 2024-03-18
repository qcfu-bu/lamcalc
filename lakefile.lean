import Lake
open Lake DSL

package «lamcalc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «Lamcalc» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
