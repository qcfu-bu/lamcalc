import Lake
open Lake DSL

package «lamcalc» where
  -- add package configuration options here

@[default_target]
lean_lib «Lamcalc» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
