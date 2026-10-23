import Lake
open Lake DSL

package Lampe where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  moreLeanArgs := #["--tstack=65536", "-M4096"]
  testDriver := "Tests"

require "leanprover-community" / "batteries" @ git "v4.33.1"
require "leanprover-community" / "mathlib" @ git "v4.33.1"

@[default_target]
lean_lib Lampe where

lean_lib Tests where
    globs := #[.submodules `Tests]
