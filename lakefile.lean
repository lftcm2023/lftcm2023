import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package lftcm2023 where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib LftCM where
  moreLeanArgs := moreLeanArgs

@[default_target]
lean_lib Projects where
  moreLeanArgs := moreLeanArgs

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"3f9dee6"
