import Lake
open Lake DSL

package «desargues» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  moreLinkArgs := #[
  "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  "-lctranslate2"
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.5.1"

lean_lib «PV» where
lean_lib «Structure» where
lean_lib «Examples» where

@[default_target]
lean_lib «Basic» where
  -- add any library configuration options here
