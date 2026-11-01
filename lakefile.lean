import Lake
open Lake DSL

package «prove2me» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @
  "3d425859e73fcfbef85b9638c2a91708ef4a22d4"

lean_lib «Definitions»
lean_lib «Theorems»
@[default_target]
lean_lib «Solutions»
