import Lake

open System Lake DSL

package «Fast-ML-FE2» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions :=
  #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.28.0"
require repl from git "https://github.com/leanprover-community/repl.git"@"v4.28.0"

@[default_target] lean_lib FastMLFE2
