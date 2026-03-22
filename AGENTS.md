# Repository Guidelines

## Project Goal
The long-term goal of this project is to formalize Germer et al.'s Fast Multi-Level Foreground Estimation in Lean 4 as a theory-first system for proof-directed optimal implementation derivation, not to preserve the current runtime/FFI stack as the architectural center.

Prioritize work that strengthens:

- the shallow mathematical core for the single-pixel local equation,
- the canonical Germer/PyMatting semantics where the paper and authored CPU/GPU implementations agree,
- the relational theorem layer for backend-specific divergences,
- the deep refinement layer that derives efficient CPU/GPU forms from proved equalities.

When a trade-off appears between preserving legacy executable behavior and improving the theory architecture, prefer the theory architecture unless the task explicitly says otherwise.

## Project Structure & Module Organization
`FastMLFE2/` holds the main Lean modules. The repository currently still contains older proof-oriented modules such as `MultilevelSpec.lean` and `LocalModel.lean`, along with legacy executable-reference paths exposed through `NativeFFI.lean` and `CLI.lean`. `FastMLFE2.lean` is the umbrella import. Top-level entrypoints `FFILeanSmoke.lean`, `FFICliSmoke.lean`, and `FastMLFECli.lean` build runnable executables. Native C++ FFI sources live in `native/`. During the refoundation, treat runtime/native code as legacy comparison artifacts rather than as the architectural source of truth.

## Build, Test, and Development Commands
Use Lake for all routine work:

- `lake build` builds the default Lean library and native FFI.
- `lake build fastmlfeCli` builds the CLI executable.
- `lake build ffiLeanSmoke ffiCliSmoke ffiSmoke ffiRunner` builds smoke-test binaries.
- `lake env lean FastMLFE2/CLI.lean` type-checks a single file inside the project environment.

This repository links against OpenCV through `pkg-config`, so ensure `opencv4` headers and libs are installed before building.

## Coding Style & Naming Conventions
Follow existing Lean 4 style: two-space indentation in pattern matches and record literals, `CamelCase` for structures and inductives, and `lowerCamelCase` for definitions and helper functions. Keep module names aligned with file names, for example `FastMLFE2/CLI.lean` defines `namespace FastMLFE2.CLI`. In C++, keep includes grouped at the top, prefer small helper functions in anonymous namespaces, and stay with the current standard library style.

## Testing Guidelines
There is no separate `tests/` directory yet. Treat smoke executables as regression checks for the FFI boundary and CLI path. Before opening a PR, run `lake build` and at least the target you changed; for FFI changes, also build `ffiSmoke` or `ffiRunner`. Add new smoke entrypoints at the repository root only when they exercise a distinct integration path.

## Commit & Pull Request Guidelines
Recent history uses short, imperative subjects, often with a prefix such as `refactor:`, `Add`, or `Remove`. Keep commit titles concise and scoped to one change. PRs should describe whether the change affects the proof-oriented `spec` layer, the executable `reference` layer, or both; list exact verification commands; and include sample CLI output or screenshots only when user-visible behavior changes.

## Configuration & Dependency Notes
Do not hardcode new system paths unless unavoidable; `lakefile.lean` already contains platform-specific linker assumptions. If you adjust native dependencies, document the required packages and verify both Lean and C++ targets still build.
