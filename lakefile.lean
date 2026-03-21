import Lake

open System Lake DSL

def splitWhitespace (s : String) : Array String :=
  ((s.trimAscii.toString.splitOn " ").filter (· != "")).toArray

def pkgConfigArgs (args : Array String) : LogIO (Array String) := do
  let out ← IO.Process.output {
    cmd := "pkg-config"
    args := args
  }
  if out.exitCode ≠ 0 then
    error s!"pkg-config {" ".intercalate args.toList} failed:\n{out.stderr}"
  return splitWhitespace out.stdout

def leanIncludeArgs : LogIO (Array String) := do
  let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
  if out.exitCode ≠ 0 then
    error s!"lean --print-prefix failed:\n{out.stderr}"
  let leanPrefix := out.stdout.trimAscii.toString
  return #["-I", s!"{leanPrefix}/include"]

def buildFastMlfe2Ffi (pkg : Package) : FetchM (Job FilePath) := do
  let nativeDir := pkg.dir / "native"
  let cflags ← pkgConfigArgs #["--cflags", "opencv4"]
  let leanIncludes ← leanIncludeArgs
  let srcJob ← inputTextFile (nativeDir / "fastmlfe2_ffi.cpp")
  let leanSrcJob ← inputTextFile (nativeDir / "lean_fastmlfe2_ffi.cpp")
  let hdrJob ← inputTextFile (nativeDir / "fastmlfe2_ffi.h")
  let inputs := Job.collectArray #[srcJob, leanSrcJob, hdrJob]
  let objFile := pkg.buildDir / "ir" / "fastmlfe2_ffi.o"
  let objJob ← buildFileAfterDep objFile inputs fun _ =>
    compileO objFile (nativeDir / "fastmlfe2_ffi.cpp")
      (#["-std=c++17", "-fPIC"] ++ leanIncludes ++ cflags) "clang++"
  let leanObjFile := pkg.buildDir / "ir" / "lean_fastmlfe2_ffi.o"
  let leanObjJob ← buildFileAfterDep leanObjFile inputs fun _ =>
    compileO leanObjFile (nativeDir / "lean_fastmlfe2_ffi.cpp")
      (#["-std=c++17", "-fPIC"] ++ leanIncludes ++ cflags) "clang++"
  buildStaticLib (pkg.buildDir / "lib" / Lake.nameToStaticLib "fastmlfe2ffi") #[objJob, leanObjJob]

package «Fast-ML-FE2» where
  version := v!"0.1.0"
  keywords := #["math"]
  moreLinkArgs := #[
    "/usr/lib/gcc/x86_64-linux-gnu/13/libstdc++.so",
    "/usr/lib/x86_64-linux-gnu/libopencv_imgproc.so",
    "/usr/lib/x86_64-linux-gnu/libopencv_core.so"
  ]
  leanOptions :=
  #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.28.0"

extern_lib fastmlfe2ffi pkg := do
  buildFastMlfe2Ffi pkg

target ffiSmoke pkg : FilePath := do
  let nativeDir := pkg.dir / "native"
  let cflags ← pkgConfigArgs #["--cflags", "opencv4"]
  let libs ← pkgConfigArgs #["--libs", "opencv4"]
  let smokeSrcJob ← inputTextFile (nativeDir / "smoke.cpp")
  let hdrJob ← inputTextFile (nativeDir / "fastmlfe2_ffi.h")
  let libJob ← buildFastMlfe2Ffi pkg
  let smokeInputs := Job.collectArray #[smokeSrcJob, hdrJob]
  let smokeObj := pkg.buildDir / "ir" / "ffi_smoke.o"
  let smokeObjJob ← buildFileAfterDep smokeObj smokeInputs fun _ =>
    compileO smokeObj (nativeDir / "smoke.cpp")
      (#["-std=c++17", "-I", nativeDir.toString] ++ cflags) "clang++"
  let linkInputs := Job.collectArray #[smokeObjJob, libJob]
  buildFileAfterDep (pkg.binDir / "ffi-smoke") linkInputs fun deps =>
    compileExe (pkg.binDir / "ffi-smoke")
      (#[deps[0]!.toString, deps[1]!.toString] ++ libs) "clang++"

target ffiRunner pkg : FilePath := do
  let nativeDir := pkg.dir / "native"
  let cflags ← pkgConfigArgs #["--cflags", "opencv4"]
  let libs ← pkgConfigArgs #["--libs", "opencv4"]
  let runnerSrcJob ← inputTextFile (nativeDir / "runner.cpp")
  let hdrJob ← inputTextFile (nativeDir / "fastmlfe2_ffi.h")
  let libJob ← buildFastMlfe2Ffi pkg
  let runnerInputs := Job.collectArray #[runnerSrcJob, hdrJob]
  let runnerObj := pkg.buildDir / "ir" / "ffi_runner.o"
  let runnerObjJob ← buildFileAfterDep runnerObj runnerInputs fun _ =>
    compileO runnerObj (nativeDir / "runner.cpp")
      (#["-std=c++17", "-I", nativeDir.toString] ++ cflags) "clang++"
  let linkInputs := Job.collectArray #[runnerObjJob, libJob]
  buildFileAfterDep (pkg.binDir / "ffi-runner") linkInputs fun deps =>
    compileExe (pkg.binDir / "ffi-runner")
      (#[deps[0]!.toString, deps[1]!.toString] ++ libs) "clang++"

@[default_target] lean_lib FastMLFE2 where
  extraDepTargets := #[`fastmlfe2ffi]

lean_exe ffiLeanSmoke where
  root := `FFILeanSmoke
  extraDepTargets := #[`fastmlfe2ffi]
