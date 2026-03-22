import FastMLFE2.NativeFFI
import FastMLFE2.Runtime.CliArgs
import FastMLFE2.Runtime.Config

namespace FastMLFE2.Runtime

private def constantFloatArray (size : Nat) (value : Float) : FloatArray :=
  Id.run do
    let mut arr := FloatArray.empty
    for _ in [0:size] do
      arr := arr.push value
    return arr

private def constantGrayImage (width height : Nat) (value : Float) : IO NativeGrayImage :=
  NativeGrayImage.ofFloatArray width height (constantFloatArray (width * height) value)

private def meanColorChannel (channel alpha : NativeGrayImage) (pickForeground : Bool) : IO Float := do
  let channelValues ← NativeGrayImage.toFloatArray channel
  let alphaValues ← NativeGrayImage.toFloatArray alpha
  if channelValues.size != alphaValues.size then
    throw <| IO.userError "meanColorChannel: channel/alpha size mismatch"
  let mut sum := 0.0
  let mut count := 0.0
  for i in [0:alphaValues.size] do
    let a := alphaValues[i]!
    let keep := if pickForeground then a > 0.9 else a < 0.1
    if keep then
      sum := sum + channelValues[i]!
      count := count + 1.0
  pure (sum / (count + 0.00001))

def referenceInit (image : NativeRgbImage) (alpha : NativeGrayImage) : IO (NativeRgbImage × NativeRgbImage) := do
  image.assertWellFormed
  let width ← NativeRgbImage.width image
  let height ← NativeRgbImage.height image
  let fgR ← meanColorChannel image.red alpha true
  let fgG ← meanColorChannel image.green alpha true
  let fgB ← meanColorChannel image.blue alpha true
  let bgR ← meanColorChannel image.red alpha false
  let bgG ← meanColorChannel image.green alpha false
  let bgB ← meanColorChannel image.blue alpha false
  let fg : NativeRgbImage := {
    red := ← constantGrayImage width height fgR
    green := ← constantGrayImage width height fgG
    blue := ← constantGrayImage width height fgB
  }
  let bg : NativeRgbImage := {
    red := ← constantGrayImage width height bgR
    green := ← constantGrayImage width height bgG
    blue := ← constantGrayImage width height bgB
  }
  pure (fg, bg)

/-- `reference` is the executable multi-level solver, aligned with the pymatting-style implementation.
It uses nearest-neighbor resizing and mean-color initialization. This runtime path is distinct
from the Lean `spec` model and does not claim identical step semantics. Each level now uses
RBGS with a max-iteration cap plus level-dependent adaptive stopping, or the new
global linear V-cycle solver selected by `ExecutionConfig.solver`. -/
def runMultilevelForegroundEstimation
    (image : NativeRgbImage) (alpha : NativeGrayImage) (config : ExecutionConfig) :
    IO (NativeRgbImage × NativeRgbImage) := do
  if config.smallSize = 0 then
    throw <| IO.userError "small_size must be positive"
  if !(config.epsR > 0.0) then
    throw <| IO.userError "eps_r must be positive"
  if config.omega < 0.0 then
    throw <| IO.userError "omega must be nonnegative"
  if config.smallResidualTol < 0.0 then
    throw <| IO.userError "small_residual_tol must be nonnegative"
  if config.bigUpdateTol < 0.0 then
    throw <| IO.userError "big_update_tol must be nonnegative"
  if config.vcycleResidualTol < 0.0 then
    throw <| IO.userError "vcycle_residual_tol must be nonnegative"
  image.assertWellFormed
  let width ← NativeRgbImage.width image
  let height ← NativeRgbImage.height image
  let alphaWidth ← NativeGrayImage.width alpha
  let alphaHeight ← NativeGrayImage.height alpha
  if width != alphaWidth || height != alphaHeight then
    throw <| IO.userError
      s!"image/alpha shape mismatch: image={width}x{height}, alpha={alphaWidth}x{alphaHeight}"
  let schedule := levelSizes width height config.levels
  let (fg0, bg0) ← referenceInit image alpha
  match config.solver with
  | .rbgs =>
      let rec loop (sizes : List (Nat × Nat)) (fg bg : NativeRgbImage) : IO (NativeRgbImage × NativeRgbImage) := do
        match sizes with
        | [] => pure (fg, bg)
        | (levelW, levelH) :: rest =>
            let imageLevel ← NativeRgbImage.resizeNearest image levelW levelH
            let alphaLevel ← NativeGrayImage.resizeNearest alpha levelW levelH
            let fgLevel ← NativeRgbImage.resizeNearest fg levelW levelH
            let bgLevel ← NativeRgbImage.resizeNearest bg levelW levelH
            let stopPolicy := stopPolicyForLevel config levelW levelH
            let (fgNext, bgNext) ←
              NativeRgbImage.referenceRefine
                stopPolicy.maxIterations
                imageLevel alphaLevel fgLevel bgLevel
                config.epsR config.omega
                stopPolicy.residualTol stopPolicy.updateTol
            loop rest fgNext bgNext
      loop schedule fg0 bg0
  | .globalVcycle =>
      let levelCount := max 1 schedule.length
      NativeRgbImage.globalSpdVcycle
        levelCount
        config.vcycleMaxCycles
        config.vcyclePreSmoothing
        config.vcyclePostSmoothing
        config.vcycleCoarseIterations
        image alpha fg0 bg0
        config.epsR config.omega config.vcycleResidualTol

def runCliInvocation (invocation : CliInvocation) : IO PUnit := do
  let image ← NativeRgbImage.readPng invocation.imagePath
  let alpha ← NativeGrayImage.readPngGray invocation.alphaPath
  let (fg, bg) ← runMultilevelForegroundEstimation image alpha invocation.config
  NativeRgbImage.writePng invocation.outFgPath fg
  NativeRgbImage.writePng invocation.outBgPath bg

end FastMLFE2.Runtime
