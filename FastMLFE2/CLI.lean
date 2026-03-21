import FastMLFE2.NativeFFI

open System

namespace FastMLFE2.CLI

inductive LevelSchedule where
  | auto
  | manual (count : Nat)
  deriving BEq, DecidableEq, Repr

structure ExecutionConfig where
  levels : LevelSchedule
  smallSize : Nat
  nSmallIterations : Nat
  nBigIterations : Nat
  epsR : Float
  omega : Float

private structure ParsedArgs where
  mode : Option String := none
  levels : Option LevelSchedule := none
  smallSize : Option Nat := none
  nSmallIterations : Option Nat := none
  nBigIterations : Option Nat := none
  epsR : Option Float := none
  omega : Option Float := none
  positionals : List String := []

private def usage : String :=
  String.intercalate "\n"
    [ "usage: fastmlfe-cli [options] image.png alpha.png out_fg.png out_bg.png"
    , "options:"
    , "  --mode reference"
    , "  --levels auto|N"
    , "  --small-size N"
    , "  --n-small-iterations N"
    , "  --n-big-iterations N"
    , "  --eps-r X"
    , "  --omega X"
    ]

private def parseUnsignedNatArg (name value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid {name}: {value}"

private def parseFloatCore? (s : String) : Option Float :=
  match s.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
      match whole.toNat?, frac.toNat? with
      | some w, some f =>
          some <| Float.ofNat w + Float.ofNat f / (10.0 ^ Float.ofNat frac.length)
      | _, _ => none
  | _ => none

private def parseFloatArg (name value : String) : IO Float := do
  let (sign, magnitude) :=
    if value.startsWith "-" then
      (-1.0, (value.drop 1).toString)
    else if value.startsWith "+" then
      (1.0, (value.drop 1).toString)
    else
      (1.0, value)
  match parseFloatCore? magnitude with
  | some x => pure (sign * x)
  | none => throw <| IO.userError s!"invalid {name}: {value}"

private def parseModeArg (value : String) : IO String :=
  match value with
  | "reference" => pure value
  | "paper" => throw <| IO.userError "paper mode has been removed; use the reference solver"
  | _ => throw <| IO.userError s!"invalid mode: {value}"

private def parseLevelsArg (value : String) : IO LevelSchedule := do
  if value = "auto" then
    pure .auto
  else
    let n ← parseUnsignedNatArg "levels" value
    if n = 0 then
      throw <| IO.userError "levels must be positive"
    pure (.manual n)

private partial def parseCliArgs (args : List String) (acc : ParsedArgs := {}) : IO ParsedArgs := do
  match args with
  | [] => pure acc
  | "--mode" :: value :: rest =>
      parseCliArgs rest { acc with mode := some (← parseModeArg value) }
  | "--levels" :: value :: rest =>
      parseCliArgs rest { acc with levels := some (← parseLevelsArg value) }
  | "--small-size" :: value :: rest =>
      parseCliArgs rest { acc with smallSize := some (← parseUnsignedNatArg "small_size" value) }
  | "--n-small-iterations" :: value :: rest =>
      parseCliArgs rest { acc with nSmallIterations := some (← parseUnsignedNatArg "n_small_iterations" value) }
  | "--n-big-iterations" :: value :: rest =>
      parseCliArgs rest { acc with nBigIterations := some (← parseUnsignedNatArg "n_big_iterations" value) }
  | "--eps-r" :: value :: rest =>
      parseCliArgs rest { acc with epsR := some (← parseFloatArg "eps_r" value) }
  | "--omega" :: value :: rest =>
      parseCliArgs rest { acc with omega := some (← parseFloatArg "omega" value) }
  | option :: rest =>
      if option.startsWith "--" then
        throw <| IO.userError s!"unknown option: {option}"
      else
        parseCliArgs rest { acc with positionals := acc.positionals ++ [option] }

private def defaultConfig : ExecutionConfig :=
  { levels := .auto
  , smallSize := 32
  , nSmallIterations := 10
  , nBigIterations := 2
  , epsR := 0.00001
  , omega := 1.0
  }

private def finalizeConfig (parsed : ParsedArgs) : ExecutionConfig :=
  let defaults := defaultConfig
  { defaults with
    levels := parsed.levels.getD defaults.levels
    smallSize := parsed.smallSize.getD defaults.smallSize
    nSmallIterations := parsed.nSmallIterations.getD defaults.nSmallIterations
    nBigIterations := parsed.nBigIterations.getD defaults.nBigIterations
    epsR := parsed.epsR.getD defaults.epsR
    omega := parsed.omega.getD defaults.omega
  }

private def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    Nat.log2 (n - 1) + 1

private def roundFloatToNatAtLeastOne (x : Float) : Nat :=
  max 1 (UInt64.toNat (Float.toUInt64 (Float.round x)))

private def levelSizeAt (size level levelCount : Nat) : Nat :=
  if levelCount = 0 then
    size
  else
    roundFloatToNatAtLeastOne
      ((Float.ofNat size) ^ (Float.ofNat level / Float.ofNat levelCount))

private def autoLevelSizes (width height : Nat) : List (Nat × Nat) :=
  let levelCount := ceilLog2 (max width height)
  if levelCount = 0 then
    [(width, height)]
  else
    (List.range (levelCount + 1)).map fun level =>
      (levelSizeAt width level levelCount, levelSizeAt height level levelCount)

private def manualLevelSizes (width height count : Nat) : List (Nat × Nat) :=
  if count = 0 then
    []
  else if count = 1 then
    [(width, height)]
  else
    (List.range count).map fun level =>
      (levelSizeAt width level (count - 1), levelSizeAt height level (count - 1))

private def levelSizes (width height : Nat) (levels : LevelSchedule) : List (Nat × Nat) :=
  match levels with
  | .auto => autoLevelSizes width height
  | .manual count => manualLevelSizes width height count

def testLevelSizes (width height : Nat) (levels : LevelSchedule) : List (Nat × Nat) :=
  levelSizes width height levels

private def iterationsForLevel (config : ExecutionConfig) (width height : Nat) : Nat :=
  if width ≤ config.smallSize && height ≤ config.smallSize then
    config.nSmallIterations
  else
    config.nBigIterations

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

private def referenceInit (image : NativeRgbImage) (alpha : NativeGrayImage) : IO (NativeRgbImage × NativeRgbImage) := do
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

private partial def iteratePasses
    (iterations : Nat)
    (image : NativeRgbImage) (alpha : NativeGrayImage)
    (fg bg : NativeRgbImage)
    (epsR omega : Float) :
    IO (NativeRgbImage × NativeRgbImage) := do
  let rec loop (remaining : Nat) (fg bg : NativeRgbImage) : IO (NativeRgbImage × NativeRgbImage) := do
    if remaining = 0 then
      pure (fg, bg)
    else
      let (fg', bg') ← NativeRgbImage.referenceRefinePass image alpha fg bg epsR omega
      NativeRgbImage.clamp01 fg'
      NativeRgbImage.clamp01 bg'
      loop (remaining - 1) fg' bg'
  loop iterations fg bg

/-- `reference` is the executable multi-level solver, aligned with the pymatting-style implementation.
It uses nearest-neighbor resizing and mean-color initialization. This runtime path is distinct
from the Lean `spec` model and does not claim identical step semantics. -/
def runMultilevelForegroundEstimation
    (image : NativeRgbImage) (alpha : NativeGrayImage) (config : ExecutionConfig) :
    IO (NativeRgbImage × NativeRgbImage) := do
  if config.smallSize = 0 then
    throw <| IO.userError "small_size must be positive"
  if !(config.epsR > 0.0) then
    throw <| IO.userError "eps_r must be positive"
  if config.omega < 0.0 then
    throw <| IO.userError "omega must be nonnegative"
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
  let rec loop (sizes : List (Nat × Nat)) (fg bg : NativeRgbImage) : IO (NativeRgbImage × NativeRgbImage) := do
    match sizes with
    | [] => pure (fg, bg)
    | (levelW, levelH) :: rest =>
        let imageLevel ← NativeRgbImage.resizeNearest image levelW levelH
        let alphaLevel ← NativeGrayImage.resizeNearest alpha levelW levelH
        let fgLevel ← NativeRgbImage.resizeNearest fg levelW levelH
        let bgLevel ← NativeRgbImage.resizeNearest bg levelW levelH
        let iterations := iterationsForLevel config levelW levelH
        let (fgNext, bgNext) ← iteratePasses iterations imageLevel alphaLevel fgLevel bgLevel config.epsR config.omega
        loop rest fgNext bgNext
  loop schedule fg0 bg0

private def parseInvocation (args : List String) : IO (ExecutionConfig × FilePath × FilePath × FilePath × FilePath) := do
  let parsed ← parseCliArgs args
  let config := finalizeConfig parsed
  match parsed.positionals with
  | [imagePath, alphaPath, outFgPath, outBgPath] =>
      pure (config, imagePath, alphaPath, outFgPath, outBgPath)
  | _ =>
      throw <| IO.userError usage

def runCli (args : List String) : IO PUnit := do
  let (config, imagePath, alphaPath, outFgPath, outBgPath) ← parseInvocation args
  let image ← NativeRgbImage.readPng imagePath
  let alpha ← NativeGrayImage.readPngGray alphaPath
  let (fg, bg) ← runMultilevelForegroundEstimation image alpha config
  NativeRgbImage.writePng outFgPath fg
  NativeRgbImage.writePng outBgPath bg

def main (args : List String) : IO UInt32 := do
  try
    runCli args
    pure 0
  catch e =>
    IO.eprintln e.toString
    pure 1

end FastMLFE2.CLI
