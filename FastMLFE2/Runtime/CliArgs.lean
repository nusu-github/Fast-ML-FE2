import FastMLFE2.Runtime.Config

namespace FastMLFE2.Runtime

open System

structure ParsedCliArgs where
  mode : Option String := none
  levels : Option LevelSchedule := none
  smallSize : Option Nat := none
  nSmallIterations : Option Nat := none
  nBigIterations : Option Nat := none
  epsR : Option Float := none
  omega : Option Float := none
  positionals : List String := []

structure CliInvocation where
  config : ExecutionConfig
  imagePath : FilePath
  alphaPath : FilePath
  outFgPath : FilePath
  outBgPath : FilePath

def cliUsage : String :=
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

private partial def parseCliArgs (args : List String) (acc : ParsedCliArgs := {}) : IO ParsedCliArgs := do
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

def finalizeConfig (parsed : ParsedCliArgs) : ExecutionConfig :=
  let defaults := defaultConfig
  { defaults with
    levels := parsed.levels.getD defaults.levels
    smallSize := parsed.smallSize.getD defaults.smallSize
    nSmallIterations := parsed.nSmallIterations.getD defaults.nSmallIterations
    nBigIterations := parsed.nBigIterations.getD defaults.nBigIterations
    epsR := parsed.epsR.getD defaults.epsR
    omega := parsed.omega.getD defaults.omega }

def parseCliInvocation (args : List String) : IO CliInvocation := do
  let parsed ← parseCliArgs args
  let config := finalizeConfig parsed
  match parsed.positionals with
  | [imagePath, alphaPath, outFgPath, outBgPath] =>
      pure {
        config := config
        imagePath := (imagePath : System.FilePath)
        alphaPath := (alphaPath : System.FilePath)
        outFgPath := (outFgPath : System.FilePath)
        outBgPath := (outBgPath : System.FilePath)
      }
  | _ =>
      throw <| IO.userError cliUsage

end FastMLFE2.Runtime
