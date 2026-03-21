import FastMLFE2.NativeFFI

open System

namespace FastMLFE2.CLI

private def usage : String :=
  "usage: fastmlfe-cli image.png alpha.png out_fg.png out_bg.png levels iters_per_level eps_r omega"

private def pow10 : Nat → Float
  | 0 => 1.0
  | n + 1 => 10.0 * pow10 n

private def parseFloat? (s : String) : Option Float :=
  match s.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
      match whole.toNat?, frac.toNat? with
      | some w, some f =>
          some <| Float.ofNat w + Float.ofNat f / pow10 frac.length
      | _, _ => none
  | _ => none

private def parseNatArg (name value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid {name}: {value}"

private def parseFloatArg (name value : String) : IO Float :=
  match parseFloat? value with
  | some x => pure x
  | none => throw <| IO.userError s!"invalid {name}: {value}"

private def ceilDiv (x y : Nat) : Nat :=
  (x + y - 1) / y

private def levelSizes (width height levels : Nat) : List (Nat × Nat) :=
  (List.range levels).map fun idx =>
    let divisor := Nat.pow 2 (levels - 1 - idx)
    (max 1 (ceilDiv width divisor), max 1 (ceilDiv height divisor))

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
      let (fg', bg') ← image.paperRefinePass alpha fg bg epsR omega
      fg'.clamp01
      bg'.clamp01
      loop (remaining - 1) fg' bg'
  loop iterations fg bg

def runMultilevelForegroundEstimation
    (image : NativeRgbImage) (alpha : NativeGrayImage)
    (levels itersPerLevel : Nat) (epsR omega : Float) :
    IO (NativeRgbImage × NativeRgbImage) := do
  if levels = 0 then
    throw <| IO.userError "levels must be positive"
  if !(epsR > 0.0) then
    throw <| IO.userError "eps_r must be positive"
  if omega < 0.0 then
    throw <| IO.userError "omega must be nonnegative"
  image.assertWellFormed
  let width ← image.width
  let height ← image.height
  let alphaWidth ← alpha.width
  let alphaHeight ← alpha.height
  if width != alphaWidth || height != alphaHeight then
    throw <| IO.userError
      s!"image/alpha shape mismatch: image={width}x{height}, alpha={alphaWidth}x{alphaHeight}"
  let schedule := levelSizes width height levels
  let rec loop (sizes : List (Nat × Nat)) (fg bg : NativeRgbImage) : IO (NativeRgbImage × NativeRgbImage) := do
    match sizes with
    | [] => pure (fg, bg)
    | (levelW, levelH) :: rest =>
        let imageLevel ← image.resize levelW levelH
        let alphaLevel ← alpha.resize levelW levelH
        let fgLevel ← fg.resize levelW levelH
        let bgLevel ← bg.resize levelW levelH
        let (fgNext, bgNext) ← iteratePasses itersPerLevel imageLevel alphaLevel fgLevel bgLevel epsR omega
        loop rest fgNext bgNext
  loop schedule image image

def runCli (args : List String) : IO PUnit := do
  match args with
  | [imagePath, alphaPath, outFgPath, outBgPath, levelsArg, itersArg, epsArg, omegaArg] =>
      let levels ← parseNatArg "levels" levelsArg
      let itersPerLevel ← parseNatArg "iters_per_level" itersArg
      let epsR ← parseFloatArg "eps_r" epsArg
      let omega ← parseFloatArg "omega" omegaArg
      let image ← NativeRgbImage.readPng imagePath
      let alpha ← NativeGrayImage.readPngGray alphaPath
      let (fg, bg) ← runMultilevelForegroundEstimation image alpha levels itersPerLevel epsR omega
      fg.writePng outFgPath
      bg.writePng outBgPath
  | _ =>
      throw <| IO.userError usage

def main (args : List String) : IO UInt32 := do
  try
    runCli args
    pure 0
  catch e =>
    IO.eprintln e.toString
    pure 1

end FastMLFE2.CLI
