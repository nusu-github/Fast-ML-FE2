import FastMLFE2.CLI
import FastMLFE2.Runtime

open System

def makeGray (w h : Nat) (values : List Float) : IO FastMLFE2.NativeGrayImage :=
  FastMLFE2.NativeGrayImage.ofFloatArray w h values.toFloatArray

def approxEq (x y : Float) : Bool :=
  Float.abs (x - y) ≤ 1.0e-2

def expectAllEq (context : String) (actual : FloatArray) (expected : Float) : IO Unit := do
  for i in [0:actual.size] do
    if !approxEq actual[i]! expected then
      throw <| IO.userError
        s!"{context}: expected all entries {expected}, got {actual}"

def expectEqNatList (context : String) (actual expected : List (Nat × Nat)) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"{context}: expected {expected}, got {actual}"

def expectValueRange (context : String) (actual : FloatArray) : IO Unit := do
  for i in [0:actual.size] do
    let value := actual[i]!
    if value < 0.0 || value > 1.0 then
      throw <| IO.userError s!"{context}: value out of range at {i}: {value}"

def main : IO Unit := do
  expectEqNatList "manual level count"
    (FastMLFE2.Runtime.levelSizes 100 50 (.manual 4))
    [(1, 1), (5, 4), (22, 14), (100, 50)]
  let tmp ← IO.FS.createTempDir
  let imagePath := tmp / "image.png"
  let alphaPath := tmp / "alpha.png"
  let outFgPath := tmp / "out_fg.png"
  let outBgPath := tmp / "out_bg.png"

  let rgb : FastMLFE2.NativeRgbImage := {
    red := ← makeGray 2 2 [0.0, 1.0, 0.2, 0.8]
    green := ← makeGray 2 2 [0.5, 0.2, 0.7, 0.1]
    blue := ← makeGray 2 2 [1.0, 0.0, 0.4, 0.6]
  }
  let alpha ← makeGray 2 2 [0.0, 0.5, 0.75, 1.0]
  rgb.writePng imagePath
  alpha.writePngGray alphaPath
  let exitCode ← FastMLFE2.CLI.main [
    "--mode",
    "reference",
    "--levels",
    "auto",
    "--n-small-iterations",
    "0",
    "--n-big-iterations",
    "0",
    "--small-size",
    "32",
    "--eps-r",
    "0.005",
    "--omega",
    "0.1",
    imagePath.toString,
    alphaPath.toString,
    outFgPath.toString,
    outBgPath.toString
  ]
  if exitCode != 0 then
    throw <| IO.userError s!"CLI returned nonzero exit code: {exitCode}"
  if !(← outFgPath.pathExists) || !(← outBgPath.pathExists) then
    throw <| IO.userError "CLI did not produce output PNG files"
  let fg ← FastMLFE2.NativeRgbImage.readPng outFgPath
  let bg ← FastMLFE2.NativeRgbImage.readPng outBgPath
  let fgW ← fg.width
  let fgH ← fg.height
  let bgW ← bg.width
  let bgH ← bg.height
  if fgW != 2 || fgH != 2 || bgW != 2 || bgH != 2 then
    throw <| IO.userError "CLI output dimensions are incorrect"
  let fgRed ← FastMLFE2.NativeGrayImage.toFloatArray fg.red
  let fgGreen ← FastMLFE2.NativeGrayImage.toFloatArray fg.green
  let fgBlue ← FastMLFE2.NativeGrayImage.toFloatArray fg.blue
  let bgRed ← FastMLFE2.NativeGrayImage.toFloatArray bg.red
  let bgGreen ← FastMLFE2.NativeGrayImage.toFloatArray bg.green
  let bgBlue ← FastMLFE2.NativeGrayImage.toFloatArray bg.blue
  expectAllEq "fg.red" fgRed 0.8
  expectAllEq "fg.green" fgGreen 0.1
  expectAllEq "fg.blue" fgBlue 0.6
  expectAllEq "bg.red" bgRed 0.0
  expectAllEq "bg.green" bgGreen 0.5
  expectAllEq "bg.blue" bgBlue 1.0
  let outFgIterPath := tmp / "out_fg_iter.png"
  let outBgIterPath := tmp / "out_bg_iter.png"
  let iterExitCode ← FastMLFE2.CLI.main [
    "--mode",
    "reference",
    "--levels",
    "2",
    "--n-small-iterations",
    "1",
    "--n-big-iterations",
    "1",
    "--small-size",
    "1",
    "--eps-r",
    "0.005",
    "--omega",
    "0.1",
    imagePath.toString,
    alphaPath.toString,
    outFgIterPath.toString,
    outBgIterPath.toString
  ]
  if iterExitCode != 0 then
    throw <| IO.userError s!"iterative CLI returned nonzero exit code: {iterExitCode}"
  let fgIter ← FastMLFE2.NativeRgbImage.readPng outFgIterPath
  let bgIter ← FastMLFE2.NativeRgbImage.readPng outBgIterPath
  let fgIterRed ← FastMLFE2.NativeGrayImage.toFloatArray fgIter.red
  let fgIterGreen ← FastMLFE2.NativeGrayImage.toFloatArray fgIter.green
  let fgIterBlue ← FastMLFE2.NativeGrayImage.toFloatArray fgIter.blue
  let bgIterRed ← FastMLFE2.NativeGrayImage.toFloatArray bgIter.red
  let bgIterGreen ← FastMLFE2.NativeGrayImage.toFloatArray bgIter.green
  let bgIterBlue ← FastMLFE2.NativeGrayImage.toFloatArray bgIter.blue
  expectValueRange "fg.iter.red" fgIterRed
  expectValueRange "fg.iter.green" fgIterGreen
  expectValueRange "fg.iter.blue" fgIterBlue
  expectValueRange "bg.iter.red" bgIterRed
  expectValueRange "bg.iter.green" bgIterGreen
  expectValueRange "bg.iter.blue" bgIterBlue
