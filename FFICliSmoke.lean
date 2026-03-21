import FastMLFE2.CLI

open System

def makeGray (w h : Nat) (values : List Float) : IO FastMLFE2.NativeGrayImage :=
  FastMLFE2.NativeGrayImage.ofFloatArray w h values.toFloatArray

def main : IO Unit := do
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
    imagePath.toString,
    alphaPath.toString,
    outFgPath.toString,
    outBgPath.toString,
    "2",
    "1",
    "0.001",
    "1.0"
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
