import FastMLFE2.NativeFFI

def approxEqTol (eps x y : Float) : Bool :=
  Float.abs (x - y) ≤ eps

def approxEq (x y : Float) : Bool :=
  approxEqTol 1.0e-6 x y

def floatArrayApproxEqTol (eps : Float) (xs ys : FloatArray) : Bool :=
  xs.size == ys.size &&
    Id.run do
      for i in [0:xs.size] do
        if !approxEqTol eps xs[i]! ys[i]! then
          return false
      return true

def floatArrayApproxEq (xs ys : FloatArray) : Bool :=
  floatArrayApproxEqTol 1.0e-6 xs ys

def expectApproxEqArrayTol
    (context : String) (eps : Float) (actual expected : FloatArray) : IO Unit := do
  if !(floatArrayApproxEqTol eps actual expected) then
    throw <| IO.userError s!"{context}: expected {expected}, got {actual}"

def expectApproxEqArray (context : String) (actual expected : FloatArray) : IO Unit := do
  expectApproxEqArrayTol context 1.0e-6 actual expected

def expectArrayInRange (context : String) (actual : FloatArray) : IO Unit := do
  for i in [0:actual.size] do
    let value := actual[i]!
    if value < 0.0 || value > 1.0 then
      throw <| IO.userError s!"{context}: value out of range at {i}: {value}"

def makeRgb
    (width height : Nat)
    (red green blue : List Float) : IO FastMLFE2.NativeRgbImage := do
  pure {
    red := ← FastMLFE2.NativeGrayImage.ofFloatArray width height red.toFloatArray
    green := ← FastMLFE2.NativeGrayImage.ofFloatArray width height green.toFloatArray
    blue := ← FastMLFE2.NativeGrayImage.ofFloatArray width height blue.toFloatArray
  }

def expectRgbApproxEq
    (context : String) (eps : Float)
    (actual expected : FastMLFE2.NativeRgbImage) : IO Unit := do
  let actualRed ← FastMLFE2.NativeGrayImage.toFloatArray actual.red
  let actualGreen ← FastMLFE2.NativeGrayImage.toFloatArray actual.green
  let actualBlue ← FastMLFE2.NativeGrayImage.toFloatArray actual.blue
  let expectedRed ← FastMLFE2.NativeGrayImage.toFloatArray expected.red
  let expectedGreen ← FastMLFE2.NativeGrayImage.toFloatArray expected.green
  let expectedBlue ← FastMLFE2.NativeGrayImage.toFloatArray expected.blue
  expectApproxEqArrayTol s!"{context}.red" eps actualRed expectedRed
  expectApproxEqArrayTol s!"{context}.green" eps actualGreen expectedGreen
  expectApproxEqArrayTol s!"{context}.blue" eps actualBlue expectedBlue

def main : IO Unit := do
  let pixels := ([0.0, 0.5, 1.0, 1.5] : List Float).toFloatArray
  let image ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 pixels
  let w ← FastMLFE2.NativeGrayImage.width image
  let h ← FastMLFE2.NativeGrayImage.height image
  if w != 2 || h != 2 then
    throw <| IO.userError s!"unexpected dimensions: {w}x{h}"
  let roundTrip ← FastMLFE2.NativeGrayImage.toFloatArray image
  if roundTrip != pixels then
    throw <| IO.userError "unexpected round-trip image data"
  let resized ← FastMLFE2.NativeGrayImage.resizeNearest image 4 4
  let rw ← FastMLFE2.NativeGrayImage.width resized
  let rh ← FastMLFE2.NativeGrayImage.height resized
  if rw != 4 || rh != 4 then
    throw <| IO.userError s!"unexpected resized dimensions: {rw}x{rh}"
  let resizedPixels ← FastMLFE2.NativeGrayImage.toFloatArray resized
  expectApproxEqArray "nearest resize"
    resizedPixels
    (([
      0.0, 0.0, 0.5, 0.5,
      0.0, 0.0, 0.5, 0.5,
      1.0, 1.0, 1.5, 1.5,
      1.0, 1.0, 1.5, 1.5
    ] : List Float).toFloatArray)
  let shrinkSrc ← FastMLFE2.NativeGrayImage.ofFloatArray 3 1 (([0.0, 1.0, 2.0] : List Float).toFloatArray)
  let shrinkDst ← FastMLFE2.NativeGrayImage.resizeNearest shrinkSrc 2 1
  let shrinkPixels ← FastMLFE2.NativeGrayImage.toFloatArray shrinkDst
  expectApproxEqArray "reference nearest shrink"
    shrinkPixels
    (([0.0, 1.0] : List Float).toFloatArray)
  let unclampedPixels := ([-0.5, 0.2, 1.2, 0.7] : List Float).toFloatArray
  let unclamped ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 unclampedPixels
  FastMLFE2.NativeGrayImage.clamp01 unclamped
  let clamped ← FastMLFE2.NativeGrayImage.toFloatArray unclamped
  expectApproxEqArray "clamp"
    clamped
    (([0.0, 0.2, 1.0, 0.7] : List Float).toFloatArray)
  let alphaPixels := ([0.25] : List Float).toFloatArray
  let fgPixels := ([0.8] : List Float).toFloatArray
  let bgPixels := ([0.1] : List Float).toFloatArray
  let imagePixels := ([0.3] : List Float).toFloatArray
  let alpha ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 alphaPixels
  let fg ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 fgPixels
  let bg ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 bgPixels
  let singleImage ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 imagePixels
  let (fgOut, bgOut) ←
    FastMLFE2.NativeGrayImage.referenceRefineSinglePass singleImage alpha fg bg 0.5 1.0
  let fgRoundTrip ← FastMLFE2.NativeGrayImage.toFloatArray fgOut
  let bgRoundTrip ← FastMLFE2.NativeGrayImage.toFloatArray bgOut
  if fgRoundTrip.size != 1 || bgRoundTrip.size != 1 then
    throw <| IO.userError "unexpected refine output shape"
  expectApproxEqArray "four-neighbor refine fg" fgRoundTrip (([0.8023809524] : List Float).toFloatArray)
  expectApproxEqArray "four-neighbor refine bg" bgRoundTrip (([0.1071428571] : List Float).toFloatArray)
  let image2 ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 (([0.1, 0.4, 0.7, 0.9] : List Float).toFloatArray)
  let alpha2 ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 (([0.0, 0.3, 0.8, 1.0] : List Float).toFloatArray)
  let fg2 ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 (([0.2, 0.2, 0.8, 0.8] : List Float).toFloatArray)
  let bg2 ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 (([0.0, 0.1, 0.4, 0.5] : List Float).toFloatArray)
  let (fgOut2, bgOut2) ←
    FastMLFE2.NativeGrayImage.referenceRefineSinglePass image2 alpha2 fg2 bg2 0.005 0.1
  let fgRoundTrip2 ← FastMLFE2.NativeGrayImage.toFloatArray fgOut2
  let bgRoundTrip2 ← FastMLFE2.NativeGrayImage.toFloatArray bgOut2
  if fgRoundTrip2.size != 4 || bgRoundTrip2.size != 4 then
    throw <| IO.userError "unexpected multi-pixel refine output shape"
  for i in [0:fgRoundTrip2.size] do
    let fgValue := fgRoundTrip2[i]!
    let bgValue := bgRoundTrip2[i]!
    if fgValue < 0.0 || fgValue > 1.0 then
      throw <| IO.userError s!"multi-pixel refine fg out of range at {i}: {fgValue}"
    if bgValue < 0.0 || bgValue > 1.0 then
      throw <| IO.userError s!"multi-pixel refine bg out of range at {i}: {bgValue}"
  let rgbImage ← makeRgb 2 2
    [0.1, 0.4, 0.7, 0.9]
    [0.2, 0.6, 0.3, 0.8]
    [0.9, 0.5, 0.2, 0.1]
  let rgbAlpha ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2
    (([0.0, 0.3, 0.8, 1.0] : List Float).toFloatArray)
  let fgRgbInit ← makeRgb 2 2
    [0.2, 0.2, 0.8, 0.8]
    [0.1, 0.3, 0.7, 0.9]
    [0.8, 0.6, 0.4, 0.2]
  let bgRgbInit ← makeRgb 2 2
    [0.0, 0.1, 0.4, 0.5]
    [0.9, 0.7, 0.3, 0.1]
    [0.2, 0.4, 0.6, 0.8]
  let (fgOutRgb, bgOutRgb) ←
    FastMLFE2.NativeRgbImage.referenceRefine
      3 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 0.0 0.0
  let fgExpected ← makeRgb 2 2
    [0.830597758, 0.88038969, 0.843004763, 0.894744515]
    [0.461264521, 0.739589155, 0.351412773, 0.784993887]
    [0.102423653, 0.0851337761, 0.0536182709, 0.10242942]
  let bgExpected ← makeRgb 2 2
    [0.107164577, 0.189354777, 0.128722265, 0.194471642]
    [0.212035656, 0.509556174, 0.220379204, 0.447383642]
    [0.883042753, 0.689597011, 0.820391357, 0.680520773]
  expectRgbApproxEq "rgb canonical refine fg" 1.0e-5 fgOutRgb fgExpected
  expectRgbApproxEq "rgb canonical refine bg" 1.0e-5 bgOutRgb bgExpected
  let (fgOneSweep, bgOneSweep) ←
    FastMLFE2.NativeRgbImage.referenceRefine
      1 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 0.0 0.0
  let (fgResidualStop, bgResidualStop) ←
    FastMLFE2.NativeRgbImage.referenceRefine
      5 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 100.0 0.0
  expectRgbApproxEq "rgb residual stop fg" 1.0e-6 fgResidualStop fgOneSweep
  expectRgbApproxEq "rgb residual stop bg" 1.0e-6 bgResidualStop bgOneSweep
  let (fgUpdateStop, bgUpdateStop) ←
    FastMLFE2.NativeRgbImage.referenceRefine
      5 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 0.0 100.0
  expectRgbApproxEq "rgb update stop fg" 1.0e-6 fgUpdateStop fgOneSweep
  expectRgbApproxEq "rgb update stop bg" 1.0e-6 bgUpdateStop bgOneSweep
  let (fgVcycleZero, bgVcycleZero) ←
    FastMLFE2.NativeRgbImage.globalSpdVcycle
      2 0 1 1 4 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 0.0
  expectRgbApproxEq "rgb vcycle zero fg" 1.0e-6 fgVcycleZero fgRgbInit
  expectRgbApproxEq "rgb vcycle zero bg" 1.0e-6 bgVcycleZero bgRgbInit
  let (fgVcycle, bgVcycle) ←
    FastMLFE2.NativeRgbImage.globalSpdVcycle
      2 1 1 1 4 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 0.0
  let fgVcycleExpected ← makeRgb 2 2
    [0.807817996, 0.87388587, 0.83967936, 0.891311824]
    [0.467442304, 0.740829587, 0.352023721, 0.785146832]
    [0.158401713, 0.110177621, 0.0641333014, 0.110751525]
  let bgVcycleExpected ← makeRgb 2 2
    [0.108410649, 0.192118362, 0.132425442, 0.199902028]
    [0.212983996, 0.509907484, 0.220896989, 0.454189509]
    [0.876524687, 0.675309062, 0.800831616, 0.635260463]
  expectRgbApproxEq "rgb vcycle fg" 1.0e-5 fgVcycle fgVcycleExpected
  expectRgbApproxEq "rgb vcycle bg" 1.0e-5 bgVcycle bgVcycleExpected
  let (fgVcycleStop, bgVcycleStop) ←
    FastMLFE2.NativeRgbImage.globalSpdVcycle
      2 5 1 1 4 rgbImage rgbAlpha fgRgbInit bgRgbInit 0.005 0.1 100.0
  expectRgbApproxEq "rgb vcycle residual stop fg" 1.0e-6 fgVcycleStop fgVcycle
  expectRgbApproxEq "rgb vcycle residual stop bg" 1.0e-6 bgVcycleStop bgVcycle
  let fgVcycleRed ← FastMLFE2.NativeGrayImage.toFloatArray fgVcycle.red
  let fgVcycleGreen ← FastMLFE2.NativeGrayImage.toFloatArray fgVcycle.green
  let fgVcycleBlue ← FastMLFE2.NativeGrayImage.toFloatArray fgVcycle.blue
  let bgVcycleRed ← FastMLFE2.NativeGrayImage.toFloatArray bgVcycle.red
  let bgVcycleGreen ← FastMLFE2.NativeGrayImage.toFloatArray bgVcycle.green
  let bgVcycleBlue ← FastMLFE2.NativeGrayImage.toFloatArray bgVcycle.blue
  expectArrayInRange "rgb vcycle fg.red" fgVcycleRed
  expectArrayInRange "rgb vcycle fg.green" fgVcycleGreen
  expectArrayInRange "rgb vcycle fg.blue" fgVcycleBlue
  expectArrayInRange "rgb vcycle bg.red" bgVcycleRed
  expectArrayInRange "rgb vcycle bg.green" bgVcycleGreen
  expectArrayInRange "rgb vcycle bg.blue" bgVcycleBlue
