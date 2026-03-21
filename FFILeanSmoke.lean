import FastMLFE2.NativeFFI

def approxEq (x y : Float) : Bool :=
  Float.abs (x - y) ≤ 1.0e-6

def floatArrayApproxEq (xs ys : FloatArray) : Bool :=
  xs.size == ys.size &&
    Id.run do
      for i in [0:xs.size] do
        if !approxEq xs[i]! ys[i]! then
          return false
      return true

def expectApproxEqArray (context : String) (actual expected : FloatArray) : IO Unit := do
  if !(floatArrayApproxEq actual expected) then
    throw <| IO.userError s!"{context}: expected {expected}, got {actual}"

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
  let (fgOut, bgOut) ← FastMLFE2.NativeGrayImage.referenceRefinePass singleImage alpha fg bg 0.5 1.0
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
  let (fgOut2, bgOut2) ← FastMLFE2.NativeGrayImage.referenceRefinePass image2 alpha2 fg2 bg2 0.005 0.1
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
