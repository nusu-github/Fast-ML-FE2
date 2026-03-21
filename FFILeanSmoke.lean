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

def main : IO Unit := do
  let pixels := ([0.0, 0.5, 1.0, 1.5] : List Float).toFloatArray
  let image ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 pixels
  let w ← image.width
  let h ← image.height
  if w != 2 || h != 2 then
    throw <| IO.userError s!"unexpected dimensions: {w}x{h}"
  let roundTrip ← image.toFloatArray
  if roundTrip != pixels then
    throw <| IO.userError "unexpected round-trip image data"
  let resized ← image.resize 1 4
  let rw ← resized.width
  let rh ← resized.height
  if rw != 1 || rh != 4 then
    throw <| IO.userError s!"unexpected resized dimensions: {rw}x{rh}"
  let unclampedPixels := ([-0.5, 0.2, 1.2, 0.7] : List Float).toFloatArray
  let unclamped ← FastMLFE2.NativeGrayImage.ofFloatArray 2 2 unclampedPixels
  unclamped.clamp01
  let clamped ← unclamped.toFloatArray
  if !(floatArrayApproxEq clamped (([0.0, 0.2, 1.0, 0.7] : List Float).toFloatArray)) then
    throw <| IO.userError s!"unexpected clamp output: {clamped}"
  let alphaPixels := ([0.25] : List Float).toFloatArray
  let fgPixels := ([0.8] : List Float).toFloatArray
  let bgPixels := ([0.1] : List Float).toFloatArray
  let imagePixels := ([0.3] : List Float).toFloatArray
  let alpha ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 alphaPixels
  let fg ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 fgPixels
  let bg ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 bgPixels
  let singleImage ← FastMLFE2.NativeGrayImage.ofFloatArray 1 1 imagePixels
  let (fgOut, bgOut) ← FastMLFE2.NativeGrayImage.paperRefinePass singleImage alpha fg bg 0.5 1.0
  let fgRoundTrip ← fgOut.toFloatArray
  let bgRoundTrip ← bgOut.toFloatArray
  if fgRoundTrip.size != 1 || bgRoundTrip.size != 1 then
    throw <| IO.userError "unexpected refine output shape"
