import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Canonical

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level

namespace GridPixelData

abbrev localCtx
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w)) :
    LocalContext (ValidDir p) :=
  data.toCanonicalPixelData.toLocalContext p state

@[simp] theorem localCtx_eq_toLocalContext
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w)) :
    data.localCtx p state = data.toCanonicalPixelData.toLocalContext p state := by
  rfl

@[simp] theorem localCtx_eq_builder_build
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w)) :
    data.localCtx p state = (data.toCanonicalPixelData.canonicalBuilder.build p state) := by
  rfl

end GridPixelData

end FastMLFE2.Theory.Canonical
