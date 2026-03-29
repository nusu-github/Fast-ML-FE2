import FastMLFE2.Canonical.MultilevelRun
import FastMLFE2.Canonical.GridContext

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

noncomputable def resizeGridPixelDataNNTo
    {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (data : GridPixelData hSrc wSrc) : GridPixelData hDst wDst where
  alpha := nearestNeighborResize
    (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) data.alpha
  image := nearestNeighborResize
    (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) data.image
  epsilonR := data.epsilonR
  omega := data.omega

noncomputable def nearestNeighborPyramidData
    {h w : Nat}
    (finest : GridPixelData h w)
    [Fact (0 < h)] [Fact (0 < w)]
    (target : RealLevelSpec) : GridPixelData target.height target.width :=
  resizeGridPixelDataNNTo
    (hSrc := h) (wSrc := w) (hDst := target.height) (wDst := target.width) finest

noncomputable def nearestNeighborPyramidFamily
    {h w : Nat}
    (finest : GridPixelData h w)
    [Fact (0 < h)] [Fact (0 < w)] : GridBuilderFamily where
  builder h' w' :=
    let resized :=
      resizeGridPixelDataNNTo
        (hSrc := h) (wSrc := w) (hDst := h') (wDst := w') finest
    resized.toCanonicalPixelData.canonicalBuilder

@[simp] theorem resizeGridPixelDataNNTo_alpha
    {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (data : GridPixelData hSrc wSrc)
    (p : Pixel hDst wDst) :
    (resizeGridPixelDataNNTo (hDst := hDst) (wDst := wDst) data).alpha p =
      data.alpha (nearestNeighborPixel
        (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) p) := by
  rfl

@[simp] theorem resizeGridPixelDataNNTo_image
    {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (data : GridPixelData hSrc wSrc)
    (p : Pixel hDst wDst) :
    (resizeGridPixelDataNNTo (hDst := hDst) (wDst := wDst) data).image p =
      data.image (nearestNeighborPixel
        (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) p) := by
  rfl

@[simp] theorem resizeGridPixelDataNNTo_self
    {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)]
    (data : GridPixelData h w) :
    resizeGridPixelDataNNTo (hSrc := h) (wSrc := w) (hDst := h) (wDst := w) data = data := by
  cases data
  simp [resizeGridPixelDataNNTo]

@[simp] theorem nearestNeighborPyramidData_sameSize
    (target : RealLevelSpec)
    (data : GridPixelData target.height target.width) :
    @nearestNeighborPyramidData target.height target.width data
      ⟨target.heightPos⟩ ⟨target.widthPos⟩ target = data := by
  letI : Fact (0 < target.height) := ⟨target.heightPos⟩
  letI : Fact (0 < target.width) := ⟨target.widthPos⟩
  change resizeGridPixelDataNNTo
      (hSrc := target.height) (wSrc := target.width)
      (hDst := target.height) (wDst := target.width) data = data
  exact resizeGridPixelDataNNTo_self
    (h := target.height) (w := target.width) data

@[simp] theorem nearestNeighborPyramidFamily_builder_sameSize
    {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)]
    (data : GridPixelData h w) :
    (nearestNeighborPyramidFamily data).builder h w =
      data.toCanonicalPixelData.canonicalBuilder := by
  simp [nearestNeighborPyramidFamily, resizeGridPixelDataNNTo_self]

end FastMLFE2.Canonical
