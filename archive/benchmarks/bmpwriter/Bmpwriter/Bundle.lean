import Bmpwriter.Impl.Image

/-!
# Bmpwriter.Bundle

Per-package implementation bundle for the `Bmpwriter` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure BmpwriterBundle where
  build       : Bmpwriter.BuildSig
  parseWidth  : Bmpwriter.ParseWidthSig
  parseHeight : Bmpwriter.ParseHeightSig
  parse       : Bmpwriter.ParseSig
  validMagic  : Bmpwriter.ValidMagicSig
