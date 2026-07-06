import Textwrap.Impl.Wrap

/-!
# Textwrap.Bundle

Per-package implementation bundle for the `Textwrap` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure TextwrapBundle where
  wrap    : Textwrap.WrapSig
  shorten : Textwrap.ShortenSig
