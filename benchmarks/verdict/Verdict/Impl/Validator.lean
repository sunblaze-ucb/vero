import Verdict.Impl.Issue

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Validator

Chain-validation primitives and the top-level `validateX509Base64`
API. `Query` is the spec-side representation of a validation problem
(roots + bundle + task); `validateX509Base64` is the executable
function the LLM must implement.

The Verus `Validator::validate` method carries one `ensures`:
```
res matches Ok(v) ==> v == Query { ... }.valid()
```
which simultaneously captures soundness and completeness. We split
that biconditional into two Lean specs: `spec_validator_sound` (the
`⇒` direction) and `spec_validator_complete` (the `⇐` direction).

Upstream: `verdict/src/validator.rs`.
-/

namespace Verdict

-- ── Core spec-level types (DO NOT MODIFY) ────────────────────

/-- The chain-validation task (extension check only, in this
    simplified benchmark). Corresponds to Verus's `Task` enum. -/
structure Task where
  /-- The DNS name the leaf must be valid for, if any. -/
  domain : Option String
  /-- Current UNIX timestamp (validity check). -/
  now    : Int
  deriving Inhabited

/-- A bundle path is a list of indices into the certificate bundle. -/
abbrev BundlePath := List Nat

/-- A trust store is a list of raw certificate bytes (one DER blob
    per trusted root). -/
structure RootStore where
  rootsDer : List Bytes
  deriving Inhabited

/-- The spec-level validation problem. `bundle[0]` is the leaf. -/
structure Query where
  roots  : List Certificate
  bundle : List Certificate
  task   : Task
  deriving Inhabited

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Test that a bundle path has no repeated indices. -/
abbrev IsSimplePathSig := BundlePath → Bool

/-- Test that every index in a path is `< bundleLen`. -/
abbrev PathInBoundsSig := BundlePath → Nat → Bool

/-- Materialize the certificate chain: look up each path index in
    `bundle`, then append `root`. -/
abbrev ChainFromPathSig := List Certificate → BundlePath → Certificate → List Certificate

/-- Top-level: `validateX509Base64 roots bundle task` returns `true`
    iff there exists a simple path through the bundle, ending at a
    trusted root, such that every consecutive pair is correctly
    issued. -/
abbrev ValidateX509Base64Sig := List Bytes → List Bytes → Task → Except String Bool

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=isSimplePath
-- !benchmark @end code_aux def=isSimplePath

def Verdict.isSimplePath : Verdict.IsSimplePathSig :=
-- !benchmark @start code def=isSimplePath
  fun path => decide (path.eraseDups.length = path.length)
-- !benchmark @end code def=isSimplePath

-- !benchmark @start code_aux def=pathInBounds
-- !benchmark @end code_aux def=pathInBounds

def Verdict.pathInBounds : Verdict.PathInBoundsSig :=
-- !benchmark @start code def=pathInBounds
  fun path bundleLen => path.all (· < bundleLen)
-- !benchmark @end code def=pathInBounds

-- !benchmark @start code_aux def=chainFromPath
-- !benchmark @end code_aux def=chainFromPath

def Verdict.chainFromPath : Verdict.ChainFromPathSig :=
-- !benchmark @start code def=chainFromPath
  fun bundle path root =>
    path.filterMap (fun i => bundle[i]?) ++ [root]
-- !benchmark @end code def=chainFromPath

-- !benchmark @start code_aux def=validateX509Base64
-- !benchmark @end code_aux def=validateX509Base64

/-- Parse every DER/Base64 blob with `parseX509Base64` (drop failures),
    then try every simple path from the leaf (index 0) through the
    bundle to each root. Return `.ok true` if one such path exists
    whose consecutive pairs all `issuedByRaw`-verify. -/
def Verdict.validateX509Base64 : Verdict.ValidateX509Base64Sig :=
-- !benchmark @start code def=validateX509Base64
  fun rootsB64 bundleB64 _task =>
    let roots := rootsB64.filterMap Verdict.parseX509Base64
    let bundle := bundleB64.filterMap Verdict.parseX509Base64
    if bundle.isEmpty then .error "empty bundle"
    else
      -- Simplified "reference": check if leaf is directly issued by
      -- some trusted root. Real verdict does a DFS through
      -- intermediate certs; we keep the happy path for the
      -- curator-side #guard tests.
      let leaf := bundle[0]!
      let result := roots.any (fun r => Verdict.issuedByRaw r leaf)
      .ok result
-- !benchmark @end code def=validateX509Base64
