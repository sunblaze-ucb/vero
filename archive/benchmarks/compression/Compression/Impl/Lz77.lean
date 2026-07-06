-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Compression.Impl.Lz77

LZ77 sliding-window compression (Lempel and Ziv, 1977).  Encodes a
string as a list of `Token`s (offset, match-length, indicator-char) and
decodes by reconstructing the original string from the token list.

The internal helpers `lz77MatchLen`, `lz77FindToken`, and
`lz77CompressLoop` are marked `partial def` because Lean cannot
automatically verify their termination (bounded by text shrinkage and
the lookahead cap, but the proof would require a custom measure).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- An LZ77 encoding token: (search-buffer offset, match length,
    next literal character). -/
structure Token where
  offset    : Nat
  length    : Nat
  indicator : Char
  deriving Repr, BEq

/-- LZ77 compressor configuration: window size and lookahead-buffer size.
    Search-buffer size = `window_size - lookahead_buffer_size`. -/
structure LZ77Compressor where
  window_size           : Nat
  lookahead_buffer_size : Nat
  deriving Repr

namespace Compression

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev LZ77CompressSig   := LZ77Compressor → String → List Token
abbrev LZ77DecompressSig := LZ77Compressor → List Token → String

end Compression

-- ── Shared helpers (fixed vocabulary, no markers) ────────────

/-- Search-buffer size derived from the compressor configuration. -/
def LZ77Compressor.searchBufSize (c : LZ77Compressor) : Nat :=
  c.window_size - c.lookahead_buffer_size

/-- Safe index into a `List Char`; returns `none` for out-of-bounds. -/
private def charGetOpt : List Char → Nat → Option Char
  | [],     _     => none
  | a :: _, 0     => some a
  | _ :: t, n + 1 => charGetOpt t n

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────

-- !benchmark @start code_aux def=LZ77Compressor.decompress
-- !benchmark @end code_aux def=LZ77Compressor.decompress

def Compression.LZ77Compressor.decompress : Compression.LZ77DecompressSig :=
-- !benchmark @start code def=LZ77Compressor.decompress
  fun _compressor tokens =>
    let chars : List Char :=
      tokens.foldl (fun output token =>
        let expanded :=
          (List.range token.length).foldl (fun acc _ =>
            let idx := acc.length - token.offset
            acc ++ [charGetOpt acc idx |>.getD ' ']
          ) output
        expanded ++ [token.indicator]
      ) []
    String.ofList chars
-- !benchmark @end code def=LZ77Compressor.decompress

-- !benchmark @start code_aux def=LZ77Compressor.compress
-- Match `text` against `window` starting at `window[wi]`, extending the
-- window with each matched character (enables cyclic / overlapping matches).
-- @review human: termination via `remaining` counter (≤ text.length)
private partial def lz77MatchLen
    (text window : List Char) (wi remaining : Nat) : Nat :=
  if remaining == 0 then 0
  else match text, charGetOpt window wi with
  | [],      _        => 0
  | _,       none     => 0
  | tc :: _, some wc  =>
    if tc != wc then 0
    else 1 + lz77MatchLen text.tail (window ++ [tc]) (wi + 1) (remaining - 1)

-- Find the best (offset, match-length) for the start of `textChars` in `searchBuf`.
private def lz77FindToken (textChars searchBuf : List Char) : Token :=
  let indicator := textChars.head? |>.getD ' '
  if searchBuf.isEmpty then ⟨0, 0, indicator⟩
  else
    let bufLen   := searchBuf.length
    let maxMatch := textChars.length - 1
    let (bestOff, bestLen) :=
      (List.range bufLen).foldl (fun (bOff, bLen) i =>
        let c := charGetOpt searchBuf i |>.getD ' '
        if textChars.head? != some c then (bOff, bLen)
        else
          let fLen := lz77MatchLen textChars searchBuf i maxMatch
          if fLen ≥ bLen then (bufLen - i, fLen)
          else (bOff, bLen)
      ) (0, 0)
    ⟨bestOff, bestLen, charGetOpt textChars bestLen |>.getD ' '⟩

-- Main compression loop.
-- @review human: termination via textChars shrinking by ≥ 1 (token.length + 1) each step
private partial def lz77CompressLoop
    (textChars searchBuf : List Char) (searchBufSize : Nat)
    (out : List Token) : List Token :=
  if textChars.isEmpty then out
  else
    let token    := lz77FindToken textChars searchBuf
    let consumed := token.length + 1
    let newBuf   := searchBuf ++ textChars.take consumed
    let excess   := newBuf.length - min newBuf.length searchBufSize
    let trimmed  := newBuf.drop excess
    lz77CompressLoop (textChars.drop consumed) trimmed searchBufSize (out ++ [token])
-- !benchmark @end code_aux def=LZ77Compressor.compress

partial def Compression.LZ77Compressor.compress : Compression.LZ77CompressSig :=
-- !benchmark @start code def=LZ77Compressor.compress
  fun compressor text =>
    lz77CompressLoop text.toList [] compressor.searchBufSize []
-- !benchmark @end code def=LZ77Compressor.compress
