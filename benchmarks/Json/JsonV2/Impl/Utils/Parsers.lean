import JsonV2.Impl.Utils.Cursors

/-!
# Json.Impl.Utils.Parsers

Parser result vocabulary translated from `JSON.Utils.Parsers`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev SplitResult (T R : Type) := Except (CursorError R) (Split T)

end JSON
