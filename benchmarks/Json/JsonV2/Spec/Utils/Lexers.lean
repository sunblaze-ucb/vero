import JsonV2.Harness

/-!
# Json.Spec.Utils.Lexers

Frozen specifications for lexer behavior from `JSON.Utils.Lexers`.
-/

open JSON

/-- A backslash toggles the string-body escape state. -/
def spec_string_body_backslash_toggles_escape (impl : RepoImpl) : Prop :=
  ∀ (R : Type) (escaped : Bool),
    impl.json.stringBody R escaped (some (92 : UInt8)) = .partial_ (!escaped)

/-- An unescaped double quote accepts the string body. -/
def spec_string_body_accept_unescaped_quote (impl : RepoImpl) : Prop :=
  ∀ (R : Type),
    impl.json.stringBody R false (some (34 : UInt8)) = .accept

/-- An escaped double quote continues the string body and clears the escape state. -/
def spec_string_body_escaped_quote_continues (impl : RepoImpl) : Prop :=
  ∀ (R : Type),
    impl.json.stringBody R true (some (34 : UInt8)) = .partial_ false

/-- A JSON string starts with a double quote. -/
def spec_lex_string_start_quote (impl : RepoImpl) : Prop :=
  impl.json.lexString .start (some (34 : UInt8)) = .partial_ (.body false)

/-- Any non-quote byte at the start rejects the string. -/
def spec_lex_string_start_non_quote_rejects (impl : RepoImpl) : Prop :=
  ∀ (byte : Option UInt8),
    byte ≠ some (34 : UInt8) →
    ∃ err : String, impl.json.lexString .start byte = .reject err

/-- The end state accepts any next byte. -/
def spec_lex_string_end_accepts (impl : RepoImpl) : Prop :=
  ∀ (byte : Option UInt8),
    impl.json.lexString .end_ byte = .accept

/-- A backslash toggles the full string lexer's body escape state. -/
def spec_lex_string_body_backslash_toggles (impl : RepoImpl) : Prop :=
  ∀ (escaped : Bool),
    impl.json.lexString (.body escaped) (some (92 : UInt8)) = .partial_ (.body (!escaped))

/-- An unescaped body quote moves the string lexer to the end state. -/
def spec_lex_string_body_unescaped_quote_ends (impl : RepoImpl) : Prop :=
  impl.json.lexString (.body false) (some (34 : UInt8)) = .partial_ .end_

/-- An escaped body quote continues the string body and clears the escape state. -/
def spec_lex_string_body_escaped_quote_continues (impl : RepoImpl) : Prop :=
  impl.json.lexString (.body true) (some (34 : UInt8)) = .partial_ (.body false)
