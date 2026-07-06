from vero.curation.models import SourceLanguage
from vero.curation.stages.source_index import _extract_entities


def test_dafny_source_index_extracts_json_declaration_shapes() -> None:
    text = """
module {:options "-functionSyntax:4"} JSON.API {
  function {:opaque} Serialize(js: Values.JSON) : Result<seq<byte>>
  method {:test} Test() {
  }
  lemma {:axiom} Assume(b: bool) ensures b
  type bytes32 = bs: seq<uint8> | |bs| < 10
  const Valid? := true
  function Int'(n: int): seq<uint8>

  class Vector<A> {
    const MAX_CAPACITY: uint32 := 100
    constructor(a0: A, initial_capacity: uint32 := 8)
  }
}
"""

    entities = _extract_entities(text, "JSON/API.dfy", SourceLanguage.DAFNY)
    names = {(entity["kind"], entity["name"]) for entity in entities}

    assert ("module", "JSON") in names
    assert ("function", "Serialize") in names
    assert ("method", "Test") in names
    assert ("lemma", "Assume") in names
    assert ("type", "bytes32") in names
    assert ("const", "Valid?") in names
    assert ("function", "Int'") in names
    assert ("class", "Vector") in names
    assert ("const", "MAX_CAPACITY") in names
    assert ("constructor", "constructor") in names
