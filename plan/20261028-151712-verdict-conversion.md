# Issue #5

Repair the conversion task boundary and source correspondence independently of the incomplete policy reference implementations. Preserve meaningful success/failure behavior, synchronize manifest/bundle/spec callers, and add positive and negative conversion checks.

Base: origin/main at 0a7325df9e9e6dbc275c0ad483b3d1cbe38d9b09. One independent branch and draft PR for this issue. Use curator/source material only, not private submitted proof artifacts. Keep the grader timeout and axiom policy unchanged. Run regression checks and required Ruff checks before committing.

Source review: the current parser model omits upstream version, extension, and conversion data required by the full reference. This draft implements a temporary curator hold using the existing spec_helpers/requires_human_review vocabulary, rather than inventing missing certificate fields or trusting unproved preservation laws. The full source port and re-scoring remain open.
