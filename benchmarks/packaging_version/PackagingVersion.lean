import PackagingVersion.Impl.Version
import PackagingVersion.Bundle
import PackagingVersion.Harness
import PackagingVersion.Spec.Version
import PackagingVersion.Test

/-!
# PackagingVersion

Root import hub for the version-ordering benchmark. A `Ver` is an already-parsed
version — an epoch, a release tuple, and a single pre/post/dev tag. The API is
the comparator family (`verLe` / `verEq`), the extremal queries (`maxVer` /
`minVer`), and a canonical sort (`sortVers`). Behaviour is pinned by
`Spec/Version.lean`.

Scope: the comparator core only. There is no version-string parser, and local
labels together with combined pre/post/dev qualifiers are out of scope.
-/
