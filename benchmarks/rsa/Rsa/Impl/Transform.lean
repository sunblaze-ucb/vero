-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Rsa.Impl.Transform

The raw integer transformations at the heart of RSA. The two operations are
the modular exponentiations:

* `encryptInt m e n` = `m^e mod n`
* `decryptInt c d n` = `c^d mod n`

Types and signatures are fixed vocabulary (DO NOT MODIFY). Behaviour is
pinned by `Spec/Transform.lean`.
-/

namespace Rsa

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `encryptInt m e n`: the RSA integer encryption primitive — the modular
    exponentiation `m^e mod n` (Python `pow(m, e, n)`). -/
abbrev EncryptIntSig := Nat → Nat → Nat → Nat

/-- `decryptInt c d n`: the RSA integer decryption primitive — the modular
    exponentiation `c^d mod n` (Python `pow(c, d, n)`). -/
abbrev DecryptIntSig := Nat → Nat → Nat → Nat

end Rsa

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=encryptInt
-- !benchmark @end code_aux def=encryptInt

def Rsa.encryptInt : Rsa.EncryptIntSig :=
-- !benchmark @start code def=encryptInt
  fun m e n => (m ^ e) % n
-- !benchmark @end code def=encryptInt

-- !benchmark @start code_aux def=decryptInt
-- !benchmark @end code_aux def=decryptInt

def Rsa.decryptInt : Rsa.DecryptIntSig :=
-- !benchmark @start code def=decryptInt
  fun c d n => (c ^ d) % n
-- !benchmark @end code def=decryptInt
