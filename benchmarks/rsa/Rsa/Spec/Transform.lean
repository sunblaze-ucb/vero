import Rsa.Harness

/-!
# Rsa.Spec.Transform

Specifications for the RSA integer transformations `encryptInt` and
`decryptInt`. Each `spec_*` is a property over an arbitrary `impl : RepoImpl`;
an API is always reached through `impl.rsa.<fn>`, never by calling the
reference `Rsa.<fn>` directly.

`encryptInt` and `decryptInt` are each specified independently as their own
modular-exponentiation residue `(base ^ exp) % n`, a value in `[0, n)`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ════════════════════════════════════════════════════════════════
-- encrypt / decrypt: independent frozen modular-exponentiation residues
-- ════════════════════════════════════════════════════════════════

/-- `encryptInt` is exactly the modular exponentiation `(m^e) % n`. -/
def spec_encrypt_int_correct (impl : RepoImpl) : Prop :=
  ∀ (m e n : Nat), impl.rsa.encryptInt m e n = (m ^ e) % n

/-- `decryptInt` is exactly the modular exponentiation `(c^d) % n`. -/
def spec_decrypt_int_correct (impl : RepoImpl) : Prop :=
  ∀ (c d n : Nat), impl.rsa.decryptInt c d n = (c ^ d) % n

/-- `%`-stability of encryption: reducing the message modulo `n` before
    encrypting does not change the cyphertext —
    `encryptInt (m % n) e n = encryptInt m e n`. -/
def spec_encrypt_mod_message (impl : RepoImpl) : Prop :=
  ∀ (m e n : Nat), impl.rsa.encryptInt (m % n) e n = impl.rsa.encryptInt m e n

/-- Encryption range: a positive modulus bounds the cyphertext —
    `encryptInt m e n < n` for `n > 0`. -/
def spec_encrypt_range (impl : RepoImpl) : Prop :=
  ∀ (m e n : Nat), 0 < n → impl.rsa.encryptInt m e n < n

/-- Decryption range: `decryptInt c d n < n` for `n > 0`. -/
def spec_decrypt_range (impl : RepoImpl) : Prop :=
  ∀ (c d n : Nat), 0 < n → impl.rsa.decryptInt c d n < n

/-- Exponent-one identity: `encryptInt m 1 n = m % n`. -/
def spec_encrypt_exp_one (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat), impl.rsa.encryptInt m 1 n = m % n

/-- Concrete vector: `encryptInt 2 10 1000 = 24` (`2^10 = 1024 ≡ 24 mod 1000`). -/
def spec_encrypt_vec (impl : RepoImpl) : Prop :=
  impl.rsa.encryptInt 2 10 1000 = 24

-- ════════════════════════════════════════════════════════════════
-- Multiplicative / compositional laws of the modular power
-- ════════════════════════════════════════════════════════════════

/-- Multiplicativity of encryption in the base: encrypting a product is the
    product of the cyphertexts, reduced modulo `n` —
    `(encryptInt a e n * encryptInt b e n) % n = encryptInt (a * b) e n`. -/
def spec_encrypt_mul_base (impl : RepoImpl) : Prop :=
  ∀ (a b e n : Nat),
    (impl.rsa.encryptInt a e n * impl.rsa.encryptInt b e n) % n
      = impl.rsa.encryptInt (a * b) e n

/-- Exponent additivity of encryption: splitting the exponent factors the
    cyphertext —
    `encryptInt m (e₁ + e₂) n = (encryptInt m e₁ n * encryptInt m e₂ n) % n`. -/
def spec_encrypt_exp_add (impl : RepoImpl) : Prop :=
  ∀ (m e₁ e₂ n : Nat),
    impl.rsa.encryptInt m (e₁ + e₂) n
      = (impl.rsa.encryptInt m e₁ n * impl.rsa.encryptInt m e₂ n) % n

/-- Base-congruence stability: two messages agreeing modulo `n` encrypt to the
    same cyphertext — `a % n = b % n → encryptInt a e n = encryptInt b e n`. -/
def spec_encrypt_base_congr (impl : RepoImpl) : Prop :=
  ∀ (a b e n : Nat),
    a % n = b % n → impl.rsa.encryptInt a e n = impl.rsa.encryptInt b e n

/-- Encrypt/decrypt composition: applying `decryptInt … d n` to a cyphertext
    `encryptInt m e n` equals the modular exponentiation by the product of the
    exponents — `decryptInt (encryptInt m e n) d n = (m ^ (e * d)) % n` (the
    right-hand power is the spec's own ground truth; it never mentions
    `impl`). -/
def spec_decrypt_encrypt_compose (impl : RepoImpl) : Prop :=
  ∀ (m e d n : Nat),
    impl.rsa.decryptInt (impl.rsa.encryptInt m e n) d n = (m ^ (e * d)) % n

/-- Iterated-encryption exponent fusion: re-encrypting a message through a
    whole list of exponents — starting from the reduced seed `m % n` and
    folding `encryptInt · eᵢ n` left-to-right — equals a single encryption
    whose exponent is the product of the list —
    `exps.foldl (fun c e => encryptInt c e n) (m % n)
       = encryptInt m (exps.foldl (·*·) 1) n`. -/
def spec_encrypt_chain_exps (impl : RepoImpl) : Prop :=
  ∀ (m n : Nat) (exps : List Nat),
    exps.foldl (fun c e => impl.rsa.encryptInt c e n) (m % n)
      = impl.rsa.encryptInt m (exps.foldl (· * ·) 1) n
