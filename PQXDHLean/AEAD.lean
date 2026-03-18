/-
Abstract Authenticated Encryption with Associated Data (AEAD).

An AEAD scheme provides both confidentiality and integrity for a
plaintext message, while binding the ciphertext to unencrypted
associated data (AD). In X3DH/PQXDH:

  - The session key SK (derived by the KDF) is the AEAD key.
  - Alice encrypts her first message ("hello") using SK.
  - The associated data AD = IKₐᵖᵏ ‖ IKᵦᵖᵏ binds the ciphertext
    to both parties' identities, preventing key-mismatch attacks.

## Security assumptions (§2.5, assumption 3)

The concrete instantiation is AES-256 in CBC mode with HMAC
(Encrypt-Then-Mac). The paper assumes:

  - **IND-CPA** (Indistinguishability under Chosen-Plaintext Attack):
    ciphertexts reveal nothing about the plaintext.
  - **IND-CTXT** (Integrity of Ciphertext):
    an adversary cannot forge a valid ciphertext.

Together, IND-CPA + IND-CTXT imply IND-CCA2 for AEAD schemes.

## Abstract interface

We model AEAD with encrypt and decrypt operations. Encryption is
deterministic given a nonce (which we fold into the key for
abstraction). Decryption returns `Option PT` to model authentication
failure: `none` means the ciphertext or AD was tampered with.

Reference: Bhargavan et al., §2.1 and §2.5 assumption (3).
-/

/-! ## AEAD structure -/

-- ANCHOR: AEADStructure
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt
-- ANCHOR_END: AEADStructure

/-! ## Correctness theorems -/

-- ANCHOR: AEADDecryptEncrypt
theorem AEAD_decrypt_encrypt {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k : K) (pt : PT) (ad : AD) :
    aead.decrypt k (aead.encrypt k pt ad) ad = some pt :=
  aead.correctness k pt ad
-- ANCHOR_END: AEADDecryptEncrypt

-- ANCHOR: AEADAgree
theorem AEAD_agree {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k_a k_b : K) (pt : PT) (ad_a ad_b : AD) (ct : CT)
    (h_key : k_a = k_b) (h_ad : ad_a = ad_b)
    (h_enc : ct = aead.encrypt k_a pt ad_a) :
    aead.decrypt k_b ct ad_b = some pt := by
  subst h_key; subst h_ad; subst h_enc
  exact aead.correctness k_a pt ad_a
-- ANCHOR_END: AEADAgree
