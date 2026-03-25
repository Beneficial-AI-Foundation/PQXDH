/-
Abstract Authenticated Encryption with Associated Data (AEAD).

Reference: Bhargavan et al., §2.1 p. 470 and §2.5 p. 472 assumption (3).
-/

/-- §2.1, p. 470 "Session Secret Generation" and §2.5 p. 472, assumption 3:
Authenticated Encryption with Associated Data. Alice uses the session key
SKₐ to "encrypt a first message with an Authenticated Encryption with
Additional Data (AEAD), where the associated data includes an encoding
of IKₐᵖᵏ, IKᵦᵖᵏ". Parameterized by key type `K`, plaintext `PT`,
ciphertext `CT`, and associated data `AD`. The `correctness` field
guarantees that decrypting an honestly encrypted ciphertext with the correct
key and AD always succeeds.
Concrete instantiation: AES-256 in CBC mode with HMAC (Encrypt-Then-MAC).
The paper assumes IND-CPA + IND-CTXT (§2.5 assumption 3, p. 472). -/
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt

/-! ## Correctness theorems -/

/-- §2.1, p. 470: Decrypting an honestly encrypted ciphertext with the same
key and associated data recovers the original plaintext.
Direct consequence of the AEAD correctness axiom. -/
theorem AEAD_decrypt_encrypt {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k : K) (pt : PT) (ad : AD) :
    aead.decrypt k (aead.encrypt k pt ad) ad = some pt :=
  aead.correctness k pt ad

/-- §2.1, p. 470 "Completing the Handshake": If Alice and Bob share the
same session key and associated data (AD = IKₐᵖᵏ ‖ IKᵦᵖᵏ), Bob can
decrypt Alice's ciphertext. Models the handshake scenario where both
parties derive SKₐ = SK_B via the KDF. -/
theorem AEAD_agree {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k_a k_b : K) (pt : PT) (ad_a ad_b : AD) (ct : CT)
    (h_key : k_a = k_b) (h_ad : ad_a = ad_b)
    (h_enc : ct = aead.encrypt k_a pt ad_a) :
    aead.decrypt k_b ct ad_b = some pt := by
  subst h_key; subst h_ad; subst h_enc
  exact aead.correctness k_a pt ad_a
