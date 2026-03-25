/-
Abstract Key Encapsulation Mechanism (KEM).

Reference: Bhargavan et al., §2.3 p. 471–472 and §2.5 p. 472 assumption (1.B).
-/

/-- §2.3, p. 472 and Figure 1, p. 471, §2.5 p. 472 assumption 1.B:
Key Encapsulation Mechanism. In the PQXDH protocol (Figure 1), Alice
computes "CT, SS ← KEM.encaps(PQSPKᵦᵖᵏ)" and Bob computes
"SS = KEM.decaps(CT, PQSPKᵦˢᵏ)". Parameterized by public key `PK`,
secret key `SK_kem`, ciphertext `CT`, and shared secret `SS`.
The `correctness` field guarantees that honest encaps/decaps round-trips.
Concrete instantiation: Kyber-1024 (ML-KEM). The paper assumes the KEM
is IND-CCA (§2.5 assumption 1.B, p. 472). -/
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss

/-- §2.3, p. 472: If encapsulation produces (ct, ss), then decapsulation
with the corresponding secret key recovers ss. Direct consequence of the
KEM correctness axiom. -/
theorem KEM_decaps_encaps {PK SK_kem CT SS : Type _} (kem : KEM PK SK_kem CT SS)
    (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS)
    (h : kem.encaps pk = (ct, ss)) :
    kem.decaps sk ct = ss :=
  kem.correctness pk sk ct ss h
