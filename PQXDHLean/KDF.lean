/-
Key Derivation Function (KDF).

Definitions follow Bhargavan et al., USENIX Security 2024.
-/

/-- KDF mapping input material `I` (e.g. concatenated DH outputs)
to a fixed-size session key `K`. -/
structure KDF (I K : Type _) where
  derive : I → K
