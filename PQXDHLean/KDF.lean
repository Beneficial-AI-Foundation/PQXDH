/-
Key Derivation Function (KDF).

Two formalizations coexist, modeling different aspects of the KDF:

- `KDF` (structure): a deterministic function `derive : I → K`.
  Used in the *correctness* proofs (X3DH_agree, X3DH_handshake_correct),
  which only need "same input → same output" — no randomness or
  security assumptions.

- `KDFOracle` (abbrev): an oracle `I →ₒ K` implemented by VCV-io's
  `randomOracle` (lazy cached uniform sampling). Used in the
  *security* proofs (passive message secrecy), where the KDF is
  modeled as a random oracle per the paper's assumption 4 (§2.5).

The paper makes the same distinction: correctness is unconditional,
security assumes the ROM.

Definitions follow Bhargavan et al., USENIX Security 2024.
-/
import VCVio.OracleComp.OracleSpec

open OracleSpec

/-- KDF as a deterministic function, for correctness proofs. -/
structure KDF (I K : Type _) where
  derive : I → K

/-- KDF as a random oracle, for security proofs. -/
abbrev KDFOracle (I K : Type) := I →ₒ K
