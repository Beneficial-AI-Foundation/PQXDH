/-
Key Derivation Function (KDF).

Definitions follow Bhargavan et al., USENIX Security 2024.
-/
import VCVio.OracleComp.OracleSpec

open OracleSpec

/-- KDF modeled as a random oracle: an oracle `I →ₒ K` implemented
by VCV-io's `randomOracle` (lazy cached uniform sampling).
Parameterized by input type `I` and output type `K`. -/
abbrev KDFOracle (I K : Type) := I →ₒ K
