/-
Abstract Key Derivation Function (KDF).

Reference: Bhargavan et al., §2.1 p. 470 and §2.5 p. 472–473 assumption (4).
-/

import Mathlib.Tactic.TypeStar

/-- §2.1, p. 470 "Session Secret Generation" and §2.5 p. 473, assumption 4:
Key Derivation Function. The three or four DH values are concatenated and
"used inside a Key Derivation Function (KDF) to obtain a session key SKₐ".
Maps variable-length input material `I` (concatenation of DH outputs, and
optionally the KEM shared secret) to a fixed-size session key `K`.
Concrete instantiation: HKDF-SHA-256 (RFC 5869). The paper assumes the KDF
is a Random Oracle (classical, §2.5 assumption 4) or a PRF (post-quantum). -/
structure KDF (I K : Type _) where
  derive : I → K
