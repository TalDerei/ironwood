import Zcash.Snark.Fixture

/-!
# Fiat–Shamir schedule check: the FS-derived fingerprint matches the capture

The captured fingerprint match (`Zcash.Snark.Fixture.fingerprint_matches`) checks the assembled MSM at the
captured challenges `ch`. On its own that leaves the Fiat–Shamir schedule unchecked — a wrong
`deriveChallenges` could not be caught, because the fixture never evaluates it.

This module connects the Fiat–Shamir-derived fingerprint (`nonInteractiveFingerprint`, i.e. `assemble` at
`deriveChallenges`) to the same captured MSM, modulo one explicit assumption: that the deployed FS schedule
reproduces the captured challenges. The squeeze (Blake2b) is the random-oracle hand-wave — not modeled in
Lean — so `deriveChallenges fs init ps = ch` is that named assumption. The schedule's structure (the
absorb/squeeze order) is auditable directly against `plonk/verifier.rs` in `deriveChallenges`'s definition.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark

/-- The Fiat–Shamir-derived fingerprint matches the captured MSM, given that the deployed FS schedule
produces the captured challenges (`hch` — the random-oracle assumption, the one part of FS that depends
on the unmodeled hash). So the schedule `deriveChallenges` is now on the path to the capture, with its
hash-dependent output isolated as `hch`: a wrong FS schedule (wrong absorb/squeeze structure) no longer
trivially escapes the fixture, since `nonInteractiveFingerprint` (which uses the schedule) is what is
matched. -/
theorem nonInteractiveFingerprint_matches (fs : FiatShamir Fp G) (init : List (TranscriptElt Fp G))
    (hch : deriveChallenges fs init ps = ch) :
    MsmMatch (nonInteractiveFingerprint fs init vk ps) capturedMsm := by
  unfold nonInteractiveFingerprint
  rw [hch]
  exact fingerprint_matches

end Zcash.Snark.Fixture
