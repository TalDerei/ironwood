# Quantum Recoverability

Quantum recoverability is the note-level change that defines Ironwood notes. It
does not make the current Orchard-style protocol post-quantum. Instead, it
changes how new Orchard-style notes are created so they can be recovered into a
future shielded protocol if the current elliptic-curve-based protocol ever has
to be disabled.

The threat model is supply integrity. If an attacker can break discrete
logarithms on the curves used by Zcash, then the existing Sapling and Orchard
note commitments are not binding against that attacker. Even if Zcash later
upgraded its proof system and rebuilt note commitments with a post-quantum hash,
an attacker could otherwise try to forge a note that was not actually in the
commitment tree.

Quantum-recoverable notes address this by changing how note commitment
randomness is derived.

## Ironwood Notes

ZIP 2005 defines a new note plaintext format with lead byte `0x03`: the
quantum-recoverable note plaintext format. Ironwood adopts this format for its
notes. ZIP 2005 changes how Orchard notes are constructed; it does not by itself
define the Ironwood pool, note commitment tree, or nullifier set. Those are
Ironwood's own design, layered on top of the ZIP 2005 note-level change.

Older Orchard notes use note plaintext lead byte `0x02`. For those notes, the note
commitment randomness is derived from `rseed` and `rho`. `rseed` is the 32-byte
random seed the sender picks for a note. When a note is created, its `rho` is
set to `nf^old`, the nullifier of the input note spent in the same action (the
nullifier that action reveals).

For Ironwood notes, the randomness is instead derived from the note contents. The
derivation binds the randomness to:

- the diversifier-derived point,
- the recipient public key,
- the note value,
- `rho`, and
- the note-specific `psi` value.

In effect, the note contents become part of the randomness derivation.

```mermaid
flowchart LR
    subgraph V2["Orchard note"]
        V2Inputs["rseed, rho"] --> V2Rcm["rcm"]
    end

    subgraph Ironwood["Ironwood / QR note"]
        IronwoodInputs["rseed, gd, pkd, value, rho, psi"] --> IronwoodRcm["rcm"]
    end

    IronwoodRcm --> Future["future recovery statement can check derivation"]
```

This makes it possible for a future recovery protocol to prove that a recovered
note corresponds to a real note with fixed contents, rather than to a forged
choice of note fields. Because `rcm` is now a hash of the note contents, the
derivation can be recomputed from the recovered fields and checked against the
on-chain commitment. The Ironwood spend proof does not itself enforce this
derivation; the check is instead carried out by a future, dedicated recovery
statement that proves `rcm` was derived from the note contents.

Ironwood outputs are Orchard-style notes using the Ironwood note plaintext
format. Ironwood still uses Orchard-shaped actions, receivers, and note
encryption. The distinction is that Ironwood notes use the QR note plaintext
format, are committed into the Ironwood note commitment tree, and are spent
against the Ironwood nullifier set.

## What This Does Not Do

Quantum recoverability is not a post-quantum shielded protocol by itself.

It does not:

- make current Orchard-style spends post-quantum secure,
- define the future recovery protocol in full,
- choose a future post-quantum proof system, or
- choose a future post-quantum note commitment tree.

It is a forward-compatibility change. The goal is to make funds created as
recoverable notes usable by a later recovery protocol, without requiring Zcash
to choose that future protocol today.

## Why This Matters For Ironwood

Ironwood is the pool where new Orchard-style shielded value goes after NU6.3.
Using Ironwood notes means new Ironwood funds are created in the recoverable
format from the start.

This gives Zcash a migration path: existing value can be moved into Ironwood,
and Ironwood notes are structured so that a future post-quantum transition has
the information it needs to recover those funds.

Further reading:

- [ZIP 2005: Orchard Quantum Recoverability](https://zips.z.cash/zip-2005)
