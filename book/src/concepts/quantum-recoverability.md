# Quantum Recoverability

Quantum recoverability is the note-level change that defines *Ironwood-pool*
notes. It does not make the current Orchard protocol post-quantum. Instead, it
changes how new *Ironwood-pool* notes are created so they can be recovered into a
future shielded protocol if the current elliptic-curve-based protocol ever has to
be disabled.

The threat model is supply integrity. If an attacker can break discrete logarithms
on the curves used by Zcash, then the existing *Sapling-pool* and *Orchard-pool*
note commitments are not binding against that attacker. Even if Zcash later
upgraded its proof system and rebuilt note commitments with a post-quantum hash,
an attacker could otherwise try to forge a note that was not actually in the
commitment tree.

Quantum-recoverable notes address this by changing how note commitment
randomness is derived.

## *Ironwood-Pool* Notes

ZIP 2005 defines a new Orchard-protocol note plaintext format with lead byte
$\mathtt{0x03}$: the quantum-recoverable note plaintext format. The *Ironwood pool*
adopts this format for its notes. ZIP 2005 defines and analyses this new format
and how it is used; it does not by itself define the *Ironwood pool*, or its
note commitment tree or nullifier set. Those are layered on top of the ZIP 2005
note-level change.

*Orchard-pool* notes still use note plaintext lead byte $\mathtt{0x02}$. For
those notes, the note commitment randomness is derived only from $\rseed$
and $\noteRho$. $\rseed$ is the 32-byte random seed the sender picks for a note.
When a note is created, its $\noteRho$ is set to $\nfOld$, the nullifier of the
input note spent in the same action (the nullifier that action reveals).

For *Ironwood-pool* notes, the randomness is instead derived from the entire note
contents. The derivation binds the randomness to:

- the diversifier-derived point,
- the recipient public key,
- the note value,
- $\noteRho$, and
- the note-specific $\notePsi$ value.

In effect, the note contents become part of the randomness derivation.

```mermaid
flowchart LR
    subgraph V2["Orchard-pool note"]
        V2Inputs["$\rseed, \noteRho$"] --> V2Rcm["$\rcm$"]
    end

    subgraph Ironwood["Ironwood-pool (QR) note"]
        IronwoodInputs["$\rseed, \gd, \pkd, \value, \noteRho, \notePsi$"] --> IronwoodRcm["$\rcm$"]
    end

    IronwoodRcm --> Future["future recovery statement can check derivation"]
```

This makes it possible for a future recovery protocol to prove that a recovered
note corresponds to a real note with fixed contents, rather than to a forged
choice of note fields. Because $\rcm$ is now a hash of the note contents, the
derivation can be recomputed from the recovered fields and checked against the
on-chain commitment. The *Ironwood-pool* spend proof does not itself enforce this
derivation; the check is instead carried out by a future, dedicated recovery
statement that proves $\rcm$ was derived from the note contents.

*Ironwood-pool* outputs are Orchard-shaped notes using the quantum-recoverable
note plaintext format. The *Ironwood pool* still uses Orchard-shaped actions,
receivers, and note encryption. The distinction is that *Ironwood-pool* notes use
the quantum-recoverable note plaintext format, are committed into the *Ironwood
pool*'s note commitment tree, and are spent against the *Ironwood pool*'s
nullifier set.

## What This Does Not Do

Quantum recoverability is not a post-quantum shielded protocol by itself.

It does not:

- make current Orchard-protocol spends post-quantum secure,
- define the future recovery protocol in full,
- choose a future post-quantum proof system, or
- choose a future post-quantum note commitment tree.

It is a forward-compatibility change. The goal is to make funds created as
recoverable notes usable by a later recovery protocol, without requiring Zcash
to choose that future protocol today.

## Why This Matters For Ironwood

The *Ironwood pool* is where newly created shielded value goes after NU6.3.
Using *Ironwood-pool* notes means new *Ironwood-pool* funds are created in the
recoverable format from the start.

This gives Zcash a migration path: existing value can be moved into the *Ironwood
pool*, and *Ironwood-pool* notes are structured so that a future post-quantum
transition has the information it needs to recover those funds.

Further reading:

- [ZIP 2005: Ironwood Quantum Recoverability](https://zips.z.cash/zip-2005)
