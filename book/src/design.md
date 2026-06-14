# Design

This page summarizes the main design decisions behind Ironwood.

## Goals

Ironwood is intended to introduce a new shielded pool without discarding the
parts of Orchard that are still useful. The design therefore separates
consensus state while reusing Orchard-shaped actions, proofs, receivers, and
wallet infrastructure where possible.

The result is a new pool with a smaller implementation and deployment surface
than a fully independent shielded protocol.

## New Shielded Pool

Ironwood is a new shielded value pool and value balance based on Orchard. This
is consensus-relevant: transactions account for Ironwood value separately from
Sapling and Orchard.

Version 6 transactions support the following pools:

- transparent,
- Sapling,
- Orchard, and
- Ironwood.

Transaction version 6 is the same as transaction version 5, except that it adds
an Ironwood bundle. Sapling, Orchard, and transparent transaction components are
otherwise unchanged from version 5.

## Separate State

Ironwood has a separate note commitment tree and a separate nullifier set.

This is the main boundary between Orchard and Ironwood. Even though an Ironwood
action has the Orchard action shape, its note commitments are appended to the
Ironwood tree, and its nullifiers are checked against the Ironwood nullifier
set.

This prevents Orchard and Ironwood from sharing anonymity-set state by accident
and gives the protocol a clean migration path away from legacy Orchard state.

## Orchard-Style Bundle

The Ironwood bundle reuses Orchard action and bundle structure. In the
implementation this appears as a second Orchard-shaped bundle with an Ironwood
bundle protocol marker.

This means Ironwood inherits:

- Orchard action layout,
- Orchard authorization structure,
- Orchard note encryption shape,
- Orchard proof construction, and
- Orchard bundle padding behavior.

Quantum recoverability is the only note-level change for new Ironwood outputs.
The rest of the bundle structure follows Orchard.

## Orchard Circuit Constraint

After NU7, Orchard is constrained so that it can only remove value from Orchard
or split existing Orchard notes into change notes. It must not allow new value
to enter Orchard.

This means Orchard remains usable for legacy note handling:

- an Orchard note can be withdrawn out of Orchard,
- an Orchard note can be split into multiple Orchard change notes, and
- zero-balance Orchard actions remain possible.

But transactions cannot use Orchard as a destination for newly created value.
New shielded outputs that would previously have been Orchard outputs are routed
to Ironwood instead.

The "split into change notes" half of this constraint (requiring each retained
output to return to the address it was spent from) is enforced in the Action
circuit as the cross-address restriction. The "no new value" half is the
value-balance rule below. See [Action Circuit](design/action-circuit.md) for the
exact circuit mechanism.

## Quantum-Recoverable Ironwood Notes

ZIP 2005 defines a new Orchard note plaintext format with lead byte `0x03`: the
quantum-recoverable note plaintext format. Ironwood adopts this format for its
notes.

This gives Ironwood a concrete note-level distinction while preserving Orchard
keys and receiver handling. Wallet code can therefore model Ironwood notes as
Orchard-shaped notes, but classify them by note plaintext format:

- Orchard notes use the existing Orchard note plaintext format,
- Ironwood notes use the Ironwood / QR note plaintext format.

When an Ironwood note is spent, the witness is obtained from the Ironwood note
commitment tree, not the Orchard tree.

## Version 6 Transaction Format

Transaction version 6 adds the Ironwood bundle to the transaction format. The
bundle order is:

1. transparent bundle,
2. Sapling bundle,
3. Orchard bundle,
4. Ironwood bundle.

The Ironwood bundle uses the same Orchard-style bundle serialization as the
Orchard bundle, but is interpreted under the Ironwood protocol context.

Version 6 is the default transaction version for NU7. Version 5 remains the
transaction version for NU5 through NU6.2.

## Transaction Hashing

Ironwood uses Orchard-style bundle and action hashing, but with
Ironwood-specific personalization strings.

This applies to:

- Ironwood bundle txid hashing,
- Ironwood action compact hashing,
- Ironwood action memo hashing,
- Ironwood action non-compact hashing, and
- Ironwood authorization hashing.

The version 6 transaction ID tree includes an Ironwood digest after the Orchard
digest. Empty Ironwood bundles are represented by the Ironwood empty-bundle
digest, not by reusing Orchard's empty-bundle digest.

Version 6 signature hashing uses the version 6 transaction hash path. This
ensures signatures bind to the Ironwood bundle when it is present.

## Post-NU7 Orchard Value Rule

After NU7 activation, no funds can flow into Orchard. Transactions must not have
a negative Orchard value balance.

The rule still permits:

- spending existing Orchard value,
- positive Orchard value balances, where value exits Orchard, and
- zero-balance Orchard actions.

This lets wallets spend existing Orchard funds while preventing newly created
shielded value from being placed back into Orchard.

## Wallet Routing

Wallet-created Orchard receiver outputs are routed to Ironwood after NU7.

Before NU7, an Orchard receiver produces an Orchard output. After NU7, the same
receiver produces an Ironwood output using the QR note plaintext format.
Change follows the same rule: Orchard change after NU7 is emitted as Ironwood
change.

When spending notes, wallets split Orchard-shaped notes by note plaintext
format:

- Orchard notes use the Orchard anchor and Orchard witness path,
- Ironwood notes use the Ironwood anchor and Ironwood witness path.

This allows legacy Orchard notes to migrate out through ordinary spends while
ensuring new outputs land in Ironwood.

## Wallet Storage And APIs

Ironwood is exposed as a distinct pool in wallet-facing state, while reusing
Orchard-shaped note data internally.

Wallet storage tracks:

- Ironwood tree metadata,
- Ironwood shardtree state,
- Ironwood nullifier observations,
- Ironwood balances,
- Ironwood Orchard-shaped received notes, and
- pool-code distinctions for sent and received outputs.

Compact block and lightwallet protocol data also grow Ironwood fields:

- Ironwood action data,
- Ironwood commitment tree size,
- Ironwood tree state, and
- Ironwood subtree roots.

This gives light clients enough information to maintain the Ironwood note
commitment tree and detect Ironwood spends and outputs independently of Orchard.

## PCZT

Partially-created Zcash transactions include an Ironwood bundle in the updated
PCZT format.

PCZT version 2 can carry:

- transparent data,
- Sapling data,
- Orchard data, and
- Ironwood data.

The PCZT Orchard action fields also include note plaintext version, because
verifiers and provers need the note version to reconstruct note commitments.

## Open Placeholders

The current design still has placeholders that should be finalized before a
production protocol specification:

- the NU7 consensus branch ID,
- final ZIP text for transaction version 6 and Ironwood hashing, and
- final activation heights and deployment rules.

The circuit and proof-system changes, previously open here, are now specified in
[Action Circuit](design/action-circuit.md): Ironwood reuses the Orchard Action
circuit and adds a single new constraint, the cross-address restriction, with its
own proving and verifying keys.
