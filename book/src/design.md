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

Transaction version 6 is based on transaction version 5 and adds an Ironwood
bundle. Transparent and Sapling components are unchanged from version 5. The
Orchard component is the same Orchard bundle, but version 6 changes how it is
encoded, hashed, and verified; see
[Orchard Bundle Changes in Version 6](#orchard-bundle-changes-in-version-6).

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

## Orchard Bundle Changes in Version 6

The Orchard bundle keeps its version 5 layout, but version 6 changes it in three
consensus-visible ways. Together these wind Orchard down into a spend-only,
same-address pool while reusing its action machinery.

- **Flag encoding.** Orchard bundle flags are serialized in the NU6.3 flag
  format, which gives meaning to the `enableCrossAddress` flag (bit 2). In
  version 5 that bit is reserved and must be zero. After NU7 an Orchard bundle
  must *not* set `enableCrossAddress`: consensus rejects a version 6 Orchard
  bundle that sets it, which forces the circuit's `disableCrossAddress` input and
  restricts Orchard actions to change or withdrawal. Ironwood, by contrast, may
  set `enableCrossAddress`. See [Action Circuit](design/action-circuit.md).
- **Anchor placement.** The Orchard anchor is excluded from the version 6 txid
  and signature hash and is committed in the authorization digest instead, the
  same as Ironwood. See [Transaction Hashing](#transaction-hashing).
- **Verifying key.** Version 6 Orchard bundles are verified with the Ironwood
  circuit verifying key, not the version 5 (post-NU6.2) key, because the
  cross-address restriction must be enforceable on Orchard actions.

<<<<<<< HEAD
## ZIP 233 in Version 6

Version 6 transactions do not carry a ZIP 233 explicit-fee (burn) field. ZIP 233
handling is confined to the experimental `zfuture` path and is not part of the
NU7 version 6 format. NU7 and `zfuture` are mutually exclusive deployments and
cannot be enabled together.

## Transaction Hashing
=======
### Transaction Hashing
>>>>>>> 128e1e6 (nit remove)

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

The bundle anchor is excluded from version 6 txid and signature hashing, and is
committed in the authorization digest instead. Because the signature no longer
binds the anchor, a spend can be pre-signed before the anchor it is finalized
against exists. The anchor is still bound at the consensus layer, through the
block's authorizing-data commitment.

## Chain History Tree

The chain history tree (the FlyClient MMR introduced in
[ZIP 221](https://zips.z.cash/zip-0221)) gains Ironwood metadata. From NU7
onward, history nodes use a new node-data version that, in addition to the
existing Sapling and Orchard fields, commits to:

- the Ironwood note commitment tree root at the start of the node's block range,
- the Ironwood note commitment tree root at the end of the node's block range,
  and
- the number of transactions in the range that contain an Ironwood bundle.

A leaf's start and end Ironwood roots are both the final Ironwood tree root after
its block. Combining two subtrees takes the left child's start root, the right
child's end root, and the sum of the two transaction counts, and the maximum
history node-data size grows to hold the new fields. The effect is that, from
NU7 onward, the chain history commitment binds the Ironwood tree state and
Ironwood activity of every range, just as it already binds Sapling and Orchard.

## Post-NU7 Orchard Value Rule

After NU7 activation, no funds can flow into Orchard. Transactions must not have
a negative Orchard value balance.

The rule still permits:

- spending existing Orchard value,
- positive Orchard value balances, where value exits Orchard, and
- zero-balance Orchard actions.

This lets wallets spend existing Orchard funds while preventing newly created
shielded value from being placed back into Orchard.

## Coinbase After NU7

Because new value may not enter Orchard after NU7, coinbase rules change so that
block rewards are never paid into the Orchard pool:

- **No Orchard coinbase outputs.** Coinbase reward outputs are routed to Sapling
  or transparent receivers; the Orchard receiver is no longer a reward
  destination after NU7. A miner address whose unified address contains *only* an
  Orchard receiver is therefore rejected for coinbase use.
- **Coinbase value balance includes Ironwood.** The coinbase balance check
  accounts for the Ironwood value balance alongside Sapling and Orchard. Any
  Ironwood output in a coinbase transaction must be decryptable with the all-zero
  outgoing viewing key, as already required for Sapling and Orchard, so that
  coinbase funds are not burned.
- **No coinbase spends.** A coinbase transaction must not enable spends in its
  Ironwood bundle (`EnableSpendsIronwood` must be unset), mirroring the existing
  rule for Orchard.

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
