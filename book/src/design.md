# Design

This page summarizes the main design decisions behind $\IronwoodProject$.

## Overview

### Goals

$\IronwoodProject$ introduces a new shielded pool without discarding the parts
of the Orchard protocol that are still useful. The design therefore separates
consensus state while reusing Orchard-shaped actions, proofs, receivers, and
wallet infrastructure where possible.

The result is the *Ironwood pool*, with a smaller implementation and deployment
surface than a fully independent shielded protocol.

### New Shielded Pool

The *Ironwood pool* is a new shielded value pool and value balance, based on the
Orchard protocol. This is consensus-relevant: transactions account for
*Ironwood-pool* value separately from the *Sapling* and *Orchard pools*.

Version 6 transactions support the following pools:

- transparent,
- *Sapling*,
- *Orchard*, and
- *Ironwood*.

Transaction version 6 is based on transaction version 5 and adds an
*Ironwood-pool* bundle. The transparent and *Sapling-pool* components are
unchanged from version 5. The *Orchard-pool* component is the same bundle
as in version 5, but version 6 changes how it is hashed and verified; see
[*Orchard-Pool* Bundle Changes in Version 6](#orchard-pool-bundle-changes-in-version-6).

## Pool State

### Separate State

The *Ironwood pool* has a separate note commitment tree and a separate nullifier
set.

This is the main boundary between the *Orchard* and *Ironwood pools*. Even though
an *Ironwood-pool* action has the Orchard action shape, its note commitments are
appended to the *Ironwood pool*'s tree, and its nullifiers are checked against the
*Ironwood pool*'s nullifier set.

This prevents the *Orchard* and *Ironwood pools* from sharing anonymity-set state
by accident, and gives a clean migration path away from legacy *Orchard-pool*
state.

### Chain History Tree

The chain history tree (the FlyClient MMR introduced in
[ZIP 221](https://zips.z.cash/zip-0221)) gains *Ironwood-pool* metadata. From
NU6.3 onward, history nodes use a new node-data version that, in addition to the
existing *Sapling-pool* and *Orchard-pool* fields, commits to:

- the *Ironwood pool*'s note commitment tree root at the start of the node's
  block range,
- the *Ironwood pool*'s note commitment tree root at the end of the node's block
  range, and
- the number of transactions in the range that contain an *Ironwood-pool* bundle.

The effect is that, from NU6.3 onward, the chain history commitment binds the
*Ironwood pool*'s tree state and *Ironwood-pool* activity of every block range,
just as it already binds the *Sapling* and *Orchard pools*.

## Actions and Notes

### *Ironwood-Pool* Bundle

The *Ironwood-pool* bundle reuses the Orchard-protocol action and bundle
structure. In the implementation this appears as a second Orchard-shaped bundle
in the transaction encoding.

This means the *Ironwood pool* inherits, from the Orchard protocol:

- the Orchard-protocol action layout;
- the Orchard-protocol authorization structure;
- the Orchard-protocol note encryption, modified for quantum recoverability;
- Orchard-protocol proof construction; and
- Orchard-protocol bundle padding behavior.

Quantum recoverability is the only note-level change for new *Ironwood-pool*
outputs. The rest of the bundle structure follows the Orchard protocol.

### Orchard Circuit Constraint

After NU6.3, the *Orchard pool* is constrained so that it can only remove value
from the *Orchard pool* or split existing *Orchard-pool* notes into change notes.
It must not allow new value to enter the *Orchard pool*.

This means the *Orchard pool* remains usable for legacy note handling:

- an *Orchard-pool* note can be withdrawn out of the *Orchard pool*;
- an *Orchard-pool* note can be split into multiple *Orchard-pool* change notes; and
- zero-balance *Orchard-pool* actions remain possible.

But transactions cannot use the *Orchard pool* as a destination for newly created
value. New shielded outputs that would previously have been *Orchard-pool*
outputs are routed to the *Ironwood pool* instead.

The "split into change notes" half of this constraint (requiring each retained
output to return to the address it was spent from) is enforced in the Action
circuit as the cross-address restriction. The "no new value" half is the
value-balance rule below. See [Action Circuit](design/action-circuit.md) for the
exact circuit mechanism.

### Quantum-Recoverable *Ironwood-Pool* Notes

ZIP 2005 defines a new Orchard-protocol note plaintext format with lead byte
$\mathtt{0x03}$: the quantum-recoverable note plaintext format. The *Ironwood pool*
adopts this format for its notes.

This gives the *Ironwood pool* a concrete note-level distinction while preserving
the Orchard keys and receiver handling. Wallet code can therefore model
*Ironwood-pool* notes as Orchard-shaped notes, but classify them by note plaintext
format:

- *Orchard-pool* notes use the existing note plaintext format, and
- *Ironwood-pool* notes use the quantum-recoverable note plaintext format.

When an *Ironwood-pool* note is spent, the witness is obtained from the *Ironwood
pool*'s note commitment tree, not the *Orchard pool*'s tree.

## Transaction Format and Hashing

### Version 6 Transaction Format

Transaction version 6 adds the *Ironwood-pool* bundle to the transaction format.
The bundle order is:

1. transparent bundle,
2. *Sapling-pool* bundle,
3. *Orchard-pool* bundle,
4. *Ironwood-pool* bundle.

The *Ironwood-pool* bundle uses the same Orchard-protocol bundle serialization as
the *Orchard-pool* bundle, but is interpreted in the *Ironwood-pool* context.

Version 6 is the default transaction version that wallets SHOULD use from NU6.3
activation. Transaction versions 4 and 5 remain valid.

### *Orchard-Pool* Bundle Changes in Version 6

The *Orchard-pool* bundle keeps its version 5 layout, but version 6 changes it in
three consensus-visible ways. Together these wind the *Orchard pool* down so that
it only supports transactions that take value out of the pool or that send it to
one of the expanded receivers spent from in the same transaction.

- **Flag encoding.** The flags byte gains a new `enableCrossAddress` flag (bit 2).
  After NU6.3 an *Orchard-pool* bundle must *not* set it: consensus rejects a
  version 6 *Orchard-pool* bundle that does, restricting *Orchard-pool* actions to
  change or withdrawal. An *Ironwood-pool* bundle, by contrast, may set it. See
  [Action Circuit](design/action-circuit.md).
- **Anchor placement.** For every supported pool (*Sapling*, *Orchard*, and *Ironwood*),
  the anchor is excluded from the version 6 txid and signature hash and is committed
  in the authorization digest instead. See [Transaction Hashing](#transaction-hashing).
- **Verifying key.** From NU6.3, *Orchard-pool* actions are verified with the
  post-NU6.3 circuit verifying key, which is selected by block height (not by
  transaction version), so that the cross-address restriction is enforceable on
  them. This binds *Orchard-pool* actions in version 5 transactions as well as
  version 6.

The Orchard-protocol action machinery is otherwise reused.

### Transaction Hashing

The *Ironwood-pool* bundle uses Orchard-protocol bundle and action hashing, but
with *Ironwood-pool*-specific personalization strings.

This applies to:

- *Ironwood-pool* bundle hashing,
- *Ironwood-pool* action compact hashing,
- *Ironwood-pool* action memo hashing,
- *Ironwood-pool* action non-compact hashing, and
- *Ironwood-pool* authorization hashing.

The version 6 transaction ID tree includes an *Ironwood-pool* component digest
after the *Orchard-pool* one. An empty *Ironwood-pool* bundle is represented by
its own empty-bundle digest, not by reusing the *Orchard-pool* empty-bundle
digest.

Version 6 signature hashing uses the version 6 transaction hash path. This ensures
signatures bind to the *Ironwood-pool* bundle when it is present.

The bundle anchor is excluded from version 6 txid and signature hashing, and is
committed in the authorization digest instead. Because the signature no longer
binds the anchor, a spend can be pre-signed before the anchor it is finalized
against exists. The anchor is still bound at the consensus layer, through the
block's authorizing-data commitment.

## Consensus Value Rules

### Post-NU6.3 *Orchard-Pool* Value Rule

After NU6.3 activation, no funds can flow into the *Orchard pool*. Transactions
must not have a negative *Orchard-pool* value balance.

The rule still permits:

- spending existing *Orchard-pool* value,
- positive *Orchard-pool* value balances, where value exits the *Orchard pool*,
  and
- zero-balance *Orchard-pool* actions.

This lets wallets spend existing *Orchard-pool* funds while preventing newly
created shielded value from being placed back into the *Orchard pool*.

### Coinbase After NU6.3

Because new value may not enter the *Orchard pool* after NU6.3, coinbase rules
change so that block rewards are never paid into it:

- **Empty Orchard component.** A coinbase transaction must contain no
  *Orchard-pool* actions at all. Coinbase reward outputs are routed to the
  *Sapling pool* or transparent receivers; the Orchard receiver is no longer a
  reward destination after NU6.3, and a miner address whose unified address
  contains *only* an Orchard receiver is rejected for coinbase use.
- **Coinbase value balance.** The coinbase balance check accounts for the
  *Ironwood-pool* value balance alongside the *Sapling* and *Orchard pools*, and
  *Ironwood-pool* coinbase outputs must be recoverable, as already required for
  the *Sapling* and *Orchard pools*, so that coinbase funds are not burned.
- **No coinbase spends.** A coinbase transaction must not enable spends in its
  *Ironwood-pool* bundle, mirroring the existing rule for the *Orchard pool*.

## Wallet and Tooling

### Wallet Routing

Wallet-created Orchard-receiver outputs are routed to the *Ironwood pool* after
NU6.3.

Before NU6.3, an Orchard receiver produces an *Orchard-pool* output. After NU6.3,
the same receiver produces an *Ironwood-pool* output using the quantum-recoverable
note plaintext format. Change follows the same rule: *Orchard-pool* change after
NU6.3 is emitted as *Ironwood-pool* change.

This allows legacy *Orchard-pool* notes to migrate out through ordinary spends
while ensuring new outputs land in the *Ironwood pool*.

Wallets must keep track of which pool a note is in (as they already need to do
for notes in the *Sapling* and *Orchard pools*), and use the appropriate anchor
and witness path when spending them.

### Wallet Storage And APIs

The *Ironwood pool* is exposed as a distinct pool in wallet-facing state, while
reusing Orchard-protocol note data internally.

Wallet storage tracks:

- *Ironwood-pool* note commitment tree metadata,
- *Ironwood-pool* shardtree state,
- *Ironwood-pool* nullifier observations,
- *Ironwood-pool* balances,
- *Ironwood-pool* Orchard-protocol received notes, and
- pool distinctions for sent and received outputs.

Compact block and lightwallet protocol data also grow *Ironwood-pool* fields:

- *Ironwood-pool* action data,
- *Ironwood-pool* note commitment tree size,
- *Ironwood-pool* tree state, and
- *Ironwood-pool* subtree roots.

This gives light clients enough information to maintain the *Ironwood pool*'s note
commitment tree and detect *Ironwood-pool* spends and outputs independently of the
*Orchard pool*.

### PCZT

Partially-created Zcash transactions include an *Ironwood-pool* bundle in the
updated PCZT format.

PCZT version 2 can carry:

- transparent data,
- *Sapling-pool* data,
- *Orchard-pool* data, and
- *Ironwood-pool* data.

The PCZT action fields also include the note plaintext version, because verifiers
and provers need it to reconstruct note commitments.

## Status

### Open Placeholders

The current design still has placeholders that should be finalized before a
production protocol specification:

- final activation heights and deployment rules.

The circuit and proof-system changes, previously open here, are now specified in
[Action Circuit](design/action-circuit.md). From NU6.3 a single Action circuit
version —the Orchard-protocol Action circuit plus one new constraint, the
cross-address restriction— is used for both the *Orchard* and *Ironwood pools*,
with its own proving and verifying keys.
