# Concepts

$\IronwoodProject$ is the project to deploy a new shielded value pool for Zcash: the
*Ironwood pool*. The *Ironwood pool* reuses the Orchard protocol —the Orchard
action shape, keys, and proof system— while keeping its own state, separate from
the *Orchard pool*, and using a new note plaintext format for quantum-recoverable
notes.

At a high level, $\IronwoodProject$ introduces:

- a new shielded value pool and value balance, the *Ironwood pool*, with its
  own note commitment tree and nullifier set but reusing the Orchard protocol;
- transaction version 6, which is version 5 with an *Ironwood-pool* bundle added;
- quantum-recoverable note plaintexts for *Ironwood-pool* notes;
- a rule that no funds can flow into the *Orchard pool* after NU6.3; and
- a circuit update that lets *Orchard-pool* notes be withdrawn or split into
  change notes, without allowing new value to enter that pool.

## Relationship To Orchard

We distinguish the Orchard protocol —the shared action shape, keys, proof
system, and note machinery— from the *Orchard pool* and the *Ironwood pool*, the
two value pools that use it. Each pool has its own note commitment tree,
nullifier set, and value balance.

The *Ironwood pool* reuses the Orchard protocol's action and zero-knowledge proof
structure. This keeps the transition smaller than introducing an entirely new
shielded protocol from first principles.

The important distinction is that the *Ironwood pool* is not "more *Orchard-pool*
state". It has its own value balance, note commitment tree, and nullifier set. An
*Ironwood-pool* note is represented with Orchard-protocol note machinery, but it
is committed into the *Ironwood pool*'s note commitment tree and spent against the
*Ironwood pool*'s nullifier set.

This lets the existing Orchard receiver and viewing-key infrastructure remain
useful while creating a clean state boundary between legacy *Orchard-pool* funds
and *Ironwood-pool* funds.

## Quantum-Recoverable Notes

ZIP 2005 defines a new Orchard-protocol note plaintext format with lead byte
$\mathtt{0x03}$: the quantum-recoverable note plaintext format. The *Ironwood pool*
adopts this format for its notes.

In wallet-facing code, *Ironwood-pool* notes are Orchard-shaped notes using the
quantum-recoverable note plaintext format. The note plaintext format of
*Orchard-pool* notes remains unchanged. *Ironwood-pool* notes use that pool's
treestate when they are spent.

## Transaction Version 6

A new transaction format, version 6, is introduced in order to add an
*Ironwood-pool* bundle. There are no other transaction format changes from v5
(there is a change to the signature hashing needed to support [anchor update](#anchor-update)).

A version 6 transaction can contain:

- transparent inputs and outputs,
- bundles for each of the *Sapling*, *Orchard*, and *Ironwood* pools.

The *Sapling-pool* and transparent components are unchanged from version 5. The
*Orchard-pool* and *Ironwood-pool* bundles follow the same Orchard-protocol
bundle structure, but they are separate bundles in the transaction. The
*Ironwood-pool* bundle uses different personalization strings for its transaction
and authorization hashes.

## Value Movement After NU6.3

After NU6.3 activation, no funds can flow into the *Orchard pool*. Transactions
can still spend *Orchard-pool* funds, and zero-balance *Orchard-pool* actions are
still allowed, but the *Orchard pool*'s value balance must not be negative.

Wallet-created payments and change that would previously have produced
*Orchard-pool* outputs are routed to the *Ironwood pool* after NU6.3. This moves
newly created shielded value into the *Ironwood pool* while still allowing legacy
*Orchard-pool* notes to be spent.
