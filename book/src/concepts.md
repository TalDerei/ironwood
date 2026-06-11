# Concepts

Ironwood is a proposed new shielded value pool for Zcash. It is designed as an
Orchard successor pool: it keeps the Orchard action shape, keys, and proof
system, while separating Ironwood state from Orchard state and using a new note
plaintext format for quantum-recoverable notes.

At a high level, Ironwood introduces:

- a new shielded value pool and value balance based on Orchard,
- a new note commitment tree and nullifier set,
- transaction version 6, which is version 5 with an Ironwood bundle added,
- Ironwood quantum-recoverable note plaintexts,
- a rule that no funds can flow into Orchard after NU7, and
- a circuit update that lets Orchard notes be withdrawn or split into change
  notes, without allowing new value to enter Orchard.

## Relationship To Orchard

Ironwood reuses the Orchard action and zero-knowledge proof structure. This
keeps the transition smaller than introducing an entirely new shielded protocol
from first principles.

The important distinction is that Ironwood is not "more Orchard state". It has
its own value pool, tree, and nullifier set. An Ironwood note is represented with
Orchard note machinery, but it is committed into the Ironwood note commitment
tree and spent against the Ironwood nullifier set.

This lets existing Orchard receiver and viewing-key infrastructure remain useful
while creating a clean state boundary between legacy Orchard funds and Ironwood
funds.

## Quantum-Recoverable Notes

ZIP 2005 defines the Ironwood note plaintext format with lead byte `0x03`. This
is the quantum-recoverable note plaintext format.

In wallet-facing code, Ironwood notes are Orchard-shaped notes using the
Ironwood note plaintext format. Existing Orchard notes remain ordinary Orchard
notes. Ironwood notes use Ironwood tree state when they are spent.

## Transaction Version 6

Ironwood is carried by transaction version 6. Transaction version 6 is the same
as version 5, except that it adds an Ironwood bundle. A version 6 transaction
can contain:

- transparent inputs and outputs,
- a Sapling bundle,
- an Orchard bundle, and
- an Ironwood bundle.

Sapling and transparent components are unchanged from version 5. The Orchard and
Ironwood bundles follow the same Orchard-style bundle structure, but they are
separate bundles in the transaction. Ironwood uses different personalization
strings for its transaction and authorization hashes.

## Value Movement After NU7

After NU7 activation, no funds can flow into Orchard. Transactions can still
spend Orchard funds, and zero-balance Orchard actions are still allowed, but
Orchard value balance must not be negative.

Wallet-created payments and change that would previously have produced Orchard
outputs are routed to Ironwood after NU7. This moves newly created shielded
value into Ironwood while still allowing legacy Orchard notes to be spent.
