# Transaction Format

Version 6 follows the version 5 transaction format, with an Ironwood bundle
added after the Orchard bundle.

At the transaction ID layer, Ironwood is another child in the transaction hash
tree:

```mermaid
flowchart TD
    TxId["txid<br/>ZcashTxHash_ || consensusBranchId"]

    Header["header digest<br/>version, branch ID, lock time, expiry height"]
    Transparent["transparent digest"]
    Sapling["Sapling digest"]
    Orchard["Orchard bundle digest"]
    Ironwood["Ironwood bundle digest"]

    TxId --> Header
    TxId --> Transparent
    TxId --> Sapling
    TxId --> Orchard
    TxId --> Ironwood
```

The Orchard and Ironwood bundle digests have the same structure. The difference
is that Ironwood uses its own personalization strings at each bundle-hash node:

```mermaid
flowchart TD
    OrchardBundle["Orchard bundle digest<br/>ZTxIdOrchardHash"]
    IronwoodBundle["Ironwood bundle digest<br/>ZTxIdIronwd_Hash"]

    subgraph Shape["Same Orchard-style bundle hash shape"]
        Compact["actions compact hash<br/>nf, cmx, epk, compact ciphertext"]
        Memos["actions memo hash<br/>memo ciphertext"]
        NonCompact["actions non-compact hash<br/>cv, rk, remaining enc ciphertext, out ciphertext"]
        Flags["bundle flags"]
        Value["value balance"]
    end

    OrchardBundle --> Compact
    OrchardBundle --> Memos
    OrchardBundle --> NonCompact
    OrchardBundle --> Flags
    OrchardBundle --> Value

    IronwoodBundle -. same fields .-> Compact
    IronwoodBundle -. same fields .-> Memos
    IronwoodBundle -. same fields .-> NonCompact
    IronwoodBundle -. same fields .-> Flags
    IronwoodBundle -. same fields .-> Value
```

The same rule applies to authorization hashing: Ironwood follows the Orchard
bundle authorization structure, but uses Ironwood-specific personalization
strings.

In version 6 the bundle **anchor** is excluded from the txid bundle digest
shown above, and is instead committed in the **authorization digest**. This
keeps both the txid and the signature sighash independent of the anchor, so a
spend can be signed before the anchor it is finalized against — the
note-commitment-tree root — exists.
