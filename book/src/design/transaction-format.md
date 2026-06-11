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
        NonCompact["actions non-compact hash<br/>cv, rk, remaining ciphertext"]
        Flags["bundle flags"]
        Value["value balance"]
        Anchor["bundle anchor"]
    end

    OrchardBundle --> Compact
    OrchardBundle --> Memos
    OrchardBundle --> NonCompact
    OrchardBundle --> Flags
    OrchardBundle --> Value
    OrchardBundle --> Anchor

    IronwoodBundle -. same fields .-> Compact
    IronwoodBundle -. same fields .-> Memos
    IronwoodBundle -. same fields .-> NonCompact
    IronwoodBundle -. same fields .-> Flags
    IronwoodBundle -. same fields .-> Value
    IronwoodBundle -. same fields .-> Anchor
```

The same rule applies to authorization hashing: Ironwood follows the Orchard
bundle authorization structure, but uses Ironwood-specific personalization
strings.
