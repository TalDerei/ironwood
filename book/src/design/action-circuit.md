# Action Circuit

Ironwood reuses the Orchard Action circuit. The proof system, curves, gadgets,
and the action statement are inherited from Orchard unchanged. There is exactly
one circuit-level addition: a chain-wide, configurable **cross-address restriction** that, when
active, forces an action's output note to be addressed to the same receiver as
the note it spends.

## What Ironwood Reuses

An Ironwood action proves the
[Action Statement (Orchard)](https://zips.z.cash/protocol/protocol.pdf#actionstatement)
plus the cross-address restriction below, reusing the same machinery: the same
Halo 2 proof system and gadgets.

The circuit keeps the same advice columns, the same custom gates, and the same
circuit size. Ironwood proofs are therefore the same size as Orchard proofs.

## The Cross-Address Restriction

The one new circuit constraint enforces a same-receiver property. An Orchard
note is addressed to a diversified address, represented in the circuit by the
diversified base `g_d` and the diversified transmission key `pk_d`. When the
restriction is active, an action's output note and spent note must share that
address:

> `(g_d, pk_d)` of the output note must equal `(g_d, pk_d)` of the spent note.

When active, the restriction limits each action to change (the output returns to
the spent note's address) or withdrawal (value leaves the pool through a positive
value balance), rather than a *cross-address transfer*. Its purpose is to
discourage economic activity within the pool.

This is the circuit mechanism behind the
[Orchard Circuit Constraint](../design.md#orchard-circuit-constraint): after NU6.3,
legacy Orchard actions disable cross-address transfers and the pool is wound
down, while pools that accept new payments (Ironwood) keep cross-address
transfers enabled.

The companion rule that no new value may enter Orchard after NU6.3 (that the
Orchard value balance must not be negative) is not enforced by this circuit. The
per-action circuit only ties `v_old - v_new` to the action's value commitment
`cv_net`; the sign of the bundle's value balance is a transaction-level concern
outside the orchard crate. See
[Post-NU6.3 Orchard Value Rule](../design.md#post-nu63-orchard-value-rule).

### A new public input

The public-input layout is unified across all circuit versions: every version's
instance carries the same ten public inputs, with `disableCrossAddress` added
after the existing Orchard action inputs.

| Index | Public input |
|------:|--------------|
| 0 | anchor |
| 1–2 | value commitment `cv_net` |
| 3 | nullifier `nf_old` |
| 4–5 | randomized spend-auth key `rk` |
| 6 | output note commitment `cmx` |
| 7 | `enableSpend` |
| 8 | `enableOutput` |
| 9 | `disableCrossAddress` |

The bundle-level flag is `enableCrossAddress` (the NU6.3 flag, bit 2); the
circuit-level public input is its negation, `disableCrossAddress`. The Ironwood
circuit constrains it: `0` imposes no extra constraint, and
`1` enforces the same-receiver property above. Older circuit versions carry and
commit the input but leave it unconstrained, relying on the proving and
verification API to reject a set flag they cannot enforce. Because instance
columns are zero-padded over the evaluation domain, an unrestricted statement
(`disableCrossAddress = 0`) commits identically to the historical nine-input
Orchard encoding.

### How the constraint is enforced

Ironwood adds the constraint without adding a gate or a column. The existing
"Orchard circuit checks" gate (which checks value balance, the computed Merkle
root against the anchor, and the enable flags) already contains a product
constraint of the form `v_old · (root − anchor) = 0`, exactly the shape needed
for `disableCrossAddress · (old_coord − new_coord) = 0`.

The circuit reuses that gate on four extra rows, one per affine coordinate of
`g_d` and `pk_d`. Copy constraints place `disableCrossAddress` and the spent and
output coordinates into the gate, and its selector is enabled on those rows; with
the gate's other terms neutralized, the surviving constraint is:

```text
disableCrossAddress · (old_coord − new_coord) = 0
```

Any nonzero `disableCrossAddress` forces each coordinate of the output address to
equal the spent address; a zero leaves them free. The check is conditional on the
flag and does not rely on the flag being boolean.

## Keys And Enforcement

Ironwood is a new *circuit version* in the orchard crate that extends the fixed
post-NU6.2 circuit with the cross-address constraint. It ships with its own
proving and verifying keys.

- **The verifying key differs.** Enabling the shared gate on the four extra rows
  changes the circuit's fixed (selector) columns, so the Ironwood verifying key
  is distinct from the fixed-circuit verifying key, even though the proof size
  and verification cost are unchanged.
- **Restricted statements require Ironwood keys.** Because older versions cannot
  constrain `disableCrossAddress`, a statement that disables cross-address
  transfers is rejected outright when proved or verified with a non-Ironwood key;
  unrestricted statements are not gated this way.

The circuit is the cryptographic enforcement point: a prover cannot satisfy a
restricted statement with a cross-address output. The builder, PCZT,
and signer layers add a same-receiver structural check so that honest
participants do not construct a restricted bundle that would fail to prove.
