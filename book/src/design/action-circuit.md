# Action Circuit

From NU6.3, both the *Orchard* and *Ironwood pools* use a single Action circuit
version (`OrchardCircuitVersion::PostNU6_3`). It inherits the proof system,
curves, gadgets, and action statement from the Orchard protocol unchanged, and
adds exactly one circuit-level constraint: a configurable **cross-address
restriction** that, when active, forces an action's output note to be addressed
to the same expanded receiver ($\gd$ and $\pkd$) as the note it spends.

## What Ironwood Reuses

A post-NU6.3 action, in either pool, proves the
[Action Statement (Orchard)](https://zips.z.cash/protocol/protocol.pdf#actionstatement)
plus the cross-address restriction below, reusing the same machinery: the same
Halo 2 proof system and gadgets.

The post-NU6.3 circuit keeps the same advice columns, the same custom gates, and
the same circuit size as the pre-NU6.3 one. Post-NU6.3 proofs are therefore the
same size as pre-NU6.3 proofs. They are also the same size between the *Orchard-pool*
and *Ironwood-pool* bundles.

## The Cross-Address Restriction

The one new circuit constraint enforces a same-receiver property. A note is
addressed to an expanded receiver, represented in the circuit by the diversified
base $\gd$ and the diversified transmission key $\pkd$. When the restriction is
active, an action's output note and spent note must share that expanded receiver:

> $(\gd, \pkd)$ of the output note must equal $(\gd, \pkd)$ of the spent note.

When active, the restriction limits each action to change (the output returns to
the spent note's address) or withdrawal (value leaves the pool through a positive
value balance), rather than a *cross-address transfer*. Its purpose is to
discourage economic activity within the pool.

This is the circuit mechanism behind the
[Orchard Circuit Constraint](../design.md#orchard-circuit-constraint): after NU6.3,
legacy *Orchard-pool* actions disable cross-address transfers and the *Orchard pool*
is wound down, while pools that accept new payments (the *Ironwood pool*) keep
cross-address transfers enabled.

The companion rule that no new value may enter the *Orchard pool* after NU6.3
(that the *Orchard pool*'s value balance must not be negative) is not enforced by
this circuit. The per-action circuit only ties $\vOld - \vNew$ to the action's
value commitment $\cvNet$; the sign of the bundle's value balance is a
transaction-level concern outside the orchard crate. See
[Post-NU6.3 *Orchard-Pool* Value Rule](../design.md#post-nu63-orchard-pool-value-rule).

### A new public input

The public-input layout is unified across all circuit versions: every version's
instance carries the same ten public inputs, with `disableCrossAddress` added
after the existing Orchard-protocol action inputs.

| Index | Public input |
|------:|--------------|
| 0 | anchor |
| 1–2 | value commitment $\cvNet$ |
| 3 | nullifier $\nfOld$ |
| 4–5 | randomized spend-auth key $\rk$ |
| 6 | output note commitment $\cmX$ |
| 7 | `enableSpends` |
| 8 | `enableOutputs` |
| 9 | `disableCrossAddress` |

The bundle-level flag is `enableCrossAddress` (the NU6.3 flag, bit 2); the
circuit-level public input is its negation, $\disableCrossAddress$. The post-NU6.3
circuit constrains it: $0$ imposes no extra constraint, and $1$ enforces the
same-expanded-receiver property above. Older circuit versions carry and
commit the input but leave it unconstrained, relying on the proving and
verification API to reject a set flag they cannot enforce. Because instance
columns are zero-padded over the evaluation domain, an unrestricted statement
($\disableCrossAddress = 0$) commits identically to the pre-NU6.3 nine-input
instance encoding.

### How the constraint is enforced

The post-NU6.3 circuit adds the constraint without adding a gate or a column. The
existing "Orchard circuit checks" gate (which checks value balance, the computed
Merkle root against the anchor, and the enable flags) already contains a product
constraint of the form $\vOld \cdot (\root - \anchor) = 0$, exactly the shape needed
for $\disableCrossAddress \cdot (\coordOld - \coordNew) = 0$.

The circuit reuses that gate on four extra rows, one per affine coordinate of
$\gd$ and $\pkd$. Copy constraints place $\disableCrossAddress$ and the spent and
output coordinates into the gate, and its selector is enabled on those rows; with
the gate's other terms neutralized, the surviving constraint is:

$$
\disableCrossAddress \cdot (\coordOld - \coordNew) = 0
$$

Any nonzero $\disableCrossAddress$ forces each coordinate of the output address to
equal the spent address; a zero leaves them free. The check is conditional on the
flag and does not rely on the flag being boolean.

## Keys And Enforcement

The post-NU6.3 circuit (`OrchardCircuitVersion::PostNU6_3`) is a new circuit
version in the orchard crate that extends the fixed post-NU6.2 circuit with the
cross-address constraint. It ships with its own proving and verifying keys.

- **The verifying key differs.** Enabling the shared gate on the four extra rows
  changes the circuit's fixed (selector) columns, so the post-NU6.3 verifying
  key is distinct from the fixed-circuit verifying key, even though the proof size
  and verification cost are unchanged.
- **Restricted statements require the post-NU6.3 keys.** Because older versions
  cannot constrain $\disableCrossAddress$, it is incorrect to use those versions
  with an instance that includes the $\disableCrossAddress$ instance variable.

The circuit is the cryptographic enforcement point: a prover cannot satisfy a
restricted statement with a cross-address output. The builder, PCZT,
and signer layers add a same-receiver structural check so that honest
participants do not construct a restricted bundle that would fail to prove.
