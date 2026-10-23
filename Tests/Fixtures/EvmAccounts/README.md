# Osaka account reference vectors

These small Yul contracts are independent reference probes. They do not modify
the pinned Rust sources. Run them with local Anvil, cast and solc:

```sh
python3 scripts/evm-account-reference.py
```

The runner compiles with `solc --strict-assembly --optimize --evm-version osaka`,
starts an isolated Anvil chain, checks returned bytes and committed account
state, and stops the chain. Temporary process logs are removed. The report is
`.upstream/evm-account-reference.json`; it records source hashes and tool
versions. The 2026-10-24 run passed all 67 checks with solc 0.8.35 and
Anvil/cast 1.5.1-stable.

Covered behavior:

- Delegate calls retain the parent caller/value/address and update parent storage.
- Call-code uses the parent address/storage, caller equal to that address, and
  explicit value. It checks balance without transferring funds. Nonzero value
  is allowed in a static context; state writes still fail.
- External code observations distinguish absent/EIP-161-empty accounts from
  funded or nonce-positive accounts without code. Addresses use their low 160
  bits. Code copying pads missing bytes, including oversized source offsets.
- Constructor self-code is hidden; its nonzero nonce makes its code hash equal
  to Keccak of empty bytes. Runtime code is installed only after construction.
- Creation checks address formulas, successful runtime installation, prefunding,
  collision by nonce or code, constructor failure data, nonce changes and rollback.
- Existing-account selfdestruct preserves code/storage/nonce. Same-transaction
  creation and destruction retain code visibility until transaction end, then
  delete the account. The pending deletion cannot bypass a creation collision.
  Self-beneficiary destruction burns funds only for the newly created account.
- Static creation/destruction fails; parent revert rolls back child creation
  and destruction effects.

`address-vectors.json` contains 11 CREATE/CREATE2 address vectors verified with
`cast compute-address` and a separate RLP implementation using `cast keccak`.
The CREATE nonce `2^64 - 1` vector tests address calculation only; it does not
assert that creation is permitted at that nonce.

Account execution should keep code identity separate from the context address.
Creation failure must restore child state while retaining an admitted attempt's
creator nonce increment; reverting the parent restores that increment too.
Deletion needs a transaction-finalization step, rather than immediate removal
of code on selfdestruct. These vectors check behavior and are not proofs of
general EVM equivalence or gas equivalence.

Relevant specifications: [EIP-7](https://eips.ethereum.org/EIPS/eip-7),
[EIP-161](https://eips.ethereum.org/EIPS/eip-161),
[EIP-211](https://eips.ethereum.org/EIPS/eip-211),
[EIP-214](https://eips.ethereum.org/EIPS/eip-214),
[EIP-684](https://eips.ethereum.org/EIPS/eip-684),
[EIP-1014](https://eips.ethereum.org/EIPS/eip-1014),
[EIP-1052](https://eips.ethereum.org/EIPS/eip-1052), and
[EIP-6780](https://eips.ethereum.org/EIPS/eip-6780).
