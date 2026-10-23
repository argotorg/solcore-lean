// Each input starts with a 32-byte operation number. The Python harness names
// the remaining words and checks returned bytes and committed account state.
object "Probe" {
  code {
    sstore(7, 10)
    datacopy(0, dataoffset("Runtime"), datasize("Runtime"))
    return(0, datasize("Runtime"))
  }
  object "Runtime" {
    code {
      let mode := calldataload(0)
      if or(and(gt(mode, 0), lt(mode, 5)), eq(mode, 12)) {
        let target := calldataload(32)
        let value := calldataload(64)
        let length := sub(calldatasize(), 96)
        calldatacopy(0, 96, length)
        let ok := 0
        switch mode
        case 1 { ok := delegatecall(gas(), target, 0, length, 0, 0) }
        case 2 { ok := callcode(gas(), target, value, 0, length, 0, 0) }
        case 3 { ok := call(gas(), target, value, 0, length, 0, 0) }
        case 4 { ok := staticcall(gas(), target, 0, length, 0, 0) }
        case 12 { ok := call(gas(), target, value, 0, length, 0, 0) }
        let size := returndatasize()
        mstore(0, ok)
        mstore(32, size)
        returndatacopy(64, 0, size)
        mstore(add(64, size), sload(7))
        mstore(add(96, size), selfbalance())
        if eq(mode, 12) { revert(0, add(128, size)) }
        return(0, add(128, size))
      }
      if eq(mode, 5) {
        let target := calldataload(32)
        mstore(0, extcodesize(target))
        mstore(32, extcodehash(target))
        extcodecopy(target, 64, calldataload(64), 64)
        mstore(128, balance(target))
        return(0, 160)
      }
      if and(gt(mode, 5), lt(mode, 9)) {
        let length := sub(calldatasize(), 96)
        calldatacopy(0, 96, length)
        let child := 0
        switch mode
        case 7 { child := create2(calldataload(32), 0, length, calldataload(64)) }
        default { child := create(calldataload(32), 0, length) }
        let size := returndatasize()
        mstore(0, child)
        mstore(32, size)
        mstore(64, extcodesize(child))
        mstore(96, extcodehash(child))
        returndatacopy(128, 0, size)
        if eq(mode, 8) { revert(0, add(128, size)) }
        return(0, add(128, size))
      }
      if eq(mode, 9) {
        let length := sub(calldatasize(), 128)
        calldatacopy(0, 128, length)
        let child := create2(calldataload(32), 0, length, calldataload(64))
        let beneficiary := calldataload(96)
        if iszero(beneficiary) { beneficiary := child }
        mstore(0, 3)
        mstore(32, beneficiary)
        let ok := call(gas(), child, 0, 0, 64, 0, 0)
        let size := extcodesize(child)
        let hash := extcodehash(child)
        let funds := balance(child)
        calldatacopy(0, 128, length)
        let again := create2(0, 0, length, calldataload(64))
        mstore(0, child)
        mstore(32, ok)
        mstore(64, size)
        mstore(96, hash)
        mstore(128, funds)
        mstore(160, again)
        return(0, 192)
      }
      if eq(mode, 10) { selfdestruct(calldataload(32)) }
      if eq(mode, 11) {
        mstore(0, sload(7))
        return(0, 32)
      }
    }
  }
}
