// Independent Osaka reference probe. Words 8/9 record constructor self-code.
object "Target" {
  code {
    sstore(7, 99)
    sstore(8, extcodesize(address()))
    sstore(9, extcodehash(address()))
    datacopy(0, dataoffset("Runtime"), datasize("Runtime"))
    return(0, datasize("Runtime"))
  }
  object "Runtime" {
    code {
      switch calldataload(0)
      case 1 { sstore(7, calldataload(32)) }
      case 2 { sstore(7, calldataload(32)) mstore(0, 0xdeadbeef) revert(28, 4) }
      case 3 { selfdestruct(calldataload(32)) }
      mstore(0, address())
      mstore(32, caller())
      mstore(64, callvalue())
      mstore(96, sload(7))
      mstore(128, selfbalance())
      mstore(160, codesize())
      return(0, 192)
    }
  }
}
