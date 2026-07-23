namespace Solcore.Foundation

def isLowerHexDigit (c : Char) : Bool :=
  "0123456789abcdef".contains c

def isLowerHexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all isLowerHexDigit

def isSha256 (value : String) : Bool :=
  isLowerHexOfLength 64 value

def isGitCommit (value : String) : Bool :=
  isLowerHexOfLength 40 value

end Solcore.Foundation
