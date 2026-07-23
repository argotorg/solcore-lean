import Lean.Data.Json.Parser

set_option autoImplicit false

open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace Solcore.Oracle.StrictJson

mutual

  partial def arrayCore (acc : Array Lean.Json) : Parser (Array Lean.Json) := do
    let head ← anyCore
    let acc := acc.push head
    let delimiter ← any
    if delimiter == ']' then
      ws
      return acc
    else if delimiter == ',' then
      ws
      arrayCore acc
    else
      fail "unexpected character in array"

  partial def objectCore
      (fields : Std.TreeMap.Raw String Lean.Json compare) :
      Parser (Std.TreeMap.Raw String Lean.Json compare) := do
    Lean.Json.Parser.lookahead (fun char => char == '"') "\""
    skip
    let key ← Lean.Json.Parser.str
    if fields.contains key then
      fail s!"duplicate object key: {key}"
    ws
    Lean.Json.Parser.lookahead (fun char => char == ':') ":"
    skip
    ws
    let value ← anyCore
    let fields := fields.insert key value
    let delimiter ← any
    if delimiter == '}' then
      ws
      return fields
    else if delimiter == ',' then
      ws
      objectCore fields
    else
      fail "unexpected character in object"

  partial def anyCore : Parser Lean.Json := do
    let char ← peek!
    if char == '[' then
      skip
      ws
      let char ← peek!
      if char == ']' then
        skip
        ws
        return .arr #[]
      else
        return .arr (← arrayCore #[])
    else if char == '{' then
      skip
      ws
      let char ← peek!
      if char == '}' then
        skip
        ws
        return .obj ∅
      else
        return .obj (← objectCore ∅)
    else if char == '"' then
      skip
      let value ← Lean.Json.Parser.str
      ws
      return .str value
    else if char == 'f' then
      skipString "false"
      ws
      return .bool false
    else if char == 't' then
      skipString "true"
      ws
      return .bool true
    else if char == 'n' then
      skipString "null"
      ws
      return .null
    else if char == '-' || ('0' <= char && char <= '9') then
      let value ← Lean.Json.Parser.num
      ws
      return .num value
    else
      fail "unexpected input"

end

def any : Parser Lean.Json := do
  ws
  let result ← anyCore
  eof
  return result

def parse (input : String) : Except String Lean.Json :=
  Parser.run any input

end Solcore.Oracle.StrictJson
