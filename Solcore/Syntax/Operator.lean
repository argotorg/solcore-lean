import Solcore.Syntax.Type

set_option autoImplicit false

namespace Solcore.Syntax

/-- Prefix operators accepted by canonical Core expressions. -/
inductive UnaryOp where
  | logicalNot
  | bitNot
  deriving Repr, BEq, DecidableEq

namespace UnaryOp

def symbol : UnaryOp → Symbol
  | .logicalNot => .bang
  | .bitNot => .tilde

end UnaryOp

/-- Infix operators accepted by canonical Core expressions. -/
inductive BinaryOp where
  | multiply
  | divide
  | modulo
  | add
  | subtract
  | shiftLeft
  | shiftRight
  | bitAnd
  | bitXor
  | bitOr
  | less
  | greater
  | lessEqual
  | greaterEqual
  | equal
  | notEqual
  | logicalAnd
  | logicalOr
  /-- `+`, `-` and `*` written in an `unchecked` block. The parser never
  produces them; `Syntax.Unchecked.mark` does. -/
  | uncheckedAdd
  | uncheckedSubtract
  | uncheckedMultiply
  deriving Repr, BEq, DecidableEq

namespace BinaryOp

/-- Larger values bind more tightly. -/
def precedence : BinaryOp → Nat
  | .multiply | .divide | .modulo | .uncheckedMultiply => 9
  | .add | .subtract | .uncheckedAdd | .uncheckedSubtract => 8
  | .shiftLeft | .shiftRight => 7
  | .bitAnd => 6
  | .bitXor => 5
  | .bitOr => 4
  | .less | .greater | .lessEqual | .greaterEqual => 3
  | .equal | .notEqual => 2
  | .logicalAnd => 1
  | .logicalOr => 0

/-- Relational and equality chains are deliberately non-associative. -/
def isNonAssociative : BinaryOp → Bool
  | .less | .greater | .lessEqual | .greaterEqual | .equal | .notEqual => true
  | _ => false

/-- The symbol of the operator's first token. -/
def symbol : BinaryOp → Symbol
  | .multiply => .star
  | .divide => .slash
  | .modulo => .percent
  | .add => .plus
  | .subtract => .minus
  | .shiftLeft => .less
  | .shiftRight => .greater
  | .bitAnd => .amp
  | .bitXor => .caret
  | .bitOr => .pipe
  | .less => .less
  | .greater => .greater
  | .lessEqual => .lessEqual
  | .greaterEqual => .greaterEqual
  | .equal => .equalEqual
  | .notEqual => .notEqual
  | .logicalAnd => .logicalAnd
  | .logicalOr => .logicalOr
  | .uncheckedAdd => .plus
  | .uncheckedSubtract => .minus
  | .uncheckedMultiply => .star

/-- `<<` and `>>` repeat their symbol in a second, adjacent token. -/
def secondSymbol? : BinaryOp → Option Symbol
  | .shiftLeft => some .less
  | .shiftRight => some .greater
  | _ => none

/-- The number of tokens spelling the operator. -/
def tokenCount (operator : BinaryOp) : Nat :=
  if operator.secondSymbol?.isSome then 2 else 1

end BinaryOp

/-- Assignment spellings that consume a right-hand expression. -/
inductive ValueAssignOp where
  | equal
  | add
  | subtract
  | multiply
  | divide
  | modulo
  | bitAnd
  | bitXor
  | bitOr
  | shiftLeft
  | shiftRight
  /-- `+=`, `-=` and `*=` written in an `unchecked` block, produced by
  `Syntax.Unchecked.mark` only. -/
  | uncheckedAdd
  | uncheckedSubtract
  | uncheckedMultiply
  deriving Repr, BEq, DecidableEq

namespace ValueAssignOp

/-- The symbol of the operator's first token. -/
def symbol : ValueAssignOp → Symbol
  | .equal => .equal
  | .add => .plusEqual
  | .subtract => .minusEqual
  | .multiply => .starEqual
  | .divide => .slashEqual
  | .modulo => .percentEqual
  | .bitAnd => .ampEqual
  | .bitXor => .caretEqual
  | .bitOr => .pipeEqual
  | .shiftLeft => .less
  | .shiftRight => .greater
  | .uncheckedAdd => .plusEqual
  | .uncheckedSubtract => .minusEqual
  | .uncheckedMultiply => .starEqual

/-- `<<=` and `>>=` are `<` before an adjacent `<=`, and `>` before an
adjacent `>=`. -/
def secondSymbol? : ValueAssignOp → Option Symbol
  | .shiftLeft => some .lessEqual
  | .shiftRight => some .greaterEqual
  | _ => none

/-- The number of tokens spelling the operator. -/
def tokenCount (operator : ValueAssignOp) : Nat :=
  if operator.secondSymbol?.isSome then 2 else 1

/-- The compound assignments that take Words only: `<<=`, `>>=` and the
arithmetic of an `unchecked` block. -/
def wordOnly : ValueAssignOp → Bool
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply => true
  | _ => false

end ValueAssignOp

/-! Operators spelled by two adjacent tokens. The lexer reads `<<` and `>>` as
two `<` or `>` tokens, so that nested type arguments still close with two `>`
tokens; `<<=` is a `<` before a `<=`, and `>>=` a `>` before a `>=`. The parser
and the declarative grammar decode operators with the functions below. -/

/-- The token at `index` inside the active window. -/
def tokenWithin? (tokens : Array Token) (endIndex index : Nat) : Option Token :=
  if index < endIndex then tokens[index]? else none

/-- The token after `index` when it starts exactly where `first` ends. -/
def adjacentToken? (tokens : Array Token) (endIndex index : Nat)
    (first : Token) : Option Token :=
  match tokenWithin? tokens endIndex (index + 1) with
  | some next => if first.span.endByte = next.span.startByte then some next else none
  | none => none

/-- The operator `spelled` decodes at `index` from the token there and an
adjacent next token; it spans both tokens when it has a second symbol. -/
def spelledAt? {α : Type} (spelled : TokenKind → Option TokenKind → Option α)
    (secondSymbol? : α → Option Symbol) (tokens : Array Token)
    (endIndex index : Nat) : Option (Located α) :=
  match tokenWithin? tokens endIndex index with
  | none => none
  | some first =>
      let second := adjacentToken? tokens endIndex index first
      (spelled first.value (second.map (·.value))).map fun operator => {
        span := match secondSymbol? operator, second with
          | some _, some next => SourceSpan.cover first.span next.span
          | _, _ => first.span
        value := operator
      }

theorem tokenWithin?_some {tokens : Array Token} {endIndex index : Nat}
    {token : Token} (found : tokenWithin? tokens endIndex index = some token) :
    index < endIndex ∧ tokens[index]? = some token := by
  unfold tokenWithin? at found
  split at found
  · exact ⟨by assumption, found⟩
  · contradiction

theorem adjacentToken?_some {tokens : Array Token} {endIndex index : Nat}
    {first next : Token}
    (found : adjacentToken? tokens endIndex index first = some next) :
    tokenWithin? tokens endIndex (index + 1) = some next ∧
      first.span.endByte = next.span.startByte := by
  unfold adjacentToken? at found
  split at found
  · rename_i candidate within
    split at found
    · cases found; exact ⟨within, by assumption⟩
    · contradiction
  · contradiction

/-- A decoded operator either spans its first token and has no second symbol,
or spans its first token and the adjacent next one. -/
theorem spelledAt?_cases {α : Type}
    {spelled : TokenKind → Option TokenKind → Option α}
    {secondSymbol? : α → Option Symbol}
    (second_spelled : ∀ {first second operator symbol},
      spelled first second = some operator → secondSymbol? operator = some symbol →
        second = some (.symbol symbol))
    {tokens : Array Token} {endIndex index : Nat} {operator : Located α}
    (found : spelledAt? spelled secondSymbol? tokens endIndex index = some operator) :
    ∃ first, tokenWithin? tokens endIndex index = some first ∧
      ((secondSymbol? operator.value = none ∧ operator.span = first.span) ∨
        ∃ symbol next, secondSymbol? operator.value = some symbol ∧
          tokenWithin? tokens endIndex (index + 1) = some next ∧
          first.span.endByte = next.span.startByte ∧
          operator.span = SourceSpan.cover first.span next.span) := by
  unfold spelledAt? at found
  split at found
  · contradiction
  · rename_i first within
    refine ⟨first, within, ?_⟩
    cases decoded : spelled first.value
        ((adjacentToken? tokens endIndex index first).map (·.value)) with
    | none => simp [decoded] at found
    | some value =>
        simp only [decoded, Option.map_some, Option.some.injEq] at found
        subst found
        cases symbolFound : secondSymbol? value with
        | none => exact .inl ⟨rfl, by simp⟩
        | some symbol =>
            have secondKind := second_spelled decoded symbolFound
            cases adjacent : adjacentToken? tokens endIndex index first with
            | none => simp [adjacent] at secondKind
            | some next =>
                rcases adjacentToken?_some adjacent with ⟨nextWithin, touching⟩
                exact .inr ⟨symbol, next, rfl, nextWithin, touching,
                  by simp⟩

/-- The tokens of a decoded operator lie inside the active window. -/
theorem spelledAt?_bound {α : Type}
    {spelled : TokenKind → Option TokenKind → Option α}
    {secondSymbol? : α → Option Symbol}
    (second_spelled : ∀ {first second operator symbol},
      spelled first second = some operator → secondSymbol? operator = some symbol →
        second = some (.symbol symbol))
    {tokens : Array Token} {endIndex index : Nat} {operator : Located α}
    (found : spelledAt? spelled secondSymbol? tokens endIndex index = some operator) :
    index + (if (secondSymbol? operator.value).isSome then 2 else 1) ≤ endIndex := by
  rcases spelledAt?_cases second_spelled found with
    ⟨first, within, ⟨none, _⟩ | ⟨symbol, next, some, nextWithin, _, _⟩⟩
  · simp only [none, Option.isSome_none]
    exact (tokenWithin?_some within).1
  · simp only [some, Option.isSome_some, if_true]
    exact (tokenWithin?_some nextWithin).1

namespace BinaryOp

/-- The operator spelled by one token. -/
def ofToken? : TokenKind → Option BinaryOp
  | .symbol .star => some .multiply
  | .symbol .slash => some .divide
  | .symbol .percent => some .modulo
  | .symbol .plus => some .add
  | .symbol .minus => some .subtract
  | .symbol .amp => some .bitAnd
  | .symbol .caret => some .bitXor
  | .symbol .pipe => some .bitOr
  | .symbol .less => some .less
  | .symbol .greater => some .greater
  | .symbol .lessEqual => some .lessEqual
  | .symbol .greaterEqual => some .greaterEqual
  | .symbol .equalEqual => some .equal
  | .symbol .notEqual => some .notEqual
  | .symbol .logicalAnd => some .logicalAnd
  | .symbol .logicalOr => some .logicalOr
  | _ => none

/-- The operator a first token spells together with the kind of an adjacent
second token. A `<` or `>` before an adjacent `<=` or `>=` starts an
assignment operator, not a binary one. -/
def spelled? : TokenKind → Option TokenKind → Option BinaryOp
  | .symbol .less, some (.symbol .less) => some .shiftLeft
  | .symbol .less, some (.symbol .lessEqual) => none
  | .symbol .greater, some (.symbol .greater) => some .shiftRight
  | .symbol .greater, some (.symbol .greaterEqual) => none
  | first, _ => ofToken? first

/-- The binary operator at `index`, spanning both tokens of `<<` and `>>`. -/
def at? (tokens : Array Token) (endIndex index : Nat) : Option (Located BinaryOp) :=
  spelledAt? spelled? secondSymbol? tokens endIndex index

theorem ofToken?_symbol {kind : TokenKind} {operator : BinaryOp}
    (decoded : ofToken? kind = some operator) :
    kind = .symbol operator.symbol ∧ operator.secondSymbol? = none := by
  cases kind with
  | symbol symbol =>
      cases symbol <;> simp only [ofToken?, Option.some.injEq, reduceCtorEq] at decoded <;>
        subst decoded <;> exact ⟨rfl, rfl⟩
  | _ => simp [ofToken?] at decoded

theorem spelled?_symbol {first : TokenKind} {second : Option TokenKind}
    {operator : BinaryOp} (decoded : spelled? first second = some operator) :
    first = .symbol operator.symbol ∧
      ∀ symbol, operator.secondSymbol? = some symbol → second = some (.symbol symbol) := by
  unfold spelled? at decoded
  split at decoded
  · cases decoded; exact ⟨rfl, fun _ found => by cases found; rfl⟩
  · contradiction
  · cases decoded; exact ⟨rfl, fun _ found => by cases found; rfl⟩
  · contradiction
  · rcases ofToken?_symbol decoded with ⟨kind, single⟩
    exact ⟨kind, fun _ found => by simp [single] at found⟩

theorem spelled?_second {first : TokenKind} {second : Option TokenKind}
    {operator : BinaryOp} {symbol : Symbol}
    (decoded : spelled? first second = some operator)
    (found : operator.secondSymbol? = some symbol) : second = some (.symbol symbol) :=
  (spelled?_symbol decoded).2 symbol found

theorem tokenCount_pos (operator : BinaryOp) : 0 < operator.tokenCount := by
  unfold tokenCount; split <;> omega

theorem at?_cases {tokens : Array Token} {endIndex index : Nat}
    {operator : Located BinaryOp} (found : at? tokens endIndex index = some operator) :
    ∃ first, tokenWithin? tokens endIndex index = some first ∧
      ((operator.value.secondSymbol? = none ∧ operator.span = first.span) ∨
        ∃ symbol next, operator.value.secondSymbol? = some symbol ∧
          tokenWithin? tokens endIndex (index + 1) = some next ∧
          first.span.endByte = next.span.startByte ∧
          operator.span = SourceSpan.cover first.span next.span) :=
  spelledAt?_cases spelled?_second found

theorem at?_bound {tokens : Array Token} {endIndex index : Nat}
    {operator : Located BinaryOp} (found : at? tokens endIndex index = some operator) :
    index + operator.value.tokenCount ≤ endIndex :=
  spelledAt?_bound spelled?_second found

end BinaryOp

namespace ValueAssignOp

/-- The assignment operator spelled by one token. -/
def ofToken? : TokenKind → Option ValueAssignOp
  | .symbol .equal => some .equal
  | .symbol .plusEqual => some .add
  | .symbol .minusEqual => some .subtract
  | .symbol .starEqual => some .multiply
  | .symbol .slashEqual => some .divide
  | .symbol .percentEqual => some .modulo
  | .symbol .ampEqual => some .bitAnd
  | .symbol .caretEqual => some .bitXor
  | .symbol .pipeEqual => some .bitOr
  | _ => none

/-- The assignment operator a first token spells together with the kind of an
adjacent second token. -/
def spelled? : TokenKind → Option TokenKind → Option ValueAssignOp
  | .symbol .less, some (.symbol .lessEqual) => some .shiftLeft
  | .symbol .greater, some (.symbol .greaterEqual) => some .shiftRight
  | first, _ => ofToken? first

/-- The assignment operator at `index`, spanning both tokens of `<<=` and
`>>=`. -/
def at? (tokens : Array Token) (endIndex index : Nat) :
    Option (Located ValueAssignOp) :=
  spelledAt? spelled? secondSymbol? tokens endIndex index

theorem ofToken?_symbol {kind : TokenKind} {operator : ValueAssignOp}
    (decoded : ofToken? kind = some operator) :
    kind = .symbol operator.symbol ∧ operator.secondSymbol? = none := by
  cases kind with
  | symbol symbol =>
      cases symbol <;> simp only [ofToken?, Option.some.injEq, reduceCtorEq] at decoded <;>
        subst decoded <;> exact ⟨rfl, rfl⟩
  | _ => simp [ofToken?] at decoded

theorem spelled?_symbol {first : TokenKind} {second : Option TokenKind}
    {operator : ValueAssignOp} (decoded : spelled? first second = some operator) :
    first = .symbol operator.symbol ∧
      ∀ symbol, operator.secondSymbol? = some symbol → second = some (.symbol symbol) := by
  unfold spelled? at decoded
  split at decoded
  · cases decoded; exact ⟨rfl, fun _ found => by cases found; rfl⟩
  · cases decoded; exact ⟨rfl, fun _ found => by cases found; rfl⟩
  · rcases ofToken?_symbol decoded with ⟨kind, single⟩
    exact ⟨kind, fun _ found => by simp [single] at found⟩

theorem spelled?_second {first : TokenKind} {second : Option TokenKind}
    {operator : ValueAssignOp} {symbol : Symbol}
    (decoded : spelled? first second = some operator)
    (found : operator.secondSymbol? = some symbol) : second = some (.symbol symbol) :=
  (spelled?_symbol decoded).2 symbol found

theorem tokenCount_pos (operator : ValueAssignOp) : 0 < operator.tokenCount := by
  unfold tokenCount; split <;> omega

theorem at?_cases {tokens : Array Token} {endIndex index : Nat}
    {operator : Located ValueAssignOp} (found : at? tokens endIndex index = some operator) :
    ∃ first, tokenWithin? tokens endIndex index = some first ∧
      ((operator.value.secondSymbol? = none ∧ operator.span = first.span) ∨
        ∃ symbol next, operator.value.secondSymbol? = some symbol ∧
          tokenWithin? tokens endIndex (index + 1) = some next ∧
          first.span.endByte = next.span.startByte ∧
          operator.span = SourceSpan.cover first.span next.span) :=
  spelledAt?_cases spelled?_second found

theorem at?_bound {tokens : Array Token} {endIndex index : Nat}
    {operator : Located ValueAssignOp} (found : at? tokens endIndex index = some operator) :
    index + operator.value.tokenCount ≤ endIndex :=
  spelledAt?_bound spelled?_second found

end ValueAssignOp

end Solcore.Syntax
