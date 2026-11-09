import Solcore.Syntax.Parser

/-! `unchecked { … }` blocks (solcore-rs #119), removed around the parser.

A block is the contextual keyword `unchecked` at the start of a statement
(after `{`, `}` or `;`) followed by `{`, as upstream reads it. `prepare`
replaces each such keyword's bytes with spaces, so the parser reads a plain
block statement starting at the recorded `{` and every other span is
unchanged. `mark` then gives the block's arithmetic its unchecked operators.
Neither the parser nor inference gains a statement form.

A block reaches every expression and statement written in it, including
nested blocks, conditions, loop headers and match arms, but no lambda body:
a lambda body starts outside any block and may hold its own. Patterns are not
marked. A block written in another block is rejected, as upstream rejects it
(`SC0001`), and so is a recorded `{` that starts no block statement. -/

set_option autoImplicit false

namespace Solcore.Syntax.Unchecked

inductive Error where
  /-- A block written in another block, at its `{`. -/
  | nested (span : SourceSpan)
  /-- `unchecked {` whose `{` starts no block statement, at that `{`. -/
  | notStatement (startByte : Nat)
  /-- The traversal bound, four times the file's byte size, was reached. -/
  | depthExhausted
  /-- Replacing ASCII bytes with spaces broke UTF-8, which cannot happen. -/
  | invalidSource
  deriving Repr, DecidableEq

/-- The `unchecked` keywords that open a block, with the `{` that follows
each. -/
def keywords : Option Token → List Token → List (SourceSpan × Nat)
  | previous, keyword :: brace :: rest =>
      let tail := keywords (some keyword) (brace :: rest)
      let atStatement := match previous with
        | some { value := .symbol .leftBrace, .. }
        | some { value := .symbol .rightBrace, .. }
        | some { value := .symbol .semicolon, .. } => true
        | _ => false
      match keyword.value, brace.value with
      | .identifier "unchecked", .symbol .leftBrace =>
          if atStatement then (keyword.span, brace.span.startByte) :: tail else tail
      | _, _ => tail
  | _, _ => []

/-- Replace each span's bytes with spaces. -/
def blank (content : String) (spans : List SourceSpan) : Option String :=
  String.fromUTF8? <| spans.foldl (fun bytes span =>
      (List.range (span.endByte - span.startByte)).foldl
        (fun bytes offset => bytes.set! (span.startByte + offset) 0x20) bytes)
    content.toByteArray

/-- The file the parser reads, and the start of every block's `{`. A file
the lexer rejects is returned unchanged for the parser to report. -/
def prepare (file : SourceFile) : Except Error (SourceFile × List Nat) :=
  match Lexer.lex file with
  | .error _ => .ok (file, [])
  | .ok lexed =>
      let found := keywords none lexed.tokens
      match blank file.content (found.map Prod.fst) with
      | some content => .ok ({ file with content }, found.map Prod.snd)
      | none => .error .invalidSource

def BinaryOp.unchecked : BinaryOp → BinaryOp
  | .add => .uncheckedAdd
  | .subtract => .uncheckedSubtract
  | .multiply => .uncheckedMultiply
  | .divide => .uncheckedDivide
  | .modulo => .uncheckedModulo
  | operator => operator

def ValueAssignOp.unchecked : ValueAssignOp → ValueAssignOp
  | .add => .uncheckedAdd
  | .subtract => .uncheckedSubtract
  | .multiply => .uncheckedMultiply
  | .divide => .uncheckedDivide
  | .modulo => .uncheckedModulo
  | operator => operator

/-- The recorded `{` starts not yet met. -/
abbrev M := StateT (List Nat) (Except Error)

/-- Whether a block statement starting here is an unchecked block. -/
def claim (startByte : Nat) : M Bool := do
  let pending ← get
  if pending.contains startByte then
    set (pending.erase startByte)
    pure true
  else
    pure false

/-- A compound arithmetic assignment in a block becomes unchecked. -/
def assignOperator (inside : Bool) (operator : Located ValueAssignOp) : Located ValueAssignOp :=
  if inside then { operator with value := ValueAssignOp.unchecked operator.value } else operator

/-- A binary arithmetic operator in a block becomes unchecked. -/
def binaryOperator (inside : Bool) (operator : Located BinaryOp) : Located BinaryOp :=
  if inside then { operator with value := BinaryOp.unchecked operator.value } else operator

mutual

def expression : Nat → Bool → Located ExprValue → M (Located ExprValue)
  | 0, _, _ => throw .depthExhausted
  | fuel + 1, inside, written => do
      let value ← match written.value with
        | .dotConstructor dot name (some arguments) =>
            pure (.dotConstructor dot name (some (← delimited fuel inside arguments)))
        | .lambda keyword parameters returnType body =>
            pure (.lambda keyword parameters returnType (← block fuel false body))
        | .unary operator operand => pure (.unary operator (← expression fuel inside operand))
        | .binary left operator right =>
            pure (.binary (← expression fuel inside left) (binaryOperator inside operator)
              (← expression fuel inside right))
        | .index base brackets index =>
            pure (.index (← expression fuel inside base) brackets (← expression fuel inside index))
        | .call callee arguments =>
            pure (.call (← expression fuel inside callee) (← delimited fuel inside arguments))
        | .field base dot name => pure (.field (← expression fuel inside base) dot name)
        | .conditional condition question thenBranch colon elseBranch =>
            pure (.conditional (← expression fuel inside condition) question
              (← expression fuel inside thenBranch) colon (← expression fuel inside elseBranch))
        | .group inner => pure (.group (← expression fuel inside inner))
        | .tuple elements => pure (.tuple (← delimited fuel inside elements))
        | .array elements => pure (.array (← delimited fuel inside elements))
        | value => pure value
      pure { written with value }

def expressions : Nat → Bool → List (Located ExprValue) → M (List (Located ExprValue))
  | 0, _, _ => throw .depthExhausted
  | _, _, [] => pure []
  | fuel + 1, inside, first :: rest =>
      return (← expression fuel inside first) :: (← expressions fuel inside rest)

def delimited : Nat → Bool → DelimitedList (Located ExprValue) →
    M (DelimitedList (Located ExprValue))
  | 0, _, _ => throw .depthExhausted
  | fuel + 1, inside, list => return { list with elements := ← expressions fuel inside list.elements }

def optional : Nat → Bool → Option (Located ExprValue) → M (Option (Located ExprValue))
  | 0, _, _ => throw .depthExhausted
  | _, _, none => pure none
  | fuel + 1, inside, some written => return some (← expression fuel inside written)

def block : Nat → Bool → Located (List (Located StatementValue)) →
    M (Located (List (Located StatementValue)))
  | 0, _, _ => throw .depthExhausted
  | fuel + 1, inside, body => return { body with value := ← statements fuel inside body.value }

def forItems : Nat → Bool → List (Located ForItemValue) → M (List (Located ForItemValue))
  | 0, _, _ => throw .depthExhausted
  | _, _, [] => pure []
  | fuel + 1, inside, item :: rest => do
      let value ← match item.value with
        | .letDecl name type initializer => pure (.letDecl name type (← optional fuel inside initializer))
        | .expression written => pure (.expression (← expression fuel inside written))
        | .assignValue target operator value =>
            pure (.assignValue (← expression fuel inside target) (assignOperator inside operator)
              (← expression fuel inside value))
        | .assignBitNot target operator => pure (.assignBitNot (← expression fuel inside target) operator)
      return { item with value } :: (← forItems fuel inside rest)

def cases : Nat → Bool → List (Located MatchCaseValue) → M (List (Located MatchCaseValue))
  | 0, _, _ => throw .depthExhausted
  | _, _, [] => pure []
  | fuel + 1, inside, arm :: rest =>
      return { arm with value := { arm.value with body := ← block fuel inside arm.value.body } } ::
        (← cases fuel inside rest)

def statements : Nat → Bool → List (Located StatementValue) → M (List (Located StatementValue))
  | 0, _, _ => throw .depthExhausted
  | _, _, [] => pure []
  | fuel + 1, inside, first :: rest =>
      return (← statement fuel inside first) :: (← statements fuel inside rest)

def statement : Nat → Bool → Located StatementValue → M (Located StatementValue)
  | 0, _, _ => throw .depthExhausted
  | fuel + 1, inside, written => do
      let value ← match written.value with
        | .letDecl name type initializer => pure (.letDecl name type (← optional fuel inside initializer))
        | .returnStmt value => pure (.returnStmt (← optional fuel inside value))
        | .expression value trailingSemicolon =>
            pure (.expression (← expression fuel inside value) trailingSemicolon)
        | .assignValue target operator value =>
            pure (.assignValue (← expression fuel inside target) (assignOperator inside operator)
              (← expression fuel inside value))
        | .assignBitNot target operator => pure (.assignBitNot (← expression fuel inside target) operator)
        | .matchWith scrutinees arms =>
            let head ← expression fuel inside scrutinees.elements.head
            let tail ← expressions fuel inside scrutinees.elements.tail
            let armCases ← cases fuel inside arms.value.cases
            let defaultBody ← match arms.value.defaultBody with
              | some body => some <$> block fuel inside body
              | none => pure none
            pure (.matchWith { scrutinees with elements := { head, tail } }
              { arms with value := { cases := armCases, defaultBody } })
        | .forLoop headerSpan initializer condition post body =>
            pure (.forLoop headerSpan (← forItems fuel inside initializer) (← expression fuel inside condition)
              (← forItems fuel inside post) (← block fuel inside body))
        | .whileLoop condition body =>
            pure (.whileLoop (← expression fuel inside condition) (← block fuel inside body))
        | .ifThen condition thenBody elseBody =>
            let condition ← expression fuel inside condition
            let thenBody ← block fuel inside thenBody
            let elseBody ← match elseBody with
              | some body => some <$> block fuel inside body
              | none => pure none
            pure (.ifThen condition thenBody elseBody)
        | .block body =>
            if ← claim written.span.startByte then
              if inside then throw (.nested written.span)
              pure (.block (← statements fuel true body))
            else
              pure (.block (← statements fuel inside body))
        | value => pure value
      pure { written with value }

end

/-- Mark every body of a declaration. -/
def functionBody (fuel : Nat) (declaration : FunctionDecl) : M FunctionDecl :=
  return { declaration with value := { declaration.value with body := ← block fuel false declaration.value.body } }

def contractMember (fuel : Nat) (member : ContractMember) : M ContractMember := do
  let value ← match member.value with
    | .field declaration =>
        pure (.field { declaration with value := { declaration.value with
          initializer := ← optional fuel false declaration.value.initializer } })
    | .function declaration => pure (.function (← functionBody fuel declaration))
    | .constructor declaration =>
        pure (.constructor { declaration with value := { declaration.value with
          body := ← block fuel false declaration.value.body } })
    | .fallback declaration =>
        pure (.fallback { declaration with value := { declaration.value with
          body := ← block fuel false declaration.value.body } })
    | value => pure value
  pure { member with value }

def topItem (fuel : Nat) (item : TopItem) : M TopItem := do
  let value ← match item.value with
    | .function declaration => pure (.function (← functionBody fuel declaration))
    | .impl declaration =>
        pure (.impl { declaration with value := { declaration.value with
          methods := ← declaration.value.methods.mapM fun method =>
            return { method with value := { method.value with
              declaration := ← functionBody fuel method.value.declaration } } } })
    | .contract declaration =>
        pure (.contract { declaration with value := { declaration.value with
          members := ← declaration.value.members.mapM (contractMember fuel) } })
    | value => pure value
  pure { item with value }

/-- Give each recorded block's arithmetic its unchecked operators. Every
recorded `{` must start a block statement. -/
def mark (fuel : Nat) (starts : List Nat) (file : ParsedFile) : Except Error ParsedFile := do
  let (items, unclaimed) ← (file.items.mapM (topItem fuel)).run starts
  match unclaimed with
  | [] => pure { file with items }
  | startByte :: _ => throw (.notStatement startByte)

end Solcore.Syntax.Unchecked
