import Solcore.Syntax.Declaration
import Solcore.Syntax.Source
import Solcore.Syntax.Parser.Terms
import Solcore.Syntax.Parser.Blocks
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Term
import Solcore.Syntax.Parser.Signatures
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Parser.Types
import Solcore.Syntax.Parser.Tokens
import Solcore.Syntax.Foundation
import Solcore.Syntax.Type

/-!
Parsers for declarations.

Main declarations: `functionDecl`, `constructorDecl`, `fallbackDecl`, `enumDecl`,
`typeAlias`, `traitDecl`, `implDecl`, `contractDecl`, `deriveAttribute`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Function
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse an ordinary named function and its root-tail-enabled body. -/
def functionDecl
    (location : FunctionLocation) : Parser FunctionDecl := do
  let signature ← functionSignature location
  let body ← isolateBlock (block .allow)
  pure {
    span := SourceSpan.cover signature.span body.span
    value := { signature, body }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.ContractEntry
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractEntryInternals

def entryParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

/-- Parse one optional contract-entry modifier marker. -/
def optionalModifier (modifier : HardKeyword) : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state modifier then
    pure (some (← keyword modifier .contractMember).span)
  else
    pure none

def implicitPublicModifiers
    (declaration : HardKeyword) : Parser (Option SourceSpan) := do
  let publicMarker ← optionalModifier .publicKw
  match publicMarker with
  | some span =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
  | none => pure ()
  optionalModifier .payableKw

end ContractEntryInternals

/-- Parse a contract constructor with an explicitly non-tail body. -/
def constructorDecl : Parser ConstructorDecl := do
  let marker ← keyword .constructorKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .constructorKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

/-- Parse a fallback entry point while retaining invalid parameters. -/
def fallbackDecl : Parser FallbackDecl := do
  let marker ← keyword .fallbackKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  if parameters.elements.isEmpty then
    pure ()
  else
    let _ ← emitDiagnostic {
      span := parameters.span
      kind := .constraintViolation .fallbackRequiresNoParameters
    }
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .fallbackKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Derive
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace DeriveTargetInternals

/-- Reserved hard keywords accepted with a diagnostic inside derive paths. -/
def reservedDeriveKeyword? : TokenKind → Option HardKeyword
  | .keyword value => match value with
    | .importKw | .exportKw | .pragmaKw | .typeKw | .dataKw |
        .classKw | .instanceKw | .contractKw | .publicKw | .payableKw |
        .functionKw | .constructorKw | .fallbackKw | .forallKw |
        .defaultKw => some value
    | _ => none
  | _ => none

/-- Parse one proof-visible component of a derive target. -/
def deriveComponent : Parser Identifier := fun state =>
  match state.peek? with
  | some token => match reservedDeriveKeyword? token.value with
    | some keywordValue =>
        let name : Identifier := {
          span := token.span
          value := keywordValue.spelling
        }
        .ok name (({ state with cursor := state.cursor + 1 }).emit {
          span := token.span
          kind := .constraintViolation (.reservedDeriveTarget keywordValue)
        })
    | none => identifier .topItem state
  | none => rejectAt state { head := .identifier, tail := [] } .topItem

/-- Finish a derive target from its first, last, and reversed tail components. -/
def finishDeriveTarget (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply DeriveTarget :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := { components := { head := first, tail := tailRev.reverse } }
  } state

/-- Fuel-bounded dotted-tail loop used by the public derive-target parser. -/
def deriveTargetTail (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply DeriveTarget
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot .topItem state with
        | .ok _ afterDot =>
            match deriveComponent afterDot with
            | .ok component next =>
                deriveTargetTail first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishDeriveTarget first last tailRev state

end DeriveTargetInternals

open DeriveTargetInternals

/-- Parse one dotted trait path inside `derive`. -/
def deriveTarget : Parser DeriveTarget := fun state =>
  match deriveComponent state with
  | .ok first next =>
      deriveTargetTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

namespace DeriveAttributeInternals

/-- Proof-visible normal path for the public derive-attribute parser. -/
def valid : Parser DeriveAttribute := do
  let hash ← symbol .hash .topItem
  let _ ← symbol .leftBracket .topItem
  let _ ← contextual .derive .topItem
  let targets ← delimitedNoTrailing .leftParen .rightParen true
    deriveTarget .topItem .topLevel
  let closing ← symbol .rightBracket .topItem
  let span := SourceSpan.cover hash.span closing.span
  if targets.elements.isEmpty then
    let _ ← emitDiagnostic {
      span
      kind := .constraintViolation .deriveRequiresTarget
    }
  else
    pure ()
  pure { span, value := { targets } }

/-- Proof-visible lookahead for a contract field following derive recovery. -/
def startsDeriveContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

/-- Proof-visible declaration boundary at which derive recovery stops. -/
def atDeriveDeclarationBoundary (state : State) : Bool :=
  atTopItemStart state || startsDeriveContractField state ||
    isSymbol state .rightBrace

/-- Build the common recovered value; exposed only for proof modules. -/
def finishRecovered (hash last : SourceSpan)
    (constraint : ParseConstraint) (state : State) : Reply DeriveAttribute :=
  let span := SourceSpan.cover hash last
  .ok {
    span
    value := { targets := { span, elements := [] } }
  } (state.emit { span, kind := .constraintViolation constraint })

/-- Scan a malformed derive tail; exposed only for proof modules. -/
def recoverTail (hash last : SourceSpan) :
    Nat → State → Reply DeriveAttribute
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if isSymbol state .rightBracket then
        match symbol .rightBracket .topItem state with
        | .ok closing next =>
            finishRecovered hash closing.span
              .malformedDeriveAttribute next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else if state.atEnd || atDeriveDeclarationBoundary state then
        finishRecovered hash last .unclosedDeriveAttribute state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTail hash token.span fuel next
        | none => finishRecovered hash last .unclosedDeriveAttribute state

/-- Proof-visible recovery path for the public derive-attribute parser. -/
def recovered : Parser DeriveAttribute := fun state =>
  match symbol .hash .topItem state with
  | .ok hash afterHash =>
      match symbol .leftBracket .topItem afterHash with
      | .ok opening next =>
          recoverTail hash.span opening.span
            (next.remainingCount + 1) next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end DeriveAttributeInternals

/--
Parse one canonical derive attribute. Once `#[` has been consumed, malformed
and unclosed forms become empty recovered attributes without consuming the next
declaration boundary.
-/
def deriveAttribute : Parser DeriveAttribute :=
  orElse DeriveAttributeInternals.valid DeriveAttributeInternals.recovered

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Enum
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace EnumInternals

/-- Parse the optional tuple payload of one enum constructor. -/
def enumConstructorFields : Parser (Option (DelimitedList TypeExpr)) := do
  let state ← getState
  if isSymbol state .leftParen then
    pure (some (← delimitedNoTrailing .leftParen .rightParen true typeExpr
      .typeExpr .topLevel))
  else
    pure none

/-- Parse one enum constructor and its optional tuple payload. -/
def enumConstructor : Parser EnumConstructor := do
  let name ← identifier .topItem
  let fields ← enumConstructorFields
  let endSpan := fields.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover name.span endSpan
    value := { leadingComments := [], name, fields }
  }

structure EnumBody where
  span : SourceSpan
  constructors : List EnumConstructor

def closeEnumBody (opening : Token)
    (constructorsRev : List EnumConstructor) : Parser EnumBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    constructors := constructorsRev.reverse
  }

def enumConstructors (opening : Token) :
    Nat → List EnumConstructor → State → Reply EnumBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, constructorsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .topItem state with
        | .ok _ afterComma =>
            if isSymbol afterComma .rightBrace then
              closeEnumBody opening constructorsRev afterComma
            else
              let before := afterComma.cursor
              match enumConstructor afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    enumConstructors opening fuel (value :: constructorsRev) next
                  else
                    .invariant (.noProgress .topLevel next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        closeEnumBody opening constructorsRev state

def enumBody : Parser EnumBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      if isSymbol next .rightBrace then
        closeEnumBody opening [] next
      else
        match enumConstructor next with
        | .ok first afterFirst =>
            enumConstructors opening (afterFirst.remainingCount + 1)
              [first] afterFirst
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end EnumInternals

/-- Parse a canonical algebraic `enum` declaration. -/
def enumDecl
    (deriveAttribute : Option DeriveAttribute) : Parser EnumDecl := do
  let marker ← contextual .enum .topItem
  let name ← identifier .topItem
  let parameters ← optionalGenericParameters
  let body ← EnumInternals.enumBody
  let startSpan := deriveAttribute.map (fun derive => derive.span)
    |>.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      deriveAttribute
      name
      parameters
      bodySpan := body.span
      constructors := body.constructors
    }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.TypeAlias
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

def finishRecoveredType (span : SourceSpan)
    (state : State) : Reply TypeExpr :=
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .typeAliasValue
  })

def recoverTypeAliasValueAux (first last : SourceSpan) :
    Nat → State → Reply TypeExpr
  | 0, state => .invariant (.fuelExhausted .typeAlias state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .semicolon then
        finishRecoveredType (SourceSpan.cover first last) state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTypeAliasValueAux first token.span fuel next
        | none => finishRecoveredType (SourceSpan.cover first last) state

/-- Consume the nonempty malformed RHS prefix before the first semicolon. -/
def recoverTypeAliasValue (state : State) : Reply TypeExpr :=
  if state.atEnd || isSymbol state .semicolon then
    rejectAt state { head := .typeExpr, tail := [] } .typeAlias
  else
    match state.advance? with
    | some (token, next) =>
        recoverTypeAliasValueAux token.span token.span
          (next.remainingCount + 1) next
    | none => rejectAt state { head := .typeExpr, tail := [] } .typeAlias

def parseAliasValue : Parser TypeExpr := fun state =>
  match typeExpr state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := {
        failedState with
        cursor := state.cursor
      }
      if rewound.atEnd || isSymbol rewound .semicolon then
        .reject failure rewound
      else
        recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end TypeAliasInternals

/-- Parse the optional parenthesized parameter list of a type alias. -/
def parseTypeAliasParameters : Parser (Option (DelimitedList Identifier)) := do
  let state ← getState
  if isSymbol state .leftParen then
    let values ← delimited .leftParen .rightParen true
      (identifier .parameter) .typeAlias .typeAlias
    pure (some values)
  else
    pure none

/-- Parse one canonical transparent type-alias declaration. -/
def typeAlias : Parser TypeAliasDecl := do
  let typeKeyword ← keyword .typeKw .typeAlias
  let name ← identifier .typeAlias
  let parameters ← parseTypeAliasParameters
  let _ ← symbol .equal .typeAlias
  let value ← TypeAliasInternals.parseAliasValue
  let semicolon ← symbol .semicolon .typeAlias
  pure {
    span := SourceSpan.cover typeKeyword.span semicolon.span
    value := {
      name
      parameters
      value
    }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Trait
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TraitInternals

/-- Parse one signature-only trait method. -/
def traitMethod : Parser TraitMethod := do
  let signature ← functionSignature .module
  let semicolon ← symbol .semicolon .topItem
  pure {
    span := SourceSpan.cover signature.span semicolon.span
    value := {
      leadingComments := []
      signature
      semicolon := semicolon.span
    }
  }

structure TraitBody where
  span : SourceSpan
  methods : List TraitMethod

def closeTraitBody (opening : Token)
    (methodsRev : List TraitMethod) : Parser TraitBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

def traitMethods (opening : Token) :
    Nat → List TraitMethod → State → Reply TraitBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeTraitBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match traitMethod state with
        | .ok value next =>
            if next.cursor > before then
              traitMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

def traitBody : Parser TraitBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      traitMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end TraitInternals

/-- Parse a canonical trait declaration and signature-only methods. -/
def traitDecl : Parser TraitDecl := do
  let marker ← contextual .trait .topItem
  let name ← identifier .topItem
  let genericParameters ← genericParameters
  let whereClause ← whereClause
  let body ← TraitInternals.traitBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Impl
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/- Proof-visible implementation-body parser components. -/
namespace ImplInternals

/-- Require at least one implementation head argument. -/
def requireImplArguments (values : DelimitedList TypeExpr) :
    Parser (NonemptyDelimitedList TypeExpr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse one function member of an implementation body. -/
def implMethod : Parser ImplMethod := do
  let declaration ← functionDecl .module
  pure {
    span := declaration.span
    value := { leadingComments := [], declaration }
  }

/-- The brace range and methods accumulated by implementation-body parsing. -/
structure ImplBody where
  span : SourceSpan
  methods : List ImplMethod

/-- Close an implementation body and restore source order. -/
def closeImplBody (opening : Token)
    (methodsRev : List ImplMethod) : Parser ImplBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

/-- Parse implementation methods with explicit fuel and progress checks. -/
def implMethods (opening : Token) :
    Nat → List ImplMethod → State → Reply ImplBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeImplBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match implMethod state with
        | .ok value next =>
            if next.cursor > before then
              implMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

/-- Parse a complete brace-delimited implementation body. -/
def implBody : Parser ImplBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      implMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse an optional leading `default` marker. -/
def implDefaultMarker : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state .defaultKw then
    pure (some (← keyword .defaultKw .topItem).span)
  else
    pure none

/-- Parse the declaration suffix following its optional default marker. -/
def implDeclAfterDefault (defaultMarker : Option SourceSpan) :
    Parser ImplDecl := do
  let marker ← contextual .impl .topItem
  let genericParameters ← optionalGenericParameters
  let traitName ← identifier .topItem
  let arguments ← delimited .less .greater false typeExpr
    .typeExpr .topLevel
  let headArguments ← requireImplArguments arguments
  let whereClause ← whereClause
  let body ← implBody
  let startSpan := defaultMarker.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      defaultMarker
      genericParameters
      traitName
      headArguments
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end ImplInternals

open ImplInternals

/-- Parse a canonical optional-default trait implementation. -/
def implDecl : Parser ImplDecl := do
  let defaultMarker ← implDefaultMarker
  implDeclAfterDefault defaultMarker

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Contract
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractInternals

def optionalFieldInitializer
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .equal then
    let _ ← symbol .equal .contractMember
    pure (some (← expression))
  else
    pure none

def contractField (expression : Parser Expr) : Parser ContractField := do
  let name ← identifier .contractMember
  let _ ← symbol .colon .contractMember
  let type ← typeExpr
  let initializer ← optionalFieldInitializer expression
  let semicolon ← symbol .semicolon .contractMember
  pure {
    span := SourceSpan.cover name.span semicolon.span
    value := { name, type, initializer }
  }

end ContractInternals

namespace ContractInternals

def wrapField (declaration : ContractField) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .field declaration
}

def wrapContractFunction
    (declaration : FunctionDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .function declaration
}

def wrapConstructor
    (declaration : ConstructorDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .constructor declaration
}

def wrapFallback (declaration : FallbackDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .fallback declaration
}

def wrapContractTypeAlias
    (declaration : TypeAliasDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

def wrapContractEnum (declaration : EnumDecl) : ContractMember := {
  span := declaration.span
  leadingComments := []
  value := .enum declaration
}

def mapMember {alpha : Type} (parser : Parser alpha)
    (wrap : alpha → ContractMember) : Parser ContractMember := do
  pure (wrap (← parser))

end ContractInternals

def ContractInternals.extendContractMemberStart (prefixSpan : SourceSpan)
    (member : ContractMember) : ContractMember :=
  let span := SourceSpan.cover prefixSpan member.span
  let value := match member.value with
    | .field declaration => .field { declaration with span }
    | .function declaration => .function { declaration with span }
    | .constructor declaration => .constructor { declaration with span }
    | .fallback declaration => .fallback { declaration with span }
    | .typeAlias declaration => .typeAlias { declaration with span }
    | .enum declaration => .enum { declaration with span }
    | .error => .error
  { member with span, value }

namespace ContractInternals

def startsContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

def rejectedContractMember : Parser ContractMember := fun state =>
  rejectAt state { head := .topItem, tail := [] } .contractMember

def contractMemberParser (state : State) : Parser ContractMember :=
  if startsContractField state then
    mapMember (contractField expression) wrapField
  else if isKeyword state .functionKw then
    mapMember (functionDecl .contract) wrapContractFunction
  else if isKeyword state .constructorKw then
    mapMember constructorDecl wrapConstructor
  else if isKeyword state .fallbackKw then
    mapMember fallbackDecl wrapFallback
  else if isKeyword state .typeKw then
    mapMember typeAlias wrapContractTypeAlias
  else if isContextual state .enum then
    mapMember (enumDecl none) wrapContractEnum
  else
    rejectedContractMember

def contractMemberCore : Parser ContractMember := fun state =>
  contractMemberParser state state

end ContractInternals

def ContractInternals.attachContractDerive (derive : DeriveAttribute)
    (member : ContractMember) : Parser ContractMember :=
  match member.value with
  | .enum declaration =>
      let span := SourceSpan.cover derive.span declaration.span
      pure {
        member with
        span
        value := .enum {
          declaration with
          span
          value := { declaration.value with deriveAttribute := some derive }
        }
      }
  | _ => do
      let _ ← emitDiagnostic {
        span := derive.span
        kind := .constraintViolation .deriveOnlyEnum
      }
      pure (ContractInternals.extendContractMemberStart derive.span member)

def ContractInternals.contractMemberWithAttribute : Parser ContractMember :=
    fun state =>
  if isSymbol state .hash then
    match deriveAttribute state with
    | .ok derive afterDerive =>
        match ContractInternals.contractMemberCore afterDerive with
        | .ok member next =>
            ContractInternals.attachContractDerive derive member next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    ContractInternals.contractMemberCore state

namespace ContractInternals

def atContractRecoveryBoundary (state : State) : Bool :=
  isSymbol state .hash || isKeyword state .functionKw ||
    isKeyword state .constructorKw ||
    isKeyword state .fallbackKw || isKeyword state .typeKw ||
    isSymbol state .rightBrace || isContextual state .enum

def finishRecoveredMember (first last : SourceSpan)
    (state : State) : Reply ContractMember :=
  let span := SourceSpan.cover first last
  .ok { span, leadingComments := [], value := .error } (state.emit {
    span
    kind := .recovered .contractMember
  })

def recoverContractMemberAux (first last : SourceSpan) :
    Nat → State → Reply ContractMember
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || atContractRecoveryBoundary state then
        finishRecoveredMember first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverContractMemberAux first token.span fuel next
        | none => finishRecoveredMember first last state

def recoverContractMember (state : State) : Reply ContractMember :=
  match state.advance? with
  | some (token, next) =>
      recoverContractMemberAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .topItem, tail := [] } .contractMember

end ContractInternals

namespace ContractInternals

structure ContractBody where
  span : SourceSpan
  members : List ContractMember

def closeContractBody (opening : Token)
    (membersRev : List ContractMember) : Parser ContractBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    members := membersRev.reverse
  }

def contractMembers (opening : Token) :
    Nat → List ContractMember → State → Reply ContractBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, membersRev, state =>
      if isSymbol state .rightBrace then
        closeContractBody opening membersRev state
      else if state.atEnd then
        match symbol .rightBrace .topItem state with
        | .ok _ _ => .invariant (.noProgress .topLevel state.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        match ContractInternals.contractMemberWithAttribute state with
        | .ok member next =>
            if next.cursor > state.cursor then
              contractMembers opening fuel (member :: membersRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure failedState =>
            let rewound := { failedState with cursor := state.cursor }
            if ContractInternals.atContractRecoveryBoundary state then
              .reject failure rewound
            else
              match ContractInternals.recoverContractMember rewound with
              | .ok member next =>
                  contractMembers opening fuel (member :: membersRev) next
              | .reject recoveryFailure next => .reject recoveryFailure next
              | .invariant error => .invariant error
        | .invariant error => .invariant error

def contractBody : Parser ContractBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      contractMembers opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ContractInternals

/-- Parse a canonical contract while preserving member source order. -/
def contractDecl : Parser ContractDecl := do
  let marker ← keyword .contractKw .topItem
  let name ← identifier .topItem
  let genericParameters ← optionalGenericParameters
  let body ← ContractInternals.contractBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      bodySpan := body.span
      members := body.members
    }
  }

end Solcore.Syntax.Parser
end
