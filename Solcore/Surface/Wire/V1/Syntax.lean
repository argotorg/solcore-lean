import Solcore.Surface.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

/-!
The Surface v1 wire syntax is closed independently of the evolving internal
Surface syntax. Refined textual atoms ensure that every constructible wire
value has a canonical lexical payload, while projections from internal values
return `Option` explicitly.
-/

private def isAsciiLower (character : Char) : Bool :=
  'a' <= character && character <= 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' <= character && character <= 'Z'

private def isAsciiDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

private def isAsciiLetter (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isAsciiHexDigit (character : Char) : Bool :=
  isAsciiDigit character ||
    ('a' <= character && character <= 'f') ||
    ('A' <= character && character <= 'F')

private def isHardKeyword (value : String) : Bool :=
  value == "function" ||
    value == "let" ||
    value == "if" ||
    value == "else" ||
    value == "return"

def identifierTextValid (value : String) : Bool :=
  (match value.toList with
  | [] => false
  | first :: rest =>
      isAsciiLetter first &&
        rest.all (fun character =>
          isAsciiLetter character ||
            isAsciiDigit character ||
            character = '_')) &&
    !isHardKeyword value

def decimalDigitsValid (value : String) : Bool :=
  !value.isEmpty && value.toList.all isAsciiDigit

def hexadecimalDigitsValid (value : String) : Bool :=
  !value.isEmpty && value.toList.all isAsciiHexDigit

theorem identifierTextValid_eq_tokenKind_isCanonical (value : String) :
    identifierTextValid value =
      (Solcore.Surface.TokenKind.identifier value).isCanonical := by
  rw [Solcore.Surface.TokenKind.identifier_isCanonical_equation]
  rfl

theorem decimalDigitsValid_eq_tokenKind_isCanonical (value : String) :
    decimalDigitsValid value =
      (Solcore.Surface.TokenKind.decimal value).isCanonical := by
  rw [Solcore.Surface.TokenKind.decimal_isCanonical_equation]
  rfl

theorem hexadecimalDigitsValid_eq_tokenKind_isCanonical (value : String) :
    hexadecimalDigitsValid value =
      (Solcore.Surface.TokenKind.hexadecimal value).isCanonical := by
  rw [Solcore.Surface.TokenKind.hexadecimal_isCanonical_equation]
  rfl

structure IdentifierText where
  value : String
  valid : identifierTextValid value = true
  deriving Repr, DecidableEq

namespace IdentifierText

instance : BEq IdentifierText :=
  ⟨fun first second => first.value == second.value⟩

def ofString? (value : String) : Option IdentifierText :=
  if valid : identifierTextValid value = true then
    some { value, valid }
  else
    none

@[simp] theorem ofString?_value (value : IdentifierText) :
    ofString? value.value = some value := by
  cases value with
  | mk text valid =>
      simp [ofString?, valid]

theorem value_eq_of_ofString?_eq_some
    {value : String}
    {text : IdentifierText}
    (projection : ofString? value = some text) :
    text.value = value := by
  unfold ofString? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
  next _ =>
    simp at projection

end IdentifierText

structure DecimalDigits where
  value : String
  valid : decimalDigitsValid value = true
  deriving Repr, DecidableEq

namespace DecimalDigits

instance : BEq DecimalDigits :=
  ⟨fun first second => first.value == second.value⟩

def ofString? (value : String) : Option DecimalDigits :=
  if valid : decimalDigitsValid value = true then
    some { value, valid }
  else
    none

@[simp] theorem ofString?_value (value : DecimalDigits) :
    ofString? value.value = some value := by
  cases value with
  | mk digits valid =>
      simp [ofString?, valid]

theorem value_eq_of_ofString?_eq_some
    {value : String}
    {digits : DecimalDigits}
    (projection : ofString? value = some digits) :
    digits.value = value := by
  unfold ofString? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
  next _ =>
    simp at projection

end DecimalDigits

structure HexadecimalDigits where
  value : String
  valid : hexadecimalDigitsValid value = true
  deriving Repr, DecidableEq

namespace HexadecimalDigits

instance : BEq HexadecimalDigits :=
  ⟨fun first second => first.value == second.value⟩

def ofString? (value : String) : Option HexadecimalDigits :=
  if valid : hexadecimalDigitsValid value = true then
    some { value, valid }
  else
    none

@[simp] theorem ofString?_value (value : HexadecimalDigits) :
    ofString? value.value = some value := by
  cases value with
  | mk digits valid =>
      simp [ofString?, valid]

theorem value_eq_of_ofString?_eq_some
    {value : String}
    {digits : HexadecimalDigits}
    (projection : ofString? value = some digits) :
    digits.value = value := by
  unfold ofString? at projection
  split at projection
  next _ =>
    have equality := Option.some.inj projection
    rw [← equality]
  next _ =>
    simp at projection

end HexadecimalDigits

structure SourceSpan where
  source : String
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

namespace SourceSpan

def toSurface (span : SourceSpan) : Solcore.Surface.SourceSpan := {
  source := span.source
  startByte := span.startByte
  endByte := span.endByte
}

def ofSurface : Solcore.Surface.SourceSpan -> SourceSpan
  | ⟨source, startByte, endByte⟩ => { source, startByte, endByte }

@[simp] theorem ofSurface_toSurface (span : SourceSpan) :
    ofSurface span.toSurface = span := by
  cases span
  rfl

@[simp] theorem toSurface_ofSurface (span : Solcore.Surface.SourceSpan) :
    (ofSurface span).toSurface = span := by
  cases span
  rfl

end SourceSpan

structure Name where
  span : SourceSpan
  text : IdentifierText
  deriving Repr, BEq, DecidableEq

namespace Name

def toSurface (name : Name) : Solcore.Surface.Name := {
  span := name.span.toSurface
  value := name.text.value
}

def ofSurface? : Solcore.Surface.Name -> Option Name
  | ⟨span, value⟩ => do
      let text <- IdentifierText.ofString? value
      some {
        span := SourceSpan.ofSurface span
        text
      }

@[simp] theorem ofSurface?_toSurface (name : Name) :
    ofSurface? name.toSurface = some name := by
  cases name
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceName : Solcore.Surface.Name}
    {name : Name}
    (projection : ofSurface? surfaceName = some name) :
    name.toSurface = surfaceName := by
  cases surfaceName with
  | mk span value =>
      cases textProjection : IdentifierText.ofString? value with
      | none =>
          simp [ofSurface?, textProjection] at projection
      | some text =>
          simp [ofSurface?, textProjection] at projection
          subst name
          simp [toSurface,
            IdentifierText.value_eq_of_ofString?_eq_some textProjection]

end Name

inductive TypeSpelling where
  | bool
  | word
  deriving Repr, BEq, DecidableEq

namespace TypeSpelling

def text : TypeSpelling -> String
  | .bool => "bool"
  | .word => "word"

def ofString? (value : String) : Option TypeSpelling :=
  if value = "bool" then
    some .bool
  else if value = "word" then
    some .word
  else
    none

@[simp] theorem ofString?_text (spelling : TypeSpelling) :
    ofString? spelling.text = some spelling := by
  cases spelling <;> rfl

theorem text_eq_of_ofString?_eq_some
    {value : String}
    {spelling : TypeSpelling}
    (projection : ofString? value = some spelling) :
    spelling.text = value := by
  unfold ofString? at projection
  split at projection
  next valueIsBool =>
    subst value
    have equality := Option.some.inj projection
    subst spelling
    rfl
  next valueIsNotBool =>
    split at projection
    next valueIsWord =>
      subst value
      have equality := Option.some.inj projection
      subst spelling
      rfl
    next valueIsNotWord =>
      simp at projection

end TypeSpelling

structure TypeSpellingOccurrence where
  span : SourceSpan
  text : TypeSpelling
  deriving Repr, BEq, DecidableEq

namespace TypeSpellingOccurrence

def toSurface (occurrence : TypeSpellingOccurrence) : Solcore.Surface.Name := {
  span := occurrence.span.toSurface
  value := occurrence.text.text
}

def ofSurface? : Solcore.Surface.Name -> Option TypeSpellingOccurrence
  | ⟨span, value⟩ => do
      let text <- TypeSpelling.ofString? value
      some {
        span := SourceSpan.ofSurface span
        text
      }

@[simp] theorem ofSurface?_toSurface (occurrence : TypeSpellingOccurrence) :
    ofSurface? occurrence.toSurface = some occurrence := by
  cases occurrence
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceName : Solcore.Surface.Name}
    {occurrence : TypeSpellingOccurrence}
    (projection : ofSurface? surfaceName = some occurrence) :
    occurrence.toSurface = surfaceName := by
  cases surfaceName with
  | mk span value =>
      cases spellingProjection : TypeSpelling.ofString? value with
      | none =>
          simp [ofSurface?, spellingProjection] at projection
      | some spelling =>
          simp [ofSurface?, spellingProjection] at projection
          subst occurrence
          simp [toSurface,
            TypeSpelling.text_eq_of_ofString?_eq_some spellingProjection]

end TypeSpellingOccurrence

inductive TypeSyntax where
  | unit (span : SourceSpan)
  | named (name : TypeSpellingOccurrence)
  deriving Repr, BEq, DecidableEq

namespace TypeSyntax

def toSurface : TypeSyntax -> Solcore.Surface.TypeSyntax
  | .unit span => .unit span.toSurface
  | .named occurrence => .named occurrence.toSurface

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.TypeSyntax -> Option TypeSyntax
  | .unit span => some (.unit (SourceSpan.ofSurface span))
  | .named occurrence =>
      .named <$> TypeSpellingOccurrence.ofSurface? occurrence
  | _ => none

@[simp] theorem ofSurface?_toSurface (type : TypeSyntax) :
    ofSurface? type.toSurface = some type := by
  cases type <;> simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceType : Solcore.Surface.TypeSyntax}
    {type : TypeSyntax}
    (projection : ofSurface? surfaceType = some type) :
    type.toSurface = surfaceType := by
  cases surfaceType with
  | unit span =>
      simp [ofSurface?] at projection
      subst type
      simp [toSurface]
  | named surfaceName =>
      cases occurrenceProjection :
          TypeSpellingOccurrence.ofSurface? surfaceName with
      | none =>
          simp [ofSurface?, occurrenceProjection] at projection
      | some occurrence =>
          simp [ofSurface?, occurrenceProjection] at projection
          subst type
          simp [toSurface,
            TypeSpellingOccurrence.toSurface_eq_of_ofSurface?_eq_some
              occurrenceProjection]

end TypeSyntax

inductive IntegerLiteral where
  | decimal (span : SourceSpan) (digits : DecimalDigits)
  | hexadecimal (span : SourceSpan) (digits : HexadecimalDigits)
  deriving Repr, BEq, DecidableEq

namespace IntegerLiteral

def toSurface : IntegerLiteral -> Solcore.Surface.IntegerLiteral
  | .decimal span digits => {
      base := .decimal
      digits := digits.value
      span := span.toSurface
    }
  | .hexadecimal span digits => {
      base := .hexadecimal
      digits := digits.value
      span := span.toSurface
    }

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.IntegerLiteral -> Option IntegerLiteral
  | ⟨.decimal, digits, span⟩ => do
      let digits <- DecimalDigits.ofString? digits
      some (.decimal (SourceSpan.ofSurface span) digits)
  | ⟨.hexadecimal, digits, span⟩ => do
      let digits <- HexadecimalDigits.ofString? digits
      some (.hexadecimal (SourceSpan.ofSurface span) digits)
  | _ => none

@[simp] theorem ofSurface?_toSurface (literal : IntegerLiteral) :
    ofSurface? literal.toSurface = some literal := by
  cases literal <;> simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceLiteral : Solcore.Surface.IntegerLiteral}
    {literal : IntegerLiteral}
    (projection : ofSurface? surfaceLiteral = some literal) :
    literal.toSurface = surfaceLiteral := by
  cases surfaceLiteral with
  | mk base digits span =>
      cases base with
      | decimal =>
          cases digitsProjection : DecimalDigits.ofString? digits with
          | none =>
              simp [ofSurface?, digitsProjection] at projection
          | some wireDigits =>
              simp [ofSurface?, digitsProjection] at projection
              subst literal
              simp [toSurface,
                DecimalDigits.value_eq_of_ofString?_eq_some digitsProjection]
      | hexadecimal =>
          cases digitsProjection : HexadecimalDigits.ofString? digits with
          | none =>
              simp [ofSurface?, digitsProjection] at projection
          | some wireDigits =>
              simp [ofSurface?, digitsProjection] at projection
              subst literal
              simp [toSurface,
                HexadecimalDigits.value_eq_of_ofString?_eq_some
                  digitsProjection]

end IntegerLiteral

inductive UnaryOp where
  | not
  deriving Repr, BEq, DecidableEq

namespace UnaryOp

def toSurface : UnaryOp -> Solcore.Surface.UnaryOp
  | .not => .not

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.UnaryOp -> Option UnaryOp
  | .not => some .not
  | _ => none

@[simp] theorem ofSurface?_toSurface (operator : UnaryOp) :
    ofSurface? operator.toSurface = some operator := by
  cases operator
  rfl

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceOperator : Solcore.Surface.UnaryOp}
    {operator : UnaryOp}
    (projection : ofSurface? surfaceOperator = some operator) :
    operator.toSurface = surfaceOperator := by
  cases surfaceOperator
  cases operator
  rfl

end UnaryOp

inductive BinaryOp where
  | mul
  | div
  | mod
  | add
  | sub
  | bitAnd
  | bitXor
  | bitOr
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  deriving Repr, BEq, DecidableEq

namespace BinaryOp

def toSurface : BinaryOp -> Solcore.Surface.BinaryOp
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .add => .add
  | .sub => .sub
  | .bitAnd => .bitAnd
  | .bitXor => .bitXor
  | .bitOr => .bitOr
  | .lt => .lt
  | .gt => .gt
  | .le => .le
  | .ge => .ge
  | .eq => .eq
  | .ne => .ne

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.BinaryOp -> Option BinaryOp
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .add => some .add
  | .sub => some .sub
  | .bitAnd => some .bitAnd
  | .bitXor => some .bitXor
  | .bitOr => some .bitOr
  | .lt => some .lt
  | .gt => some .gt
  | .le => some .le
  | .ge => some .ge
  | .eq => some .eq
  | .ne => some .ne
  | _ => none

@[simp] theorem ofSurface?_toSurface (operator : BinaryOp) :
    ofSurface? operator.toSurface = some operator := by
  cases operator <;> rfl

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceOperator : Solcore.Surface.BinaryOp}
    {operator : BinaryOp}
    (projection : ofSurface? surfaceOperator = some operator) :
    operator.toSurface = surfaceOperator := by
  cases surfaceOperator <;>
    simp only [ofSurface?, Option.some.injEq] at projection
  all_goals subst operator <;> rfl

end BinaryOp

structure UnaryOperator where
  span : SourceSpan
  operator : UnaryOp
  deriving Repr, BEq, DecidableEq

namespace UnaryOperator

def toSurface (operator : UnaryOperator) :
    Solcore.Surface.Located Solcore.Surface.UnaryOp := {
  span := operator.span.toSurface
  value := operator.operator.toSurface
}

def ofSurface? :
    Solcore.Surface.Located Solcore.Surface.UnaryOp -> Option UnaryOperator
  | ⟨span, value⟩ => do
      let operator <- UnaryOp.ofSurface? value
      some {
        span := SourceSpan.ofSurface span
        operator
      }

@[simp] theorem ofSurface?_toSurface (operator : UnaryOperator) :
    ofSurface? operator.toSurface = some operator := by
  cases operator
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceOperator : Solcore.Surface.Located Solcore.Surface.UnaryOp}
    {operator : UnaryOperator}
    (projection : ofSurface? surfaceOperator = some operator) :
    operator.toSurface = surfaceOperator := by
  cases surfaceOperator with
  | mk span value =>
      cases operatorProjection : UnaryOp.ofSurface? value with
      | none =>
          simp [ofSurface?, operatorProjection] at projection
      | some wireOperator =>
          simp [ofSurface?, operatorProjection] at projection
          subst operator
          simp [toSurface,
            UnaryOp.toSurface_eq_of_ofSurface?_eq_some operatorProjection]

end UnaryOperator

structure BinaryOperator where
  span : SourceSpan
  operator : BinaryOp
  deriving Repr, BEq, DecidableEq

namespace BinaryOperator

def toSurface (operator : BinaryOperator) :
    Solcore.Surface.Located Solcore.Surface.BinaryOp := {
  span := operator.span.toSurface
  value := operator.operator.toSurface
}

def ofSurface? :
    Solcore.Surface.Located Solcore.Surface.BinaryOp -> Option BinaryOperator
  | ⟨span, value⟩ => do
      let operator <- BinaryOp.ofSurface? value
      some {
        span := SourceSpan.ofSurface span
        operator
      }

@[simp] theorem ofSurface?_toSurface (operator : BinaryOperator) :
    ofSurface? operator.toSurface = some operator := by
  cases operator
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceOperator : Solcore.Surface.Located Solcore.Surface.BinaryOp}
    {operator : BinaryOperator}
    (projection : ofSurface? surfaceOperator = some operator) :
    operator.toSurface = surfaceOperator := by
  cases surfaceOperator with
  | mk span value =>
      cases operatorProjection : BinaryOp.ofSurface? value with
      | none =>
          simp [ofSurface?, operatorProjection] at projection
      | some wireOperator =>
          simp [ofSurface?, operatorProjection] at projection
          subst operator
          simp [toSurface,
            BinaryOp.toSurface_eq_of_ofSurface?_eq_some operatorProjection]

end BinaryOperator

inductive Expr where
  | unit (span : SourceSpan)
  | integer (literal : IntegerLiteral)
  | name (name : Name)
  | group (span : SourceSpan) (inner : Expr)
  | call (span : SourceSpan) (callee : Name) (arguments : List Expr)
  | unary (span : SourceSpan) (operator : UnaryOperator) (operand : Expr)
  | binary
      (span : SourceSpan)
      (operator : BinaryOperator)
      (left : Expr)
      (right : Expr)
  | ifThenElse
      (span : SourceSpan)
      (condition : Expr)
      (thenBranch : Expr)
      (elseBranch : Expr)
  deriving Repr, BEq

namespace Expr

def toSurface : Expr -> Solcore.Surface.Expr
  | .unit span => .unit span.toSurface
  | .integer literal => .integer literal.toSurface
  | .name identifier => .name identifier.toSurface
  | .group span inner => .group span.toSurface inner.toSurface
  | .call span callee arguments =>
      .call span.toSurface callee.toSurface (arguments.map toSurface)
  | .unary span operator operand =>
      .unary span.toSurface operator.toSurface operand.toSurface
  | .binary span operator left right =>
      .binary span.toSurface operator.toSurface left.toSurface right.toSurface
  | .ifThenElse span condition thenBranch elseBranch =>
      .ifThenElse span.toSurface condition.toSurface
        thenBranch.toSurface elseBranch.toSurface
termination_by expression => sizeOf expression

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.Expr -> Option Expr
  | .unit span => some (.unit (SourceSpan.ofSurface span))
  | .integer literal => .integer <$> IntegerLiteral.ofSurface? literal
  | .name identifier => .name <$> Name.ofSurface? identifier
  | .group span inner => do
      let inner <- ofSurface? inner
      some (.group (SourceSpan.ofSurface span) inner)
  | .call span callee arguments => do
      let callee <- Name.ofSurface? callee
      let arguments <- arguments.mapM ofSurface?
      some (.call (SourceSpan.ofSurface span) callee arguments)
  | .unary span operator operand => do
      let operator <- UnaryOperator.ofSurface? operator
      let operand <- ofSurface? operand
      some (.unary (SourceSpan.ofSurface span) operator operand)
  | .binary span operator left right => do
      let operator <- BinaryOperator.ofSurface? operator
      let left <- ofSurface? left
      let right <- ofSurface? right
      some (.binary (SourceSpan.ofSurface span) operator left right)
  | .ifThenElse span condition thenBranch elseBranch => do
      let condition <- ofSurface? condition
      let thenBranch <- ofSurface? thenBranch
      let elseBranch <- ofSurface? elseBranch
      some (.ifThenElse (SourceSpan.ofSurface span)
        condition thenBranch elseBranch)
  | _ => none
termination_by expression => sizeOf expression

mutual

  @[simp] theorem ofSurface?_toSurface :
      (expression : Expr) ->
        ofSurface? expression.toSurface = some expression
    | .unit span => by
        simp [toSurface, ofSurface?]
    | .integer literal => by
        simp [toSurface, ofSurface?]
    | .name identifier => by
        simp [toSurface, ofSurface?]
    | .group span inner => by
        simp [toSurface, ofSurface?, ofSurface?_toSurface inner]
    | .call span callee arguments => by
        simp [toSurface, ofSurface?, listOfSurface?_toSurface arguments]
    | .unary span operator operand => by
        simp [toSurface, ofSurface?, ofSurface?_toSurface operand]
    | .binary span operator left right => by
        simp [toSurface, ofSurface?, ofSurface?_toSurface left,
          ofSurface?_toSurface right]
    | .ifThenElse span condition thenBranch elseBranch => by
        simp [toSurface, ofSurface?, ofSurface?_toSurface condition,
          ofSurface?_toSurface thenBranch, ofSurface?_toSurface elseBranch]

  @[simp] theorem listOfSurface?_toSurface :
      (expressions : List Expr) ->
        expressions.mapM (ofSurface? ∘ toSurface) = some expressions
    | [] => by rfl
    | expression :: rest => by
        simp [ofSurface?_toSurface expression,
          listOfSurface?_toSurface rest]

end

mutual

  theorem toSurface_eq_of_ofSurface?_eq_some :
      (surfaceExpression : Solcore.Surface.Expr) ->
      (expression : Expr) ->
      ofSurface? surfaceExpression = some expression ->
        expression.toSurface = surfaceExpression
    | .unit span, expression, projection => by
        simp [ofSurface?] at projection
        subst expression
        simp [toSurface]
    | .integer surfaceLiteral, expression, projection => by
        cases literalProjection : IntegerLiteral.ofSurface? surfaceLiteral with
        | none =>
            simp [ofSurface?, literalProjection] at projection
        | some literal =>
            simp [ofSurface?, literalProjection] at projection
            subst expression
            simp [toSurface,
              IntegerLiteral.toSurface_eq_of_ofSurface?_eq_some
                literalProjection]
    | .name surfaceName, expression, projection => by
        cases nameProjection : Name.ofSurface? surfaceName with
        | none =>
            simp [ofSurface?, nameProjection] at projection
        | some name =>
            simp [ofSurface?, nameProjection] at projection
            subst expression
            simp [toSurface,
              Name.toSurface_eq_of_ofSurface?_eq_some nameProjection]
    | .group span inner, expression, projection => by
        cases innerProjection : ofSurface? inner with
        | none =>
            simp [ofSurface?, innerProjection] at projection
        | some wireInner =>
            simp [ofSurface?, innerProjection] at projection
            subst expression
            simp [toSurface,
              toSurface_eq_of_ofSurface?_eq_some inner wireInner
                innerProjection]
    | .call span surfaceCallee surfaceArguments, expression, projection => by
        cases calleeProjection : Name.ofSurface? surfaceCallee with
        | none =>
            simp [ofSurface?, calleeProjection] at projection
        | some callee =>
            cases argumentsProjection :
                surfaceArguments.mapM ofSurface? with
            | none =>
                simp [ofSurface?, calleeProjection, argumentsProjection]
                  at projection
            | some arguments =>
                simp [ofSurface?, calleeProjection, argumentsProjection]
                  at projection
                subst expression
                simp [toSurface,
                  Name.toSurface_eq_of_ofSurface?_eq_some calleeProjection,
                  listToSurface_eq_of_listOfSurface?_eq_some
                    surfaceArguments arguments argumentsProjection]
    | .unary span surfaceOperator operand, expression, projection => by
        cases operatorProjection :
            UnaryOperator.ofSurface? surfaceOperator with
        | none =>
            simp [ofSurface?, operatorProjection] at projection
        | some operator =>
            cases operandProjection : ofSurface? operand with
            | none =>
                simp [ofSurface?, operatorProjection, operandProjection]
                  at projection
            | some wireOperand =>
                simp [ofSurface?, operatorProjection, operandProjection]
                  at projection
                subst expression
                simp [toSurface,
                  UnaryOperator.toSurface_eq_of_ofSurface?_eq_some
                    operatorProjection,
                  toSurface_eq_of_ofSurface?_eq_some operand wireOperand
                    operandProjection]
    | .binary span surfaceOperator left right, expression, projection => by
        cases operatorProjection :
            BinaryOperator.ofSurface? surfaceOperator with
        | none =>
            simp [ofSurface?, operatorProjection] at projection
        | some operator =>
            cases leftProjection : ofSurface? left with
            | none =>
                simp [ofSurface?, operatorProjection, leftProjection]
                  at projection
            | some wireLeft =>
                cases rightProjection : ofSurface? right with
                | none =>
                    simp [ofSurface?, operatorProjection, leftProjection,
                      rightProjection] at projection
                | some wireRight =>
                    simp [ofSurface?, operatorProjection, leftProjection,
                      rightProjection] at projection
                    subst expression
                    simp [toSurface,
                      BinaryOperator.toSurface_eq_of_ofSurface?_eq_some
                        operatorProjection,
                      toSurface_eq_of_ofSurface?_eq_some left wireLeft
                        leftProjection,
                      toSurface_eq_of_ofSurface?_eq_some right wireRight
                        rightProjection]
    | .ifThenElse span condition thenBranch elseBranch,
        expression, projection => by
        cases conditionProjection : ofSurface? condition with
        | none =>
            simp [ofSurface?, conditionProjection] at projection
        | some wireCondition =>
            cases thenProjection : ofSurface? thenBranch with
            | none =>
                simp [ofSurface?, conditionProjection, thenProjection]
                  at projection
            | some wireThen =>
                cases elseProjection : ofSurface? elseBranch with
                | none =>
                    simp [ofSurface?, conditionProjection, thenProjection,
                      elseProjection] at projection
                | some wireElse =>
                    simp [ofSurface?, conditionProjection, thenProjection,
                      elseProjection] at projection
                    subst expression
                    simp [toSurface,
                      toSurface_eq_of_ofSurface?_eq_some condition
                        wireCondition conditionProjection,
                      toSurface_eq_of_ofSurface?_eq_some thenBranch wireThen
                        thenProjection,
                      toSurface_eq_of_ofSurface?_eq_some elseBranch wireElse
                        elseProjection]

  theorem listToSurface_eq_of_listOfSurface?_eq_some :
      (surfaceExpressions : List Solcore.Surface.Expr) ->
      (expressions : List Expr) ->
      surfaceExpressions.mapM ofSurface? = some expressions ->
        expressions.map toSurface = surfaceExpressions
    | [], expressions, projection => by
        simp at projection
        subst expressions
        rfl
    | surfaceExpression :: surfaceRest, expressions, projection => by
        cases expressionProjection : ofSurface? surfaceExpression with
        | none =>
            simp [expressionProjection] at projection
        | some expression =>
            cases restProjection : surfaceRest.mapM ofSurface? with
            | none =>
                simp [expressionProjection, restProjection] at projection
            | some rest =>
                simp [expressionProjection, restProjection] at projection
                subst expressions
                simp [
                  toSurface_eq_of_ofSurface?_eq_some surfaceExpression
                    expression expressionProjection,
                  listToSurface_eq_of_listOfSurface?_eq_some surfaceRest rest
                    restProjection]

end

end Expr

structure LetStatement where
  span : SourceSpan
  name : Name
  type : TypeSyntax
  value : Expr
  deriving Repr, BEq

namespace LetStatement

def toSurface (statement : LetStatement) : Solcore.Surface.LetStatement := {
  span := statement.span.toSurface
  name := statement.name.toSurface
  type := statement.type.toSurface
  value := statement.value.toSurface
}

def ofSurface? : Solcore.Surface.LetStatement -> Option LetStatement
  | ⟨span, name, type, value⟩ => do
      let name <- Name.ofSurface? name
      let type <- TypeSyntax.ofSurface? type
      let value <- Expr.ofSurface? value
      some {
        span := SourceSpan.ofSurface span
        name
        type
        value
      }

@[simp] theorem ofSurface?_toSurface (statement : LetStatement) :
    ofSurface? statement.toSurface = some statement := by
  cases statement
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceStatement : Solcore.Surface.LetStatement}
    {statement : LetStatement}
    (projection : ofSurface? surfaceStatement = some statement) :
    statement.toSurface = surfaceStatement := by
  cases surfaceStatement with
  | mk span surfaceName surfaceType surfaceValue =>
      cases nameProjection : Name.ofSurface? surfaceName with
      | none =>
          simp [ofSurface?, nameProjection] at projection
      | some name =>
          cases typeProjection : TypeSyntax.ofSurface? surfaceType with
          | none =>
              simp [ofSurface?, nameProjection, typeProjection] at projection
          | some type =>
              cases valueProjection : Expr.ofSurface? surfaceValue with
              | none =>
                  simp [ofSurface?, nameProjection, typeProjection,
                    valueProjection] at projection
              | some value =>
                  simp [ofSurface?, nameProjection, typeProjection,
                    valueProjection] at projection
                  subst statement
                  simp [toSurface,
                    Name.toSurface_eq_of_ofSurface?_eq_some nameProjection,
                    TypeSyntax.toSurface_eq_of_ofSurface?_eq_some
                      typeProjection,
                    Expr.toSurface_eq_of_ofSurface?_eq_some surfaceValue value
                      valueProjection]

@[simp] theorem listOfSurface?_toSurface (statements : List LetStatement) :
    statements.mapM (ofSurface? ∘ toSurface) = some statements := by
  induction statements with
  | nil => rfl
  | cons statement rest inductionHypothesis =>
      simp [inductionHypothesis]

theorem listToSurface_eq_of_listOfSurface?_eq_some :
    (surfaceStatements : List Solcore.Surface.LetStatement) ->
    (statements : List LetStatement) ->
    surfaceStatements.mapM ofSurface? = some statements ->
      statements.map toSurface = surfaceStatements
  | [], statements, projection => by
      simp at projection
      subst statements
      rfl
  | surfaceStatement :: surfaceRest, statements, projection => by
      cases statementProjection : ofSurface? surfaceStatement with
      | none =>
          simp [statementProjection] at projection
      | some statement =>
          cases restProjection : surfaceRest.mapM ofSurface? with
          | none =>
              simp [statementProjection, restProjection] at projection
          | some rest =>
              simp [statementProjection, restProjection] at projection
              subst statements
              simp [
                toSurface_eq_of_ofSurface?_eq_some statementProjection,
                listToSurface_eq_of_listOfSurface?_eq_some surfaceRest rest
                  restProjection]

end LetStatement

structure ReturnStatement where
  span : SourceSpan
  value : Expr
  deriving Repr, BEq

namespace ReturnStatement

def toSurface (statement : ReturnStatement) : Solcore.Surface.ReturnStatement := {
  span := statement.span.toSurface
  value := statement.value.toSurface
}

def ofSurface? : Solcore.Surface.ReturnStatement -> Option ReturnStatement
  | ⟨span, value⟩ => do
      let value <- Expr.ofSurface? value
      some {
        span := SourceSpan.ofSurface span
        value
      }

@[simp] theorem ofSurface?_toSurface (statement : ReturnStatement) :
    ofSurface? statement.toSurface = some statement := by
  cases statement
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceStatement : Solcore.Surface.ReturnStatement}
    {statement : ReturnStatement}
    (projection : ofSurface? surfaceStatement = some statement) :
    statement.toSurface = surfaceStatement := by
  cases surfaceStatement with
  | mk span surfaceValue =>
      cases valueProjection : Expr.ofSurface? surfaceValue with
      | none =>
          simp [ofSurface?, valueProjection] at projection
      | some value =>
          simp [ofSurface?, valueProjection] at projection
          subst statement
          simp [toSurface,
            Expr.toSurface_eq_of_ofSurface?_eq_some surfaceValue value
              valueProjection]

end ReturnStatement

structure FunctionDecl where
  span : SourceSpan
  name : Name
  returnType : TypeSyntax
  bindings : List LetStatement
  result : ReturnStatement
  deriving Repr, BEq

namespace FunctionDecl

def toSurface (declaration : FunctionDecl) : Solcore.Surface.FunctionDecl := {
  span := declaration.span.toSurface
  name := declaration.name.toSurface
  returnType := declaration.returnType.toSurface
  bindings := declaration.bindings.map LetStatement.toSurface
  result := declaration.result.toSurface
}

def ofSurface? : Solcore.Surface.FunctionDecl -> Option FunctionDecl
  | ⟨span, name, returnType, bindings, result⟩ => do
      let name <- Name.ofSurface? name
      let returnType <- TypeSyntax.ofSurface? returnType
      let bindings <- bindings.mapM LetStatement.ofSurface?
      let result <- ReturnStatement.ofSurface? result
      some {
        span := SourceSpan.ofSurface span
        name
        returnType
        bindings
        result
      }

@[simp] theorem ofSurface?_toSurface (declaration : FunctionDecl) :
    ofSurface? declaration.toSurface = some declaration := by
  cases declaration
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceDeclaration : Solcore.Surface.FunctionDecl}
    {declaration : FunctionDecl}
    (projection : ofSurface? surfaceDeclaration = some declaration) :
    declaration.toSurface = surfaceDeclaration := by
  cases surfaceDeclaration with
  | mk span surfaceName surfaceReturnType surfaceBindings surfaceResult =>
      cases nameProjection : Name.ofSurface? surfaceName with
      | none =>
          simp [ofSurface?, nameProjection] at projection
      | some name =>
          cases returnTypeProjection :
              TypeSyntax.ofSurface? surfaceReturnType with
          | none =>
              simp [ofSurface?, nameProjection, returnTypeProjection]
                at projection
          | some returnType =>
              cases bindingsProjection :
                  surfaceBindings.mapM LetStatement.ofSurface? with
              | none =>
                  simp [ofSurface?, nameProjection, returnTypeProjection,
                    bindingsProjection] at projection
              | some bindings =>
                  cases resultProjection :
                      ReturnStatement.ofSurface? surfaceResult with
                  | none =>
                      simp [ofSurface?, nameProjection, returnTypeProjection,
                        bindingsProjection, resultProjection] at projection
                  | some result =>
                      simp [ofSurface?, nameProjection, returnTypeProjection,
                        bindingsProjection, resultProjection] at projection
                      subst declaration
                      simp [toSurface,
                        Name.toSurface_eq_of_ofSurface?_eq_some nameProjection,
                        TypeSyntax.toSurface_eq_of_ofSurface?_eq_some
                          returnTypeProjection,
                        LetStatement.listToSurface_eq_of_listOfSurface?_eq_some
                          surfaceBindings bindings bindingsProjection,
                        ReturnStatement.toSurface_eq_of_ofSurface?_eq_some
                          resultProjection]

end FunctionDecl

inductive CommentKind where
  | line
  | block
  deriving Repr, BEq, DecidableEq

namespace CommentKind

def toSurface : CommentKind -> Solcore.Surface.CommentKind
  | .line => .line
  | .block => .block

set_option match.ignoreUnusedAlts true in
def ofSurface? : Solcore.Surface.CommentKind -> Option CommentKind
  | .line => some .line
  | .block => some .block
  | _ => none

@[simp] theorem ofSurface?_toSurface (kind : CommentKind) :
    ofSurface? kind.toSurface = some kind := by
  cases kind <;> rfl

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceKind : Solcore.Surface.CommentKind}
    {kind : CommentKind}
    (projection : ofSurface? surfaceKind = some kind) :
    kind.toSurface = surfaceKind := by
  cases surfaceKind <;> cases kind <;>
    simp [toSurface, ofSurface?] at projection ⊢

end CommentKind

structure Comment where
  kind : CommentKind
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

namespace Comment

def toSurface (comment : Comment) : Solcore.Surface.Comment := {
  kind := comment.kind.toSurface
  span := comment.span.toSurface
}

def ofSurface? : Solcore.Surface.Comment -> Option Comment
  | ⟨kind, span⟩ => do
      let kind <- CommentKind.ofSurface? kind
      some {
        kind
        span := SourceSpan.ofSurface span
      }

@[simp] theorem ofSurface?_toSurface (comment : Comment) :
    ofSurface? comment.toSurface = some comment := by
  cases comment
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceComment : Solcore.Surface.Comment}
    {comment : Comment}
    (projection : ofSurface? surfaceComment = some comment) :
    comment.toSurface = surfaceComment := by
  cases surfaceComment with
  | mk surfaceKind span =>
      cases kindProjection : CommentKind.ofSurface? surfaceKind with
      | none =>
          simp [ofSurface?, kindProjection] at projection
      | some kind =>
          simp [ofSurface?, kindProjection] at projection
          subst comment
          simp [toSurface,
            CommentKind.toSurface_eq_of_ofSurface?_eq_some kindProjection]

@[simp] theorem listOfSurface?_toSurface (comments : List Comment) :
    comments.mapM (ofSurface? ∘ toSurface) = some comments := by
  induction comments with
  | nil => rfl
  | cons comment rest inductionHypothesis =>
      simp [inductionHypothesis]

theorem listToSurface_eq_of_listOfSurface?_eq_some :
    (surfaceComments : List Solcore.Surface.Comment) ->
    (comments : List Comment) ->
    surfaceComments.mapM ofSurface? = some comments ->
      comments.map toSurface = surfaceComments
  | [], comments, projection => by
      simp at projection
      subst comments
      rfl
  | surfaceComment :: surfaceRest, comments, projection => by
      cases commentProjection : ofSurface? surfaceComment with
      | none =>
          simp [commentProjection] at projection
      | some comment =>
          cases restProjection : surfaceRest.mapM ofSurface? with
          | none =>
              simp [commentProjection, restProjection] at projection
          | some rest =>
              simp [commentProjection, restProjection] at projection
              subst comments
              simp [
                toSurface_eq_of_ofSurface?_eq_some commentProjection,
                listToSurface_eq_of_listOfSurface?_eq_some surfaceRest rest
                  restProjection]

end Comment

structure File where
  span : SourceSpan
  function : FunctionDecl
  comments : List Comment
  deriving Repr, BEq

namespace File

def toSurface (file : File) : Solcore.Surface.ParsedFile := {
  span := file.span.toSurface
  function := file.function.toSurface
  comments := file.comments.map Comment.toSurface
}

def ofSurface? : Solcore.Surface.ParsedFile -> Option File
  | ⟨span, function, comments⟩ => do
      let function <- FunctionDecl.ofSurface? function
      let comments <- comments.mapM Comment.ofSurface?
      some {
        span := SourceSpan.ofSurface span
        function
        comments
      }

@[simp] theorem ofSurface?_toSurface (file : File) :
    ofSurface? file.toSurface = some file := by
  cases file
  simp [toSurface, ofSurface?]

theorem toSurface_eq_of_ofSurface?_eq_some
    {surfaceFile : Solcore.Surface.ParsedFile}
    {file : File}
    (projection : ofSurface? surfaceFile = some file) :
    file.toSurface = surfaceFile := by
  cases surfaceFile with
  | mk span surfaceFunction surfaceComments =>
      cases functionProjection :
          FunctionDecl.ofSurface? surfaceFunction with
      | none =>
          simp [ofSurface?, functionProjection] at projection
      | some function =>
          cases commentsProjection :
              surfaceComments.mapM Comment.ofSurface? with
          | none =>
              simp [ofSurface?, functionProjection, commentsProjection]
                at projection
          | some comments =>
              simp [ofSurface?, functionProjection, commentsProjection]
                at projection
              subst file
              simp [toSurface,
                FunctionDecl.toSurface_eq_of_ofSurface?_eq_some
                  functionProjection,
                Comment.listToSurface_eq_of_listOfSurface?_eq_some
                  surfaceComments comments commentsProjection]

end File

end Solcore.Surface.Wire.V1
