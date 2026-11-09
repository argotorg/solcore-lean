import Solcore.SourceSemantics.Requirements
import Solcore.Frontend.WordLiteral
import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Types

/-!
# Literals, operators, calls, patterns and places

The construct-level rules that `Static` assembles. Main declarations: `IntegerLiteralValid`,
`WordLiteralValid`, `UnaryOperatorHasType`, `BinaryOperatorHasType`, `DeclarationApplicationValid`,
`IndirectApplicationValid`, `TypedMatchPatternHasType`, `PlaceHasType`, `AssignmentHasType`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Calls
/-!
Declarative profiles for resolved source calls.

These relations validate the call metadata retained by the occurrence graph.
They do not enumerate overload candidates, rank conversions, or run the source
checker.  Argument-expression typing is supplied by the main static-semantics
judgment.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A direct call instantiation exposes the exact catalog parameter list,
bundled result type, and instantiated declaration predicates. -/
inductive DeclarationApplicationValid (context : Context)
    (instantiation : DeclarationInstantiation) :
    List TypeSystem.Ty → TypeSystem.Ty → List ProgramPredicate → Prop where
  | intro
      {signature : ProgramFunctionSignature}
      {parameterTypes : List TypeSystem.Ty}
      {resultType : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      (signature_mem : signature ∈ context.signatures.functions)
      (valid : SourceSemantics.DeclarationInstantiation.Admissible
        context instantiation)
      (declaration_eq : instantiation.declaration = signature.id)
      (parameter_types_eq :
        signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            instantiation.parameterSubstitution) = parameterTypes)
      (result_type_eq :
        TypeSystem.ParameterSubstitution.apply
          instantiation.parameterSubstitution
          (TypeSystem.Ty.productMany signature.returnTypes) = resultType)
      (function_type_eq : instantiation.type =
        .function (TypeSystem.Ty.productMany parameterTypes) resultType)
      (predicates_eq : instantiation.predicates = predicates) :
      DeclarationApplicationValid context instantiation parameterTypes
        resultType predicates

/-- The synthetic callee inserted for a selected direct declaration call.
Its declaration predicates are owned by the call occurrence, so this reference
has neither requirements nor output coercions. -/
inductive DirectDeclarationCalleeValid
    (context : Context) (source : TypedSource) :
    ExpressionId → DeclarationInstantiation → Prop where
  | intro
      {id : ExpressionId}
      {node : ExpressionNode}
      {name : String}
      {instantiation : DeclarationInstantiation}
      (contains : ContainsExpression source id node)
      (form_eq : node.form = .reference name (.declaration instantiation))
      (instantiation_valid :
        SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
      (type_eq : node.type = instantiation.type)
      (requirements_eq : node.requirements = [])
      (coercions_eq : node.coercions = []) :
      DirectDeclarationCalleeValid context source id instantiation

/-- The synthetic callee inserted for a compiler-provided builtin call. -/
inductive DirectBuiltinCalleeValid (source : TypedSource) :
    ExpressionId → BuiltinFunctionId → Prop where
  | intro
      {id : ExpressionId}
      {node : ExpressionNode}
      {name : String}
      {function : BuiltinFunctionId}
      (contains : ContainsExpression source id node)
      (form_eq : node.form = .reference name (.builtinFunction function))
      (type_eq : node.type = function.type)
      (requirements_eq : node.requirements = [])
      (coercions_eq : node.coercions = []) :
      DirectBuiltinCalleeValid source id function

/-- Current direct-call metadata stores the selected-result coercions and any
later contextual coercions as one path.  This relation records the semantic
split and the exact interleaving of their evidence with signature evidence. -/
inductive DirectCallRequirementsValid (context : Context)
    (rawResult finalResult : TypeSystem.Ty)
    (predicates : List ProgramPredicate) :
    List RequirementId → List CoercionStep → Prop where
  | intro
      {selectedResult : TypeSystem.Ty}
      {selectedPath contextualPath : List CoercionStep}
      {signatureRequirements : List RequirementId}
      {requirements : List RequirementId}
      {coercions : List CoercionStep}
      (selected_valid : CoercionPathValid context rawResult selectedResult
        selectedPath)
      (contextual_valid : CoercionPathValid context selectedResult finalResult
        contextualPath)
      (signature_valid : RequirementSequenceProves context
        signatureRequirements predicates)
      (coercions_eq : coercions = selectedPath ++ contextualPath)
      (requirements_eq : requirements =
        coercionRequirementIds selectedPath ++
          (signatureRequirements ++ coercionRequirementIds contextualPath)) :
      DirectCallRequirementsValid context rawResult finalResult predicates
        requirements coercions

/-- Exact indirect-call metadata before the ordinary output coercion path. -/
inductive IndirectApplicationValid (context : Context)
    (metadata : IndirectCallResolution) (argumentTypes : List TypeSystem.Ty)
    (parameterType : TypeSystem.Ty) : Prop where
  | intro
      (count_eq : metadata.argumentCount = argumentTypes.length)
      (before_eq : metadata.argumentTypeBeforeCoercion =
        TypeSystem.Ty.productMany argumentTypes)
      (after_eq : metadata.argumentTypeAfterCoercion = parameterType)
      (path_valid : CoercionPathValid context
        metadata.argumentTypeBeforeCoercion parameterType
        metadata.argumentCoercions) :
      IndirectApplicationValid context metadata argumentTypes parameterType

namespace DirectCallRequirementsValid

theorem requirements_valid
    {context : Context} {rawResult finalResult : TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (valid : DirectCallRequirementsValid context rawResult finalResult
      predicates requirements coercions) :
    RequirementIdsValid context requirements := by
  cases valid with
  | @intro selectedResult selectedPath contextualPath
      signatureRequirements requirements coercions selectedValid contextualValid
      signatureValid coercionsEq requirementsEq =>
      subst requirements
      intro id member
      change id ∈ coercionRequirementIds selectedPath ++
        (signatureRequirements ++ coercionRequirementIds contextualPath) at member
      rw [List.mem_append] at member
      rcases member with selectedMember | signatureOrContext
      · exact selectedValid.requirements_valid id selectedMember
      · rw [List.mem_append] at signatureOrContext
        rcases signatureOrContext with signatureMember | contextMember
        · exact signatureValid.ids_valid id signatureMember
        · exact contextualValid.requirements_valid id contextMember

end DirectCallRequirementsValid

end Solcore.SourceSemantics
end

section
-- leanmerge: from Solcore.SourceSemantics.Literals
/-!
Declarative numeric-literal meaning for resolved source occurrences.

Literal spelling is related to its mathematical natural-number value by the
existing proof-facing digit relation.  Selected integer targets are restricted
to the two source domains implemented by the language semantics, and their
stable evidence identity must prove the exact builtin `Int` predicate.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A retained integer-literal resolution denotes its stored mathematical
value and owns exact evidence for a supported target type. -/
inductive IntegerLiteralValid (context : Context) :
    Syntax.CoreLiteralValue → IntegerLiteralResolution → Prop where
  | word
      {source : Syntax.CoreLiteralValue}
      {resolution : IntegerLiteralResolution}
      (meaning : NumericLiteralDenotes source resolution.rawValue)
      (target_eq : resolution.targetType = .word)
      (evidence : RequirementProves context resolution.requirement
        (ProgramSignatures.builtinIntPredicate resolution.targetType)) :
      IntegerLiteralValid context source resolution
  | integer
      {source : Syntax.CoreLiteralValue}
      {resolution : IntegerLiteralResolution}
      (meaning : NumericLiteralDenotes source resolution.rawValue)
      (target_eq : resolution.targetType = .integer)
      (evidence : RequirementProves context resolution.requirement
        (ProgramSignatures.builtinIntPredicate resolution.targetType)) :
      IntegerLiteralValid context source resolution

namespace IntegerLiteralValid

theorem requirement_valid
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (valid : IntegerLiteralValid context source resolution) :
    RequirementValid context resolution.requirement := by
  cases valid with
  | word _ _ evidence | integer _ _ evidence => exact ⟨_, evidence⟩

theorem target_supported
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (valid : IntegerLiteralValid context source resolution) :
    resolution.targetType = .word ∨ resolution.targetType = .integer := by
  cases valid with
  | word _ target_eq _ => exact .inl target_eq
  | integer _ target_eq _ => exact .inr target_eq

/-- Every declaratively valid integer-literal resolution selects an
admissible primitive target type. -/
theorem target_type_admissible
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (binders : TypeParameterBindersWellFormed context)
    (valid : IntegerLiteralValid context source resolution) :
    TypeAdmissible context resolution.targetType := by
  cases valid with
  | word _ targetEq _ =>
      rw [targetEq]
      exact TypeAdmissible.word binders
  | integer _ targetEq _ =>
      rw [targetEq]
      exact TypeAdmissible.integer binders

/-- Literal validity is stable under lexical-context growth when the target
retains the same signature catalog and solved requirement ledger. -/
theorem transportContext
    {sourceContext targetContext : Context}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (signatures_eq : targetContext.signatures = sourceContext.signatures)
    (solved_eq : targetContext.solvedRequirements =
      sourceContext.solvedRequirements)
    (assumptions_mono : sourceContext.assumptions ⊆
      targetContext.assumptions)
    (valid : IntegerLiteralValid sourceContext source resolution) :
    IntegerLiteralValid targetContext source resolution := by
  cases valid with
  | word meaning target_eq evidence =>
      exact .word meaning target_eq
        (evidence.transportContext signatures_eq solved_eq assumptions_mono)
  | integer meaning target_eq evidence =>
      exact .integer meaning target_eq
        (evidence.transportContext signatures_eq solved_eq assumptions_mono)

end IntegerLiteralValid

/-- Compatibility literal nodes are the strict primitive-Word form. -/
inductive WordLiteralValid : Syntax.CoreLiteralValue → Prop where
  | intro {source : Syntax.CoreLiteralValue} {value : Nat}
      (meaning : NumericLiteralDenotes source value) :
      WordLiteralValid source

end Solcore.SourceSemantics
end

section
-- leanmerge: from Solcore.SourceSemantics.Operators
/-!
Declarative source-operator typing.

Primitive operators are listed directly.  User-defined operator behavior is
validated against the resolved trait catalog and the exact retained evidence;
no overload selector or trait-search procedure is invoked here.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- Arithmetic and bitwise binary spellings whose primitive result has the
same type as both operands. -/
inductive ArithmeticBinaryOperator : Syntax.BinaryOp → Prop where
  | multiply : ArithmeticBinaryOperator .multiply
  | divide : ArithmeticBinaryOperator .divide
  | modulo : ArithmeticBinaryOperator .modulo
  | add : ArithmeticBinaryOperator .add
  | subtract : ArithmeticBinaryOperator .subtract
  | bitAnd : ArithmeticBinaryOperator .bitAnd
  | bitXor : ArithmeticBinaryOperator .bitXor
  | bitOr : ArithmeticBinaryOperator .bitOr

/-- Shift spellings: the result has the value's type, and the amount is typed
independently of the value. -/
inductive ShiftBinaryOperator : Syntax.BinaryOp → Prop where
  | shiftLeft : ShiftBinaryOperator .shiftLeft
  | shiftRight : ShiftBinaryOperator .shiftRight

/-- The arithmetic of an `unchecked` block. On `word`, `+`, `-` and `*` wrap
like the checked operators, and `/` and `%` panic with `0x12` on a zero
divisor. -/
inductive UncheckedBinaryOperator : Syntax.BinaryOp → Prop where
  | uncheckedAdd : UncheckedBinaryOperator .uncheckedAdd
  | uncheckedSubtract : UncheckedBinaryOperator .uncheckedSubtract
  | uncheckedMultiply : UncheckedBinaryOperator .uncheckedMultiply
  | uncheckedDivide : UncheckedBinaryOperator .uncheckedDivide
  | uncheckedModulo : UncheckedBinaryOperator .uncheckedModulo

/-- Comparison spellings whose primitive result is Boolean. -/
inductive ComparisonBinaryOperator : Syntax.BinaryOp → Prop where
  | less : ComparisonBinaryOperator .less
  | greater : ComparisonBinaryOperator .greater
  | lessEqual : ComparisonBinaryOperator .lessEqual
  | greaterEqual : ComparisonBinaryOperator .greaterEqual
  | equal : ComparisonBinaryOperator .equal
  | notEqual : ComparisonBinaryOperator .notEqual

/-- The comparisons whose meaning on a fixed-width integer type is Word's on its
canonical words: `==` and `!=` on every type, and the orderings on the unsigned
types. -/
inductive FixedWordComparison (type : TypeSystem.FixedInteger) : Syntax.BinaryOp → Prop where
  | equal : FixedWordComparison type .equal
  | notEqual : FixedWordComparison type .notEqual
  | less (unsigned : type.signed = false) : FixedWordComparison type .less
  | greater (unsigned : type.signed = false) : FixedWordComparison type .greater
  | lessEqual (unsigned : type.signed = false) : FixedWordComparison type .lessEqual
  | greaterEqual (unsigned : type.signed = false) : FixedWordComparison type .greaterEqual

/-- The bitwise operators whose meaning on an unsigned fixed-width integer type
is Word's: canonical words stay canonical. -/
inductive FixedWordBitwise (type : TypeSystem.FixedInteger) : Syntax.BinaryOp → Prop where
  | bitAnd (unsigned : type.signed = false) : FixedWordBitwise type .bitAnd
  | bitXor (unsigned : type.signed = false) : FixedWordBitwise type .bitXor
  | bitOr (unsigned : type.signed = false) : FixedWordBitwise type .bitOr

/-- The source spelling-to-trait-method assignment for operator forms which
remain operator nodes after resolution. -/
inductive BinaryTraitDispatch : Syntax.BinaryOp → String → String → Prop where
  | multiply : BinaryTraitDispatch .multiply "Mul" "mul"
  | divide : BinaryTraitDispatch .divide "Div" "div"
  | modulo : BinaryTraitDispatch .modulo "Mod" "mod"
  | add : BinaryTraitDispatch .add "Add" "add"
  | subtract : BinaryTraitDispatch .subtract "Sub" "sub"
  | bitAnd : BinaryTraitDispatch .bitAnd "BitAnd" "band"
  | bitXor : BinaryTraitDispatch .bitXor "BitXor" "bxor"
  | bitOr : BinaryTraitDispatch .bitOr "BitOr" "bor"
  | greater : BinaryTraitDispatch .greater "Ord" "gt"
  | equal : BinaryTraitDispatch .equal "Eq" "eq"
  | uncheckedAdd : BinaryTraitDispatch .uncheckedAdd "UncheckedAdd" "add"
  | uncheckedSubtract : BinaryTraitDispatch .uncheckedSubtract "UncheckedSub" "sub"
  | uncheckedMultiply : BinaryTraitDispatch .uncheckedMultiply "UncheckedMul" "mul"
  | uncheckedDivide : BinaryTraitDispatch .uncheckedDivide "UncheckedDiv" "div"
  | uncheckedModulo : BinaryTraitDispatch .uncheckedModulo "UncheckedMod" "mod"

/-- Unary operator forms with trait dispatch. -/
inductive UnaryTraitDispatch : Syntax.UnaryOp → String → String → Prop where
  | bitNot : UnaryTraitDispatch .bitNot "BitNot" "bnot"

/-- A uniquely named operator method has the required instantiated signature
and produces the declaration-ordered primary and method predicates. -/
inductive OperatorProfileInstantiates
    (context : Context) (traitName methodName : String)
    (operand : TypeSystem.Ty) (parameterTypes returnTypes : List TypeSystem.Ty) :
    List ProgramPredicate → Prop where
  | intro
      {signature : ProgramTraitSignature}
      {method : ProgramTraitMethodSignature}
      {parameter : TypeSystem.TypeParameterId}
      (signature_mem : signature ∈ context.signatures.traits)
      (trait_name_eq : signature.name = traitName)
      (parameters_eq : signature.parameters = [parameter])
      (method_unique :
        signature.methods.filter (fun candidate => candidate.name == methodName) =
          [method])
      (parameter_types_eq :
        method.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply [(parameter, operand)]) =
            parameterTypes)
      (return_types_eq :
        method.returnTypes.map
          (TypeSystem.ParameterSubstitution.apply [(parameter, operand)]) =
            returnTypes) :
      OperatorProfileInstantiates context traitName methodName operand
        parameterTypes returnTypes
        ({ trait := .declaration signature.id, subject := operand, arguments := [] } ::
          method.wherePredicates.map
            (ProgramPredicate.applyParameters [(parameter, operand)]))

/-- Complete unary source-operator typing, including exact evidence IDs. -/
inductive UnaryOperatorHasType (context : Context) :
    Syntax.UnaryOp → TypeSystem.Ty → TypeSystem.Ty →
      List RequirementId → Prop where
  | logicalNot : UnaryOperatorHasType context .logicalNot .bool .bool []
  | wordBitNot : UnaryOperatorHasType context .bitNot .word .word []
  | integerBitNot : UnaryOperatorHasType context .bitNot .integer .integer []
  | trait
      {operator : Syntax.UnaryOp}
      {traitName methodName : String}
      {operand result : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      {requirements : List RequirementId}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (profile : OperatorProfileInstantiates context traitName methodName
        operand [operand] [result] predicates)
      (evidence : RequirementSequenceProves context requirements predicates) :
      UnaryOperatorHasType context operator operand result requirements

/-- Complete binary source-operator typing, including exact evidence IDs. -/
inductive BinaryOperatorHasType (context : Context) :
    Syntax.BinaryOp → TypeSystem.Ty → TypeSystem.Ty → TypeSystem.Ty →
      List RequirementId → Prop where
  | wordArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .word []
  | integerArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      BinaryOperatorHasType context operator .integer .integer .integer []
  | wordShift {operator : Syntax.BinaryOp}
      (kind : ShiftBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .word []
  | wordUnchecked {operator : Syntax.BinaryOp}
      (kind : UncheckedBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .word []
  | wordComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .bool []
  | integerComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      BinaryOperatorHasType context operator .integer .integer .bool []
  | fixedComparison {operator : Syntax.BinaryOp} {type : TypeSystem.FixedInteger}
      (kind : FixedWordComparison type operator) :
      BinaryOperatorHasType context operator (.fixed type) (.fixed type) .bool []
  | fixedBitwise {operator : Syntax.BinaryOp} {type : TypeSystem.FixedInteger}
      (kind : FixedWordBitwise type operator) :
      BinaryOperatorHasType context operator (.fixed type) (.fixed type) (.fixed type) []
  | booleanAnd :
      BinaryOperatorHasType context .logicalAnd .bool .bool .bool []
  | booleanOr :
      BinaryOperatorHasType context .logicalOr .bool .bool .bool []
  | trait
      {operator : Syntax.BinaryOp}
      {traitName methodName : String}
      {operand result : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      {requirements : List RequirementId}
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (profile : OperatorProfileInstantiates context traitName methodName
        operand [operand, operand] [result] predicates)
      (evidence : RequirementSequenceProves context requirements predicates) :
      BinaryOperatorHasType context operator operand operand result requirements

namespace UnaryOperatorHasType

theorem requirements_valid
    {context : Context} {operator : Syntax.UnaryOp}
    {operand result : TypeSystem.Ty} {requirements : List RequirementId}
    (typing : UnaryOperatorHasType context operator operand result requirements) :
    RequirementIdsValid context requirements := by
  cases typing with
  | logicalNot | wordBitNot | integerBitNot => simp [RequirementIdsValid]
  | trait _ _ evidence => exact evidence.ids_valid

end UnaryOperatorHasType

namespace BinaryOperatorHasType

theorem requirements_valid
    {context : Context} {operator : Syntax.BinaryOp}
    {left right result : TypeSystem.Ty} {requirements : List RequirementId}
    (typing : BinaryOperatorHasType context operator left right result requirements) :
    RequirementIdsValid context requirements := by
  cases typing with
  | wordArithmetic | integerArithmetic | wordShift | wordUnchecked | wordComparison |
      integerComparison | fixedComparison | fixedBitwise | booleanAnd | booleanOr =>
      simp [RequirementIdsValid]
  | trait _ _ evidence => exact evidence.ids_valid

end BinaryOperatorHasType

end Solcore.SourceSemantics
end

section
-- leanmerge: from Solcore.SourceSemantics.Patterns
/-!
Declarative typing for the flattened source-pattern carrier.

`MatchPatternInstruction` is a prefix program: constructor and tuple
instructions are followed by exactly the number of self-delimiting children
recorded at their root.  The mutually inductive judgments below consume that
program directly.  Consequently neither pattern inference nor the executable
pattern consumers occur in the specification.

The source carrier deliberately preserves groups and the outer spelling of a
constructor, but it does not retain the nested source terms below constructor
or tuple roots.  Therefore `MatchPatternSourceRepresents` can validate the
root spelling and arity while the instruction judgments validate the complete
nested semantic tree.  A future lossless nested source carrier can strengthen
that correspondence without changing prefix typing.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A pattern binder is monomorphic at the matched value type, is a runtime
binder, and belongs to the declaration currently being checked when such a
declaration has been installed in the context. -/
structure PatternBinderValid (context : Context) (type : TypeSystem.Ty)
    (binder : TypedBinder) : Prop where
  scheme_eq : binder.scheme = .mono type
  runtime : binder.comptime = false
  wellFormed : ∀ declaration,
    context.currentDeclaration = some declaration →
      BinderWellFormed context declaration binder

/-- Stable identities and source spellings introduced by one pattern are both
pairwise distinct. -/
structure PatternBindersDistinct (binders : List TypedBinder) : Prop where
  ids : (binders.map (fun binder => binder.id)).Nodup
  names : (binders.map (fun binder => binder.name)).Nodup

mutual

  /-- Consume one well-typed self-delimiting pattern instruction and return
  its exact requirement IDs, binders, and unconsumed suffix. -/
  inductive PatternInstructionHasType (context : Context) :
      List MatchPatternInstruction → TypeSystem.Ty →
        List RequirementId → List TypedBinder →
          List MatchPatternInstruction → Prop where
    | wildcard {rest type} :
        PatternInstructionHasType context (.wildcard :: rest) type [] [] rest
    | integerLiteral
        {rest source resolution}
        (valid : IntegerLiteralValid context source resolution) :
        PatternInstructionHasType context
          (.integerLiteral source resolution :: rest)
          resolution.targetType [resolution.requirement] [] rest
    | binder
        {rest binder type}
        (valid : PatternBinderValid context type binder) :
        PatternInstructionHasType context (.binder binder :: rest)
          type [] [binder] rest
    | constructor
        {instructions rest instantiation argumentCount requirements binders}
        (valid : DataConstructorInstantiation.Admissible context instantiation)
        (arity : argumentCount = instantiation.payloadTypes.length)
        (arguments : PatternInstructionsHaveTypes context instructions
          instantiation.payloadTypes requirements binders rest) :
        PatternInstructionHasType context
          (.constructor instantiation argumentCount :: instructions)
          instantiation.resultType requirements binders rest
    | tuple
        {instructions rest elementCount elementTypes requirements binders}
        (arity : elementCount = elementTypes.length)
        (elements : PatternInstructionsHaveTypes context instructions
          elementTypes requirements binders rest) :
        PatternInstructionHasType context
          (.tuple elementCount :: instructions)
          (TypeSystem.Ty.productMany elementTypes) requirements binders rest

  /-- Consume a source-ordered sequence of pattern trees at the corresponding
  source types.  Requirements and binders are concatenated in that same order. -/
  inductive PatternInstructionsHaveTypes (context : Context) :
      List MatchPatternInstruction → List TypeSystem.Ty →
        List RequirementId → List TypedBinder →
          List MatchPatternInstruction → Prop where
    | nil {instructions} :
        PatternInstructionsHaveTypes context instructions [] [] [] instructions
    | cons
        {instructions afterHead rest type types
          headRequirements tailRequirements headBinders tailBinders}
        (head : PatternInstructionHasType context instructions type
          headRequirements headBinders afterHead)
        (tail : PatternInstructionsHaveTypes context afterHead types
          tailRequirements tailBinders rest) :
        PatternInstructionsHaveTypes context instructions (type :: types)
          (headRequirements ++ tailRequirements)
          (headBinders ++ tailBinders) rest

end

/-- Reconstitute the complete prefix program represented by a root
resolution. -/
def matchPatternResolutionInstructions :
    MatchPatternResolution → Nat → List MatchPatternInstruction
  | .wildcard, _ => [.wildcard]
  | .integerLiteral source resolution, _ => [.integerLiteral source resolution]
  | .binder binder, _ => [.binder binder]
  | .constructor instantiation arguments, rootArity =>
      .constructor instantiation rootArity :: arguments
  | .tuple elements, rootArity => .tuple rootArity :: elements

/-- The root resolution is a complete, exactly consumed pattern program. -/
def MatchPatternResolutionHasType (context : Context)
    (resolution : MatchPatternResolution) (type : TypeSystem.Ty)
    (requirements : List RequirementId) (binders : List TypedBinder)
    (rootArity : Nat) : Prop :=
  PatternInstructionHasType context
    (matchPatternResolutionInstructions resolution rootArity)
    type requirements binders []

/-- A constructor spelling selects the catalog constructor retained in its
instantiation.  Qualifier/import-path validity is established by the resolved
source layer; the current compact source carrier retains qualifier spellings
but not the resolution trace needed to restate that judgment here. -/
def ConstructorPatternSpellingValid (context : Context) (name : String)
    (instantiation : DataConstructorInstantiation) : Prop :=
  ∃ signature,
    signature ∈ context.signatures.dataTypes ∧
    ∃ constructor,
      constructor ∈ signature.constructors ∧
      constructor.id = instantiation.constructor ∧
      constructor.name = name

/-- Correspondence available from the compact source-pattern carrier to the
semantic root resolution.  Groups intentionally leave the resolution
unchanged. -/
inductive MatchPatternSourceRepresents (context : Context) :
    MatchPatternSource → MatchPatternResolution → Nat → Prop where
  | wildcard {span marker} :
      MatchPatternSourceRepresents context (.wildcard span marker) .wildcard 0
  | integerLiteral {span literal source resolution}
      (source_eq : literal.value = source) :
      MatchPatternSourceRepresents context (.integerLiteral span literal)
        (.integerLiteral source resolution) 0
  | binder {span name binder}
      (name_eq : binder.name = name) :
      MatchPatternSourceRepresents context (.binder span name) (.binder binder) 0
  | constructor
      {span leadingDot qualifiers name argumentCount instantiation arguments}
      (spelling : ConstructorPatternSpellingValid context name instantiation) :
      MatchPatternSourceRepresents context
        (.constructor span leadingDot qualifiers name argumentCount)
        (.constructor instantiation arguments) argumentCount
  | tuple {span elementCount elements} :
      MatchPatternSourceRepresents context (.tuple span elementCount)
        (.tuple elements) elementCount
  | group {span inner resolution rootArity}
      (inner_represents :
        MatchPatternSourceRepresents context inner resolution rootArity) :
      MatchPatternSourceRepresents context (.group span inner) resolution rootArity

/-- Complete source-level pattern typing.  The result exposes binders so a
match-arm judgment can extend its lexical context without inspecting the
carrier. -/
structure TypedMatchPatternHasType (context : Context)
    (pattern : TypedMatchPattern) (type : TypeSystem.Ty)
    (binders : List TypedBinder) (rootArity : Nat) : Prop where
  type_eq : pattern.type = type
  source_represents :
    MatchPatternSourceRepresents context pattern.source pattern.resolution rootArity
  resolution_type : MatchPatternResolutionHasType context pattern.resolution
    type pattern.requirements binders rootArity
  binders_distinct : PatternBindersDistinct binders

/-- A closed validity view when a consumer does not need the binder list. -/
def TypedMatchPatternValid (context : Context)
    (pattern : TypedMatchPattern) : Prop :=
  ∃ binders rootArity,
    TypedMatchPatternHasType context pattern pattern.type binders rootArity

mutual

  /-- Declarative irrefutability for one prefix instruction.  Constructor and
  integer roots have no constructor, matching their refutable semantics. -/
  inductive PatternInstructionIrrefutable :
      List MatchPatternInstruction → List MatchPatternInstruction → Prop where
    | wildcard {rest} : PatternInstructionIrrefutable (.wildcard :: rest) rest
    | binder {rest binder} :
        PatternInstructionIrrefutable (.binder binder :: rest) rest
    | tuple {instructions rest elementCount}
        (elements : PatternInstructionsIrrefutable instructions elementCount rest) :
        PatternInstructionIrrefutable
          (.tuple elementCount :: instructions) rest

  /-- Every pattern in a fixed-length prefix sequence is irrefutable. -/
  inductive PatternInstructionsIrrefutable :
      List MatchPatternInstruction → Nat → List MatchPatternInstruction → Prop where
    | zero {instructions} :
        PatternInstructionsIrrefutable instructions 0 instructions
    | succ {instructions afterHead rest count}
        (head : PatternInstructionIrrefutable instructions afterHead)
        (tail : PatternInstructionsIrrefutable afterHead count rest) :
        PatternInstructionsIrrefutable instructions (count + 1) rest

end

/-- A root pattern resolution is irrefutable exactly when its complete prefix
program has an irrefutability derivation consuming all instructions. -/
def MatchPatternResolutionIrrefutable
    (resolution : MatchPatternResolution) (rootArity : Nat) : Prop :=
  PatternInstructionIrrefutable
    (matchPatternResolutionInstructions resolution rootArity) []

/-- Source-connected irrefutability uses the retained root arity, which is
essential because tuple resolutions store a flat child stream. -/
def TypedMatchPatternIrrefutable (context : Context)
    (pattern : TypedMatchPattern) : Prop :=
  ∃ rootArity,
    MatchPatternSourceRepresents context pattern.source pattern.resolution
      rootArity ∧
    MatchPatternResolutionIrrefutable pattern.resolution rootArity

private theorem requirementIdsValid_append
    {context : Context} {left right : List RequirementId}
    (leftValid : RequirementIdsValid context left)
    (rightValid : RequirementIdsValid context right) :
    RequirementIdsValid context (left ++ right) := by
  intro id member
  simp only [List.mem_append] at member
  exact member.elim (leftValid id) (rightValid id)

namespace PatternInstructionHasType

/-- All requirement identities emitted by one typed pattern instruction are
independently valid. -/
theorem requirements_valid
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionHasType context instructions type requirements
      binders rest) :
    RequirementIdsValid context requirements := by
  refine PatternInstructionHasType.rec
    (motive_1 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    (motive_2 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intros
    simp [RequirementIdsValid]
  · intros
    intro id member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst id
    exact IntegerLiteralValid.requirement_valid (by assumption)
  · intros
    simp [RequirementIdsValid]
  · intros
    assumption
  · intros
    assumption
  · intros
    simp [RequirementIdsValid]
  · intros
    apply requirementIdsValid_append <;> assumption

end PatternInstructionHasType

namespace PatternInstructionsHaveTypes

/-- A typed sequence likewise emits only valid requirement identities. -/
theorem requirements_valid
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {types : List TypeSystem.Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionsHaveTypes context instructions types
      requirements binders rest) :
    RequirementIdsValid context requirements := by
  refine PatternInstructionsHaveTypes.rec
    (motive_1 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    (motive_2 := fun _ _ requirements _ _ _ =>
      RequirementIdsValid context requirements)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intros
    simp [RequirementIdsValid]
  · intros
    intro id member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst id
    exact IntegerLiteralValid.requirement_valid (by assumption)
  · intros
    simp [RequirementIdsValid]
  · intros
    assumption
  · intros
    assumption
  · intros
    simp [RequirementIdsValid]
  · intros
    apply requirementIdsValid_append <;> assumption

end PatternInstructionsHaveTypes

namespace TypedMatchPatternHasType

theorem requirements_valid
    {context : Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {rootArity : Nat}
    (typing :
      TypedMatchPatternHasType context pattern type binders rootArity) :
    RequirementIdsValid context pattern.requirements :=
  typing.resolution_type.requirements_valid

end TypedMatchPatternHasType

end Solcore.SourceSemantics
end

section
-- leanmerge: from Solcore.SourceSemantics.Places
/-!
Declarative typing for mutable source places and assignments.

The judgments are parameterized by expression typing.  Consequently this
module can state the place fragment without depending on the mutually
recursive whole-expression and whole-statement judgments.  Local lookup is
the resolved scope's first-match relation, and writable roots are deliberately
restricted to monomorphic schemes, matching the current executable profile.

Member names in `PlaceProjection.member` are retained for source diagnostics.
The semantic selection is its stable positional index.  Since the present
catalog has positional constructor payloads rather than named fields, the
member rule below conservatively requires that position to have one uniform
type in every constructor of the nominal data declaration.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- A lexical local may root a mutable place exactly when its first-match
scheme is monomorphic. -/
inductive WritableLocal (context : Context) :
    Resolved.LocalId → TypeSystem.Ty → Prop where
  | intro
      {id : Resolved.LocalId}
      {scheme : TypeSystem.Scheme}
      {type : TypeSystem.Ty}
      (lookup : context.LocalLookup id scheme)
      (scheme_well_formed : SchemeWellFormed context scheme)
      (quantified_eq : scheme.quantified = [])
      (body_eq : scheme.body = type) :
      WritableLocal context id type

namespace WritableLocal

/-- Expose the exact first-match scheme selected for a writable local. -/
theorem scheme
    {context : Context} {id : Resolved.LocalId} {type : TypeSystem.Ty}
    (writable : WritableLocal context id type) :
    ∃ scheme, context.LocalLookup id scheme ∧
      SchemeWellFormed context scheme ∧
      scheme.quantified = [] ∧ scheme.body = type := by
  cases writable with
  | intro lookup scheme_well_formed quantified_eq body_eq =>
      exact ⟨_, lookup, scheme_well_formed, quantified_eq, body_eq⟩

/-- A directly bound monomorphic local whose type is meaningful in the
admissible flexible scope is writable. -/
theorem withLocal_mono_admissible (context : Context) (id : Resolved.LocalId)
    (type : TypeSystem.Ty)
    (admissible : TypeAdmissible (context.withLocal id (.mono type)) type) :
    WritableLocal (context.withLocal id (.mono type)) id type := by
  exact .intro (.head) (SchemeWellFormed.monoAdmissible admissible) rfl rfl

/-- Closed monomorphic locals are a special case of flexible admissibility. -/
theorem withLocal_mono (context : Context) (id : Resolved.LocalId)
    (type : TypeSystem.Ty)
    (well_formed : TypeWellFormed (context.withLocal id (.mono type)) type) :
    WritableLocal (context.withLocal id (.mono type)) id type := by
  exact withLocal_mono_admissible context id type
    (TypeAdmissible.ofWellFormed well_formed)

/-- A writable root's monomorphic body is meaningful in the current admissible
flexible scope. -/
theorem type_admissible
    {context : Context} {id : Resolved.LocalId} {type : TypeSystem.Ty}
    (writable : WritableLocal context id type) :
    TypeAdmissible context type := by
  cases writable with
  | intro _ scheme_well_formed quantified_eq body_eq =>
      exact {
        binders := scheme_well_formed.binders
        typeWellScoped := by
          rw [← body_eq]
          simpa [quantified_eq] using scheme_well_formed.body
      }

end WritableLocal

/-- Positional member selection is catalog-backed and uniform across every
constructor.  Requiring a nonempty constructor list prevents the universal
condition from allowing arbitrary fields for an empty data declaration. -/
inductive UniformMemberProjection (context : Context) :
    TypeSystem.Ty → Nat → TypeSystem.Ty → Prop where
  | intro
      {base member : TypeSystem.Ty}
      {index : Nat}
      {dataType : ProgramDataSignature}
      {substitution : TypeSystem.ParameterSubstitution}
      (dataType_mem : dataType ∈ context.signatures.dataTypes)
      (substitution_exact :
        ParameterSubstitution.Exact substitution dataType.parameters)
      (base_eq : base = TypeSystem.Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments substitution
          dataType.parameters))
      (base_well_formed : TypeAdmissible context base)
      (member_well_formed : TypeAdmissible context member)
      (constructors_nonempty : dataType.constructors ≠ [])
      (member_uniform : ∀ constructor,
        constructor ∈ dataType.constructors →
          (constructor.payloadTypes.map
            (TypeSystem.ParameterSubstitution.apply substitution))[index]? =
              some member)
      /- The catalog-level projection is stable for every semantically valid
      constructor value at the same nominal base type.  This keeps the
      standalone judgment sound even when it is used with a forgeable Context
      before whole-program catalog uniqueness has been established. -/
      (valid_instantiations : ∀ instantiation,
        DataConstructorInstantiation.Admissible context instantiation →
        instantiation.resultType = base →
        instantiation.payloadTypes[index]? = some member) :
      UniformMemberProjection context base index member

namespace UniformMemberProjection

/-- A valid uniform projection records an admissible nominal base type. -/
theorem base_type_admissible
    {context : Context} {base member : TypeSystem.Ty} {index : Nat}
    (projection : UniformMemberProjection context base index member) :
    TypeAdmissible context base := by
  cases projection with
  | intro _ _ _ baseWellFormed => exact baseWellFormed

/-- A valid uniform projection records an admissible selected member type. -/
theorem member_type_admissible
    {context : Context} {base member : TypeSystem.Ty} {index : Nat}
    (projection : UniformMemberProjection context base index member) :
    TypeAdmissible context member := by
  cases projection with
  | intro _ _ _ _ memberWellFormed => exact memberWellFormed

/-- Any admissible constructor occurrence at the projected nominal base
exposes the same payload type at this position, independently of substitution
list order. -/
theorem admissible_payload
    {context : Context} {base member : TypeSystem.Ty} {index : Nat}
    (projection : UniformMemberProjection context base index member)
    {instantiation : DataConstructorInstantiation}
    (valid : DataConstructorInstantiation.Admissible context instantiation)
    (result_eq : instantiation.resultType = base) :
    instantiation.payloadTypes[index]? = some member := by
  cases projection with
  | intro _ _ _ _ _ _ _ valid_instantiations =>
      exact valid_instantiations instantiation valid result_eq

/-- Closed runtime constructor validity embeds into static use-site
admissibility. -/
theorem valid_payload
    {context : Context} {base member : TypeSystem.Ty} {index : Nat}
    (projection : UniformMemberProjection context base index member)
    {instantiation : DataConstructorInstantiation}
    (valid : DataConstructorInstantiation.Valid context instantiation)
    (result_eq : instantiation.resultType = base) :
    instantiation.payloadTypes[index]? = some member :=
  projection.admissible_payload valid.toAdmissible result_eq

end UniformMemberProjection

/-- Left-to-right typing of a retained place-projection path. -/
inductive ProjectionsHaveType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil (type : TypeSystem.Ty) :
      ProjectionsHaveType context ExpressionTyping type [] type
  | index
      {key : ExpressionId}
      {keyType valueType finalType : TypeSystem.Ty}
      {rest : List PlaceProjection}
      (key_type : ExpressionTyping key keyType)
      (rest_type : ProjectionsHaveType context ExpressionTyping
        valueType rest finalType) :
      ProjectionsHaveType context ExpressionTyping
        (.mapping keyType valueType) (.index key :: rest) finalType
  | member
      {name : String}
      {index : Nat}
      {baseType memberType finalType : TypeSystem.Ty}
      {rest : List PlaceProjection}
      (selected : UniformMemberProjection context baseType index memberType)
      (rest_type : ProjectionsHaveType context ExpressionTyping
        memberType rest finalType) :
      ProjectionsHaveType context ExpressionTyping baseType
        (.member name index :: rest) finalType

namespace ProjectionsHaveType

/-- An empty projection path preserves its input type. -/
theorem nil_iff
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {source target : TypeSystem.Ty} :
    ProjectionsHaveType context ExpressionTyping source [] target ↔
      target = source := by
  constructor
  · intro typing
    cases typing
    rfl
  · rintro rfl
    exact .nil _

/-- The first mapping projection types its key at the mapping key type. -/
theorem index_head
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {key : ExpressionId}
    {keyType valueType finalType : TypeSystem.Ty}
    {rest : List PlaceProjection}
    (typing : ProjectionsHaveType context ExpressionTyping
      (.mapping keyType valueType) (.index key :: rest) finalType) :
    ExpressionTyping key keyType ∧
      ProjectionsHaveType context ExpressionTyping
        valueType rest finalType := by
  cases typing with
  | index key_type rest_type => exact ⟨key_type, rest_type⟩

/-- A retained member head has a catalog-backed uniform positional field,
independently of the diagnostic name carried by the projection. -/
theorem member_head
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {baseType finalType : TypeSystem.Ty}
    {name : String} {index : Nat}
    {rest : List PlaceProjection}
    (typing : ProjectionsHaveType context ExpressionTyping baseType
      (.member name index :: rest) finalType) :
    ∃ memberType,
      UniformMemberProjection context baseType index memberType ∧
      ProjectionsHaveType context ExpressionTyping
        memberType rest finalType := by
  cases typing with
  | member selected rest_type => exact ⟨_, selected, rest_type⟩

end ProjectionsHaveType

/-- A retained place begins at a writable local, follows a well-typed
projection path, and records exactly the path's final type. -/
inductive PlaceHasType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    PlaceResolution → TypeSystem.Ty → Prop where
  | intro
      {place : PlaceResolution}
      {rootType finalType : TypeSystem.Ty}
      (root_type : WritableLocal context place.root rootType)
      (projections_type : ProjectionsHaveType context ExpressionTyping
        rootType place.projections finalType)
      (stored_type_eq : place.type = finalType) :
      PlaceHasType context ExpressionTyping place finalType

namespace PlaceHasType

/-- The external result of place typing is the authoritative retained type. -/
theorem type_eq
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : PlaceHasType context ExpressionTyping place type) :
    place.type = type := by
  cases typing with
  | intro _ _ stored_type_eq => exact stored_type_eq

/-- Invert a place judgment to its monomorphic root and complete projection
derivation. -/
theorem components
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : PlaceHasType context ExpressionTyping place type) :
    ∃ rootType,
      WritableLocal context place.root rootType ∧
      ProjectionsHaveType context ExpressionTyping
        rootType place.projections type := by
  cases typing with
  | intro root_type projections_type stored_type_eq =>
      subst stored_type_eq
      exact ⟨_, root_type, projections_type⟩

end PlaceHasType

/-- The compound assignment spellings supported by the current source
runtime.  Every one is the homogeneous Word operation. -/
inductive WordCompoundAssignmentOperator : Syntax.ValueAssignOp → Prop where
  | add : WordCompoundAssignmentOperator .add
  | subtract : WordCompoundAssignmentOperator .subtract
  | multiply : WordCompoundAssignmentOperator .multiply
  | divide : WordCompoundAssignmentOperator .divide
  | modulo : WordCompoundAssignmentOperator .modulo
  | bitAnd : WordCompoundAssignmentOperator .bitAnd
  | bitXor : WordCompoundAssignmentOperator .bitXor
  | bitOr : WordCompoundAssignmentOperator .bitOr
  | shiftLeft : WordCompoundAssignmentOperator .shiftLeft
  | shiftRight : WordCompoundAssignmentOperator .shiftRight
  | uncheckedAdd : WordCompoundAssignmentOperator .uncheckedAdd
  | uncheckedSubtract : WordCompoundAssignmentOperator .uncheckedSubtract
  | uncheckedMultiply : WordCompoundAssignmentOperator .uncheckedMultiply
  | uncheckedDivide : WordCompoundAssignmentOperator .uncheckedDivide
  | uncheckedModulo : WordCompoundAssignmentOperator .uncheckedModulo

/-- A value assignment validates its place and right-hand occurrence.  Plain
assignment is homogeneous at any place type; current compound forms are
homogeneous at Word.  Neither form owns trait requirements in this runtime
profile. -/
inductive AssignmentHasType
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop where
  | equal
      {assignment : AssignmentResolution}
      {value : ExpressionId}
      {type : TypeSystem.Ty}
      (target_type : PlaceHasType context ExpressionTyping assignment.target type)
      (value_type : ExpressionTyping value type)
      (requirements_eq : assignment.requirements = []) :
      AssignmentHasType context ExpressionTyping assignment .equal value
  | wordCompound
      {assignment : AssignmentResolution}
      {operator : Syntax.ValueAssignOp}
      {value : ExpressionId}
      (operator_kind : WordCompoundAssignmentOperator operator)
      (target_type : PlaceHasType context ExpressionTyping
        assignment.target .word)
      (value_type : ExpressionTyping value .word)
      (requirements_eq : assignment.requirements = []) :
      AssignmentHasType context ExpressionTyping assignment operator value

namespace AssignmentHasType

/-- Assignments in the current runtime profile own no requirement IDs. -/
theorem requirements_empty
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp}
    {value : ExpressionId}
    (typing : AssignmentHasType context ExpressionTyping
      assignment operator value) :
    assignment.requirements = [] := by
  cases typing <;> assumption

/-- Both plain and compound assignments type the right-hand occurrence at the
final place type. -/
theorem operand_types
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp}
    {value : ExpressionId}
    (typing : AssignmentHasType context ExpressionTyping
      assignment operator value) :
    ∃ type,
      PlaceHasType context ExpressionTyping assignment.target type ∧
      ExpressionTyping value type := by
  cases typing with
  | equal target_type value_type => exact ⟨_, target_type, value_type⟩
  | wordCompound _ target_type value_type =>
      exact ⟨.word, target_type, value_type⟩

end AssignmentHasType

/-- Bit-not assignment is valid only at a Word place and, like the other
current assignment forms, owns no requirements. -/
inductive BitNotAssignmentValid
    (context : Context)
    (ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop) :
    AssignmentResolution → Prop where
  | intro
      {assignment : AssignmentResolution}
      (target_type : PlaceHasType context ExpressionTyping
        assignment.target .word)
      (requirements_eq : assignment.requirements = []) :
      BitNotAssignmentValid context ExpressionTyping assignment

namespace BitNotAssignmentValid

theorem requirements_empty
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    (valid : BitNotAssignmentValid context ExpressionTyping assignment) :
    assignment.requirements = [] := by
  cases valid
  assumption

theorem target_word
    {context : Context}
    {ExpressionTyping : ExpressionId → TypeSystem.Ty → Prop}
    {assignment : AssignmentResolution}
    (valid : BitNotAssignmentValid context ExpressionTyping assignment) :
    PlaceHasType context ExpressionTyping assignment.target .word := by
  cases valid
  assumption

end BitNotAssignmentValid

end Solcore.SourceSemantics
end
