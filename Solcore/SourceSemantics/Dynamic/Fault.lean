import Solcore.SourceSemantics.Dynamic.Evaluation

/-!
Declarative faulting big-step dynamics for resolved source programs.

This module deliberately complements, rather than changes, `Evaluation`.  A
fault is justified by positive structural evidence (an absent occurrence, an
unbound identifier, a missing heap cell, a value-shape mismatch, an
unavailable requirement, or a fault in the selected child).  In particular,
there is no rule which turns failure to construct a successful evaluation into
an arbitrary `SemanticFault`.

Successful prefixes use the existing fuel-free relations.  Consequently each
propagation derivation records exactly the effects performed before its chosen
faulting child.  The relation does not assert uniqueness, totality, or a global
first-fault policy for forged malformed carriers; those properties require the
static whole-program invariants.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-! ## Structural absence and shape evidence -/

/-- An expression identity is absent from a heterogeneous occurrence table. -/
inductive ExpressionAbsentIn : List Node → ExpressionId → Prop where
  | nil (id : ExpressionId) : ExpressionAbsentIn [] id
  | expression
      {node : ExpressionNode} {nodes : List Node} {id : ExpressionId}
      (different : node.id ≠ id)
      (tail : ExpressionAbsentIn nodes id) :
      ExpressionAbsentIn (.expression node :: nodes) id
  | statement
      {node : StatementNode} {nodes : List Node} {id : ExpressionId}
      (tail : ExpressionAbsentIn nodes id) :
      ExpressionAbsentIn (.statement node :: nodes) id

/-- A statement identity is absent from a heterogeneous occurrence table. -/
inductive StatementAbsentIn : List Node → StatementId → Prop where
  | nil (id : StatementId) : StatementAbsentIn [] id
  | expression
      {node : ExpressionNode} {nodes : List Node} {id : StatementId}
      (tail : StatementAbsentIn nodes id) :
      StatementAbsentIn (.expression node :: nodes) id
  | statement
      {node : StatementNode} {nodes : List Node} {id : StatementId}
      (different : node.id ≠ id)
      (tail : StatementAbsentIn nodes id) :
      StatementAbsentIn (.statement node :: nodes) id

def ExpressionMissing (source : TypedSource) (id : ExpressionId) : Prop :=
  ExpressionAbsentIn source.nodes id

def StatementMissing (source : TypedSource) (id : StatementId) : Prop :=
  StatementAbsentIn source.nodes id

namespace ExpressionAbsentIn

theorem excludes_mem
    {nodes : List Node} {id : ExpressionId}
    (absent : ExpressionAbsentIn nodes id) {node : ExpressionNode} :
    Node.expression node ∉ nodes ∨ node.id ≠ id := by
  induction absent with
  | nil => simp
  | @expression head nodes id different tail induction =>
      by_cases same : node = head
      · subst node
        exact .inr different
      · rcases induction with missing | differentId
        · exact .inl (by simpa [same] using missing)
        · exact .inr differentId
  | @statement head nodes id tail induction =>
      rcases induction with missing | differentId
      · exact .inl (by simpa using missing)
      · exact .inr differentId

theorem excludes_contains
    {source : TypedSource} {id : ExpressionId}
    (absent : ExpressionMissing source id) {node : ExpressionNode} :
    ¬ ContainsExpression source id node := by
  intro contains
  rcases contains with ⟨member, rfl⟩
  rcases absent.excludes_mem (node := node) with missing | different
  · exact missing member
  · exact different rfl

end ExpressionAbsentIn

namespace StatementAbsentIn

theorem excludes_mem
    {nodes : List Node} {id : StatementId}
    (absent : StatementAbsentIn nodes id) {node : StatementNode} :
    Node.statement node ∉ nodes ∨ node.id ≠ id := by
  induction absent with
  | nil => simp
  | @expression head nodes id tail induction =>
      rcases induction with missing | differentId
      · exact .inl (by simpa using missing)
      · exact .inr differentId
  | @statement head nodes id different tail induction =>
      by_cases same : node = head
      · subst node
        exact .inr different
      · rcases induction with missing | differentId
        · exact .inl (by simpa [same] using missing)
        · exact .inr differentId

theorem excludes_contains
    {source : TypedSource} {id : StatementId}
    (absent : StatementMissing source id) {node : StatementNode} :
    ¬ ContainsStatement source id node := by
  intro contains
  rcases contains with ⟨member, rfl⟩
  rcases absent.excludes_mem (node := node) with missing | different
  · exact missing member
  · exact different rfl

end StatementAbsentIn

/-- First-match lexical lookup has reached the end without finding `id`. -/
inductive Environment.Unbound : Environment → Resolved.LocalId → Prop where
  | nil (id : Resolved.LocalId) : Environment.Unbound [] id
  | cons
      {environment : Environment} {id other : Resolved.LocalId}
      {location : Location}
      (different : other ≠ id)
      (tail : Environment.Unbound environment id) :
      Environment.Unbound ((other, location) :: environment) id

namespace Environment.Unbound

theorem excludes_lookup
    {environment : Environment} {id : Resolved.LocalId}
    (unbound : Environment.Unbound environment id) {location : Location} :
    ¬ Environment.LooksUp environment id location := by
  intro lookup
  induction unbound with
  | nil => cases lookup
  | cons different _ induction =>
      cases lookup with
      | head => exact different rfl
      | tail _ rest => exact induction rest

end Environment.Unbound

/-- A natural index lies strictly beyond the cells present in a heap list. -/
inductive CellMissingAt : List Cell → Nat → Prop where
  | nil (index : Nat) : CellMissingAt [] index
  | tail {cell : Cell} {cells : List Cell} {index : Nat}
      (rest : CellMissingAt cells index) :
      CellMissingAt (cell :: cells) (index + 1)

def Heap.Dangling (heap : Heap) (location : Location) : Prop :=
  CellMissingAt heap.cells location.index

namespace CellMissingAt

theorem excludes_cellAt
    {cells : List Cell} {index : Nat}
    (missing : CellMissingAt cells index) {cell : Cell} :
    ¬ Heap.CellAt cells index cell := by
  intro selected
  induction missing with
  | nil => cases selected
  | tail _ induction =>
      cases selected with
      | tail rest => exact induction rest

end CellMissingAt

namespace Heap.Dangling

theorem excludes_read
    {heap : Heap} {location : Location}
    (dangling : Heap.Dangling heap location) {cell : Cell} :
    ¬ Heap.Reads heap location cell := by
  intro read
  cases read with
  | intro selected => exact dangling.excludes_cellAt selected

end Heap.Dangling

/-- First-match runtime evidence lookup reaches the end without the goal. -/
inductive EvidenceEnvironment.Unbound :
    EvidenceEnvironment → ProgramPredicate → Prop where
  | nil (goal : ProgramPredicate) : EvidenceEnvironment.Unbound [] goal
  | cons
      {environment : EvidenceEnvironment}
      {goal other : ProgramPredicate} {evidence : TraitEvidence}
      (different : other ≠ goal)
      (tail : EvidenceEnvironment.Unbound environment goal) :
      EvidenceEnvironment.Unbound ((other, evidence) :: environment) goal

namespace EvidenceEnvironment.Unbound

theorem excludes_lookup
    {environment : EvidenceEnvironment} {goal : ProgramPredicate}
    (unbound : EvidenceEnvironment.Unbound environment goal)
    {evidence : TraitEvidence} :
    ¬ environment.LooksUp goal evidence := by
  intro lookup
  induction unbound with
  | nil => cases lookup
  | cons different _ induction =>
      cases lookup with
      | head => exact different rfl
      | tail _ rest => exact induction rest

end EvidenceEnvironment.Unbound

/- Closing a retained evidence tree faults at its first missing assumption. -/
mutual
  inductive EvidenceClosureFaults (environment : EvidenceEnvironment) :
      TraitEvidence → Prop where
    | assumption
        {goal : ProgramPredicate}
        (missing : environment.Unbound goal) :
        EvidenceClosureFaults environment (.assumption goal)
    | implementation
        {goal : ProgramPredicate} {implementation : ProgramImplId}
        {premises : List TraitEvidence}
        (premise : EvidenceClosuresFault environment premises) :
        EvidenceClosureFaults environment
          (.implementation goal implementation premises)

  inductive EvidenceClosuresFault (environment : EvidenceEnvironment) :
      List TraitEvidence → Prop where
    | head
        {evidence : TraitEvidence} {rest : List TraitEvidence}
        (fault : EvidenceClosureFaults environment evidence) :
        EvidenceClosuresFault environment (evidence :: rest)
    | tail
        {evidence closed : TraitEvidence} {rest : List TraitEvidence}
        (head : EvidenceCloses environment evidence closed)
        (fault : EvidenceClosuresFault environment rest) :
        EvidenceClosuresFault environment (evidence :: rest)
end

/-- A stable requirement identity is absent from the current ledger. -/
def RequirementMissing (context : Context) (id : RequirementId) : Prop :=
  ∀ requirement, requirement ∈ context.solvedRequirements → requirement.id ≠ id

/-- A requirement has a concrete structural reason it cannot close. -/
inductive RequirementUnavailable (context : Context)
    (environment : EvidenceEnvironment) : RequirementId → Prop where
  | missing
      {id : RequirementId}
      (absent : RequirementMissing context id) :
      RequirementUnavailable context environment id
  | evidence
      {id : RequirementId} {requirement : SolvedRequirement}
      {openEvidence : TraitEvidence}
      (contains : ContainsRequirement context id requirement)
      (representation : PredicateEvidenceRepresents requirement.evidence
        openEvidence)
      (fault : EvidenceClosureFaults environment openEvidence) :
      RequirementUnavailable context environment id

/-- Locate the first unavailable identity after structurally closing a prefix. -/
inductive RequirementListFaults (context : Context)
    (environment : EvidenceEnvironment) : List RequirementId → RequirementId → Prop where
  | head
      {id : RequirementId} {ids : List RequirementId}
      (fault : RequirementUnavailable context environment id) :
      RequirementListFaults context environment (id :: ids) id
  | tail
      {id failed : RequirementId} {ids : List RequirementId}
      {predicate : ProgramPredicate} {closed : TraitEvidence}
      (head : RequirementProducesEvidence context environment id predicate closed)
      (fault : RequirementListFaults context environment ids failed) :
      RequirementListFaults context environment (id :: ids) failed

/-- Close paired requirement/predicate sequences until the first fault. -/
inductive RequirementsFault (context : Context)
    (environment : EvidenceEnvironment) :
    List RequirementId → List ProgramPredicate → RequirementId → Prop where
  | head
      {id : RequirementId} {ids : List RequirementId}
      {predicate : ProgramPredicate} {predicates : List ProgramPredicate}
      (fault : RequirementUnavailable context environment id) :
      RequirementsFault context environment (id :: ids)
        (predicate :: predicates) id
  | tail
      {id failed : RequirementId} {ids : List RequirementId}
      {predicate : ProgramPredicate} {predicates : List ProgramPredicate}
      {closed : TraitEvidence}
      (head : RequirementProducesEvidence context environment id predicate closed)
      (fault : RequirementsFault context environment ids predicates failed) :
      RequirementsFault context environment (id :: ids)
        (predicate :: predicates) failed

/-- Canonical shallow runtime type of every mathematical source value. -/
inductive ValueRuntimeType : Value → Ty → Prop where
  | unit : ValueRuntimeType .unit .unit
  | bool (value : Bool) : ValueRuntimeType (.bool value) .bool
  | word (value : Core.Word) : ValueRuntimeType (.word value) .word
  | integer (value : Int) : ValueRuntimeType (.integer value) .integer
  | product
      {left right : Value} {leftType rightType : Ty}
      (left_type : ValueRuntimeType left leftType)
      (right_type : ValueRuntimeType right rightType) :
      ValueRuntimeType (.product left right) (.product leftType rightType)
  | proxy (inner : Ty) : ValueRuntimeType (.proxy inner) (.proxy inner)
  | constructed
      (instantiation : DataConstructorInstantiation) (arguments : List Value) :
      ValueRuntimeType (.constructed instantiation arguments)
        instantiation.resultType
  | mapping (keyType valueType : Ty) (entries : List (Value × Value)) :
      ValueRuntimeType (.mapping keyType valueType entries)
        (.mapping keyType valueType)
  | closure (function : Closure) :
      ValueRuntimeType (.closure function)
        (.function
          (Ty.productMany (function.parameters.map fun binder => binder.scheme.body))
          function.resultType)
  | global (function : GlobalFunction) :
      ValueRuntimeType (.global function) function.instantiation.type
  | builtin (function : BuiltinFunction) :
      ValueRuntimeType (.builtin function) function.id.type

/-- The first source-ordered argument whose runtime type differs from the
declared parameter type.  A successfully typed prefix is explicit. -/
inductive ValuesFirstTypeMismatch :
    List Value → List Ty → Ty → Ty → Prop where
  | head
      {value : Value} {values : List Value} {expected actual : Ty}
      {types : List Ty}
      (actual_type : ValueRuntimeType value actual)
      (different : actual ≠ expected) :
      ValuesFirstTypeMismatch (value :: values) (expected :: types)
        expected actual
  | tail
      {value : Value} {values : List Value} {expected : Ty}
      {types : List Ty} {failedExpected failedActual : Ty}
      (head_type : ValueRuntimeType value expected)
      (tail_fault : ValuesFirstTypeMismatch values types
        failedExpected failedActual) :
      ValuesFirstTypeMismatch (value :: values) (expected :: types)
        failedExpected failedActual

def BooleanValue : Value → Prop
  | .bool _ => True
  | _ => False

def IntegerValue : Value → Prop
  | .integer _ => True
  | _ => False

def WordValue : Value → Prop
  | .word _ => True
  | _ => False

def NumericPair : Value → Value → Prop
  | .word _, .word _ => True
  | .integer _, .integer _ => True
  | _, _ => False

def BooleanPair : Value → Value → Prop
  | .bool _, .bool _ => True
  | _, _ => False

def CallableValue : Value → Prop
  | .closure _ | .global _ | .builtin _ => True
  | _ => False

def ConstructedValue : Value → Prop
  | .constructed _ _ => True
  | _ => False

def MappingValue : Value → Prop
  | .mapping _ _ _ => True
  | _ => False

inductive NumericBinaryOperator : Syntax.BinaryOp → Prop where
  | multiply : NumericBinaryOperator .multiply
  | divide : NumericBinaryOperator .divide
  | modulo : NumericBinaryOperator .modulo
  | add : NumericBinaryOperator .add
  | subtract : NumericBinaryOperator .subtract
  | bitAnd : NumericBinaryOperator .bitAnd
  | bitXor : NumericBinaryOperator .bitXor
  | bitOr : NumericBinaryOperator .bitOr
  | less : NumericBinaryOperator .less
  | greater : NumericBinaryOperator .greater
  | lessEqual : NumericBinaryOperator .lessEqual
  | greaterEqual : NumericBinaryOperator .greaterEqual

inductive LogicalBinaryOperator : Syntax.BinaryOp → Prop where
  | logicalAnd : LogicalBinaryOperator .logicalAnd
  | logicalOr : LogicalBinaryOperator .logicalOr

/-- A primitive unary operator has received a structurally wrong operand. -/
inductive UnaryPrimitiveOperandInvalid : Syntax.UnaryOp → Value → Prop where
  | logicalNot {input : Value}
      (invalid : ¬ BooleanValue input) :
      UnaryPrimitiveOperandInvalid .logicalNot input
  | bitNot {input : Value}
      (not_word : ¬ WordValue input)
      (not_integer : ¬ IntegerValue input) :
      UnaryPrimitiveOperandInvalid .bitNot input

/-- A strict primitive binary operator has received an invalid pair. -/
inductive BinaryPrimitiveOperandsInvalid :
    Syntax.BinaryOp → Value → Value → Prop where
  | numeric
      {operator : Syntax.BinaryOp} {left right : Value}
      (operator_class : NumericBinaryOperator operator)
      (invalid : ¬ NumericPair left right) :
      BinaryPrimitiveOperandsInvalid operator left right
  | logical
      {operator : Syntax.BinaryOp} {left right : Value}
      (operator_class : LogicalBinaryOperator operator)
      (invalid : ¬ BooleanPair left right) :
      BinaryPrimitiveOperandsInvalid operator left right

/-- A lazy Boolean operator cannot decide whether to select its right child. -/
inductive BinaryLeftOperandInvalid : Syntax.BinaryOp → Value → Prop where
  | logicalAnd {left : Value}
      (invalid : ¬ BooleanValue left) :
      BinaryLeftOperandInvalid .logicalAnd left
  | logicalOr {left : Value}
      (invalid : ¬ BooleanValue left) :
      BinaryLeftOperandInvalid .logicalOr left

/-- Source compound-assignment spelling translated to its primitive operator. -/
inductive AssignmentOperatorBinary :
    Syntax.ValueAssignOp → Syntax.BinaryOp → Prop where
  | add : AssignmentOperatorBinary .add .add
  | subtract : AssignmentOperatorBinary .subtract .subtract
  | multiply : AssignmentOperatorBinary .multiply .multiply
  | divide : AssignmentOperatorBinary .divide .divide
  | modulo : AssignmentOperatorBinary .modulo .modulo
  | bitAnd : AssignmentOperatorBinary .bitAnd .bitAnd
  | bitXor : AssignmentOperatorBinary .bitXor .bitXor
  | bitOr : AssignmentOperatorBinary .bitOr .bitOr

inductive AssignmentOperandsInvalid :
    Syntax.ValueAssignOp → Option Value → Value → Prop where
  | uninitialized
      {operator : Syntax.ValueAssignOp} {right : Value}
      (not_equal : operator ≠ .equal) :
      AssignmentOperandsInvalid operator none right
  | compound
      {operator : Syntax.ValueAssignOp} {binary : Syntax.BinaryOp}
      {left right : Value}
      (corresponds : AssignmentOperatorBinary operator binary)
      (invalid : BinaryPrimitiveOperandsInvalid binary left right) :
      AssignmentOperandsInvalid operator (some left) right

/-- Known primitive coercions reject only a wrong-shaped source value. -/
inductive PrimitiveCoercionInputInvalid : CoercionStep → Value → Prop where
  | integerToWord
      {step : CoercionStep} {input : Value}
      (source_eq : step.source = .integer)
      (target_eq : step.target = .word)
      (invalid : ¬ IntegerValue input) :
      PrimitiveCoercionInputInvalid step input
  | wordToInteger
      {step : CoercionStep} {input : Value}
      (source_eq : step.source = .word)
      (target_eq : step.target = .integer)
      (invalid : ¬ WordValue input) :
      PrimitiveCoercionInputInvalid step input

/-- A payload index is structurally past the end of its value list. -/
inductive ValueIndexMissing : List Value → Nat → Prop where
  | nil (index : Nat) : ValueIndexMissing [] index
  | tail {value : Value} {values : List Value} {index : Nat}
      (missing : ValueIndexMissing values index) :
      ValueIndexMissing (value :: values) (index + 1)

/-- A source function identity has no signature in the program catalog. -/
def FunctionSignatureMissing (program : Program)
    (id : Resolved.DeclarationId) : Prop :=
  ∀ signature, signature ∈ program.signatures.functions → signature.id ≠ id

/-- A source function identity has no body in the program body catalog. -/
def FunctionBodyMissing (program : Program)
    (id : Resolved.DeclarationId) : Prop :=
  ∀ definition, definition ∈ program.functions → definition.body.owner ≠ id

/-- No constructor catalog entry carries the retained constructor identity. -/
def ConstructorCatalogMissing (context : Context)
    (constructor : ProgramDataConstructorId) : Prop :=
  ∀ dataType, dataType ∈ context.signatures.dataTypes →
    ∀ signature, signature ∈ dataType.constructors →
      signature.id ≠ constructor

/-- One constructor identity has a unique catalog carrier.  Whole-program
well-formedness provides this fact; keeping it explicit also makes metadata
faults disjoint from a successful instantiation in forgeable catalogs. -/
structure UniqueConstructorCatalogEntry (context : Context)
    (constructor : ProgramDataConstructorId)
    (dataType : ProgramDataSignature)
    (signature : ProgramDataConstructorSignature) : Prop where
  data_mem : dataType ∈ context.signatures.dataTypes
  signature_mem : signature ∈ dataType.constructors
  id_eq : signature.id = constructor
  unique : ∀ otherData otherSignature,
    otherData ∈ context.signatures.dataTypes →
    otherSignature ∈ otherData.constructors →
    otherSignature.id = constructor →
    otherData = dataType ∧ otherSignature = signature

/-- First source-ordered mismatch between retained and expected type metadata. -/
inductive TypesFirstMismatch : List Ty → List Ty → Ty → Ty → Prop where
  | head
      {actual expected : Ty} {actuals expecteds : List Ty}
      (different : actual ≠ expected) :
      TypesFirstMismatch (actual :: actuals) (expected :: expecteds)
        expected actual
  | tail
      {type : Ty} {actuals expecteds : List Ty}
      {failedExpected failedActual : Ty}
      (fault : TypesFirstMismatch actuals expecteds failedExpected failedActual) :
      TypesFirstMismatch (type :: actuals) (type :: expecteds)
        failedExpected failedActual

/-- Exact, catalog-backed constructor metadata failures. -/
inductive ConstructorMetadataFaults (context : Context)
    (instantiation : DataConstructorInstantiation) : SemanticFault → Prop where
  | missing
      (absent : ConstructorCatalogMissing context instantiation.constructor) :
      ConstructorMetadataFaults context instantiation
        (.missingDeclaration instantiation.constructor.dataType)
  | owner
      {dataType : ProgramDataSignature}
      {signature : ProgramDataConstructorSignature}
      (entry : UniqueConstructorCatalogEntry context instantiation.constructor
        dataType signature)
      (different : signature.id.dataType ≠ dataType.id) :
      ConstructorMetadataFaults context instantiation
        (.missingDeclaration instantiation.constructor.dataType)
  | payloadArity
      {dataType : ProgramDataSignature}
      {signature : ProgramDataConstructorSignature}
      (entry : UniqueConstructorCatalogEntry context instantiation.constructor
        dataType signature)
      (mismatch : signature.payloadTypes.length ≠
        instantiation.payloadTypes.length) :
      ConstructorMetadataFaults context instantiation
        (.argumentArityMismatch signature.payloadTypes.length
          instantiation.payloadTypes.length)
  | payloadType
      {dataType : ProgramDataSignature}
      {signature : ProgramDataConstructorSignature}
      {expected actual : Ty}
      (entry : UniqueConstructorCatalogEntry context instantiation.constructor
        dataType signature)
      (mismatch : TypesFirstMismatch instantiation.payloadTypes
        (signature.payloadTypes.map
          (ParameterSubstitution.apply instantiation.parameterSubstitution))
        expected actual) :
      ConstructorMetadataFaults context instantiation
        (.typeMismatch expected actual)
  | resultType
      {dataType : ProgramDataSignature}
      {signature : ProgramDataConstructorSignature}
      (entry : UniqueConstructorCatalogEntry context instantiation.constructor
        dataType signature)
      (different : instantiation.resultType ≠
        Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments
            instantiation.parameterSubstitution dataType.parameters)) :
      ConstructorMetadataFaults context instantiation
        (.typeMismatch
          (Ty.nominal dataType.id
            (ParameterSubstitution.orderedArguments
              instantiation.parameterSubstitution dataType.parameters))
          instantiation.resultType)

/-- Static shape of the retained source spelling is inconsistent with its
resolved pattern program.  These premises inspect only pattern metadata; they
do not negate dynamic matching or statement evaluation. -/
inductive PatternMalformed (context : Context) : TypedMatchPattern → Prop where
  | source
      {pattern : TypedMatchPattern}
      (no_representation : ∀ rootArity,
        ¬ MatchPatternSourceRepresents context pattern.source
          pattern.resolution rootArity) :
      PatternMalformed context pattern
  | prefix
      {pattern : TypedMatchPattern} {rootArity : Nat}
      (source_represents : MatchPatternSourceRepresents context pattern.source
        pattern.resolution rootArity)
      (not_delimited :
        ¬ PatternInstructionSkips
          (matchPatternResolutionInstructions pattern.resolution rootArity) []) :
      PatternMalformed context pattern

/-- The first malformed ordered match arm.  Well-formed preceding arms must
have explicit semantic non-match derivations, preserving selection order. -/
inductive MatchCasesPatternFault (context : Context) (value : Value) :
    List TypedMatchCase → Prop where
  | head
      {arm : TypedMatchCase} {rest : List TypedMatchCase}
      (malformed : PatternMalformed context arm.pattern) :
      MatchCasesPatternFault context value (arm :: rest)
  | tail
      {arm : TypedMatchCase} {rest : List TypedMatchCase}
      (does_not_match : PatternDoesNotMatch context arm.pattern value)
      (fault : MatchCasesPatternFault context value rest) :
      MatchCasesPatternFault context value (arm :: rest)

/-- Values admitted by the closed Core-representable residualization boundary.
This is not the value domain of the general source runtime. -/
inductive RuntimeBoundaryAccepts : Value → Prop where
  | unit : RuntimeBoundaryAccepts .unit
  | bool (value : Bool) : RuntimeBoundaryAccepts (.bool value)
  | word (value : Core.Word) : RuntimeBoundaryAccepts (.word value)
  | product
      {left right : Value}
      (left_ok : RuntimeBoundaryAccepts left)
      (right_ok : RuntimeBoundaryAccepts right) :
      RuntimeBoundaryAccepts (.product left right)

/-- Positive structural rejection by the closed Core-representable
residualization boundary. Nominal, mapping, and function values remain valid
source-runtime values even though they cannot cross this narrower boundary. -/
inductive RuntimeBoundaryRejects : Value → Prop where
  | integer (value : Int) : RuntimeBoundaryRejects (.integer value)
  | proxy (inner : Ty) : RuntimeBoundaryRejects (.proxy inner)
  | constructed (instantiation : DataConstructorInstantiation)
      (arguments : List Value) :
      RuntimeBoundaryRejects (.constructed instantiation arguments)
  | mapping (keyType valueType : Ty) (entries : List (Value × Value)) :
      RuntimeBoundaryRejects (.mapping keyType valueType entries)
  | closure (function : Closure) : RuntimeBoundaryRejects (.closure function)
  | global (function : GlobalFunction) : RuntimeBoundaryRejects (.global function)
  | builtin (function : BuiltinFunction) : RuntimeBoundaryRejects (.builtin function)
  | productLeft
      {left right : Value}
      (left_rejected : RuntimeBoundaryRejects left) :
      RuntimeBoundaryRejects (.product left right)
  | productRight
      {left right : Value}
      (left_ok : RuntimeBoundaryAccepts left)
      (right_rejected : RuntimeBoundaryRejects right) :
      RuntimeBoundaryRejects (.product left right)

/-! The shape evidence used by fault introduction is incompatible with the
corresponding successful primitive relations. -/

namespace UnaryPrimitiveOperandInvalid

theorem excludes_application
    {operator : Syntax.UnaryOp} {input : Value}
    (invalid : UnaryPrimitiveOperandInvalid operator input) :
    ¬ ∃ output, UnaryPrimitiveApplies operator input output := by
  rintro ⟨output, applies⟩
  cases invalid <;> cases applies <;>
    simp_all [BooleanValue, WordValue, IntegerValue]

end UnaryPrimitiveOperandInvalid

namespace BinaryPrimitiveOperandsInvalid

theorem excludes_application
    {operator : Syntax.BinaryOp} {left right : Value}
    (invalid : BinaryPrimitiveOperandsInvalid operator left right) :
    ¬ ∃ output, BinaryPrimitiveApplies operator left right output := by
  rintro ⟨output, applies⟩
  cases invalid with
  | numeric operator_class invalid_pair =>
      cases operator_class <;> cases applies <;> simp_all [NumericPair]
  | logical operator_class invalid_pair =>
      cases operator_class <;> cases applies <;> simp_all [BooleanPair]

end BinaryPrimitiveOperandsInvalid

namespace PrimitiveCoercionInputInvalid

theorem excludes_application
    {step : CoercionStep} {input : Value}
    (invalid : PrimitiveCoercionInputInvalid step input) :
    ¬ ∃ output, PrimitiveCoercionApplies step input output := by
  rintro ⟨output, applies⟩
  cases invalid <;> cases applies <;>
    simp_all [IntegerValue, WordValue, Ty.integer, Ty.word]

end PrimitiveCoercionInputInvalid

namespace RuntimeBoundaryAccepts

theorem excludes_rejection
    {value : Value} (accepted : RuntimeBoundaryAccepts value) :
    ¬ RuntimeBoundaryRejects value := by
  intro rejected
  induction accepted with
  | unit | bool | word => cases rejected
  | product left_ok right_ok left_induction right_induction =>
      cases rejected with
      | productLeft left_rejected => exact left_induction left_rejected
      | productRight _ right_rejected => exact right_induction right_rejected

end RuntimeBoundaryAccepts

/-! ## Faulting big-step relations -/

set_option maxHeartbeats 1200000 in
mutual

  /-- Fault while evaluating one expression occurrence. -/
  inductive ExpressionFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionId → SemanticFault → Heap → Prop where
    | missing
        {context evidence source environment heap id}
        (absent : ExpressionMissing source id) :
        ExpressionFaults program context evidence source environment heap id
          (.missingExpression id) heap
    | form
        {context evidence source environment before after id node reason}
        (contains : ContainsExpression source id node)
        (fault : ExpressionFormFaults program context evidence source environment
          before node.form node.requirements node.coercions reason after) :
        ExpressionFaults program context evidence source environment before id
          reason after
    | coercion
        {context evidence source environment before middle after id node raw reason}
        (contains : ContainsExpression source id node)
        (form : ExpressionFormEvaluates program context evidence source environment
          before node.form node.requirements node.coercions raw middle)
        (fault : CoercionPathFaults program context evidence middle node.coercions
          raw reason after) :
        ExpressionFaults program context evidence source environment before id
          reason after

  /-- Fault in the raw form, before the occurrence's result coercion path. -/
  inductive ExpressionFormFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionForm → List RequirementId →
        List CoercionStep → SemanticFault → Heap → Prop where
    | integerRequirement
        {context evidence source environment heap literal resolution requirements
          coercions}
        (layout : OrdinaryRequirementLayout requirements coercions
          [resolution.requirement])
        (fault : RequirementUnavailable context evidence resolution.requirement) :
        ExpressionFormFaults program context evidence source environment heap
          (.integerLiteral literal resolution) requirements coercions
          (.unsatisfiedRequirement resolution.requirement) heap
    | localUnbound
        {context evidence source environment heap name binder requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (unbound : environment.Unbound binder) :
        ExpressionFormFaults program context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.unboundLocal binder) heap
    | localDangling
        {context evidence source environment heap name binder requirements coercions
          location}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Environment.LooksUp environment binder location)
        (dangling : heap.Dangling location) :
        ExpressionFormFaults program context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.danglingLocation location) heap
    | localUninitialized
        {context evidence source environment heap name binder requirements coercions
          location cell}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor_empty : cell.generalized = none)
        (empty : cell.value = none)
        (not_mapping : ¬ ∃ keyType valueType, cell.type = .mapping keyType valueType) :
        ExpressionFormFaults program context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.uninitializedLocation location) heap
    | declarationRequirement
        {context evidence source environment heap name instantiation requirements
          coercions owned failed}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : RequirementListFaults context evidence owned failed) :
        ExpressionFormFaults program context evidence source environment heap
          (.reference name (.declaration instantiation)) requirements coercions
          (.unsatisfiedRequirement failed) heap
    | group
        {context evidence source environment before after inner requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program context evidence source environment
          before inner reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.group inner) requirements coercions reason after
    | tuple
        {context evidence source environment before after elements requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program context evidence source environment
          before elements reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.tuple elements) requirements coercions reason after
    | unaryOperand
        {context evidence source environment before after operator operand
          requirements coercions owned reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : ExpressionFaults program context evidence source environment
          before operand reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.unary operator operand) requirements coercions reason after
    | unaryApply
        {context evidence source environment before middle after operator operand
          requirements coercions owned input reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (operand_evaluates : ExpressionEvaluates program context evidence source
          environment before operand input middle)
        (fault : UnaryOperationFaults program context evidence middle operator
          owned input reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.unary operator operand) requirements coercions reason after
    | binaryLeft
        {context evidence source environment before after left operator right
          requirements coercions owned reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : ExpressionFaults program context evidence source environment
          before left reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | binaryLeftOperand
        {context evidence source environment before after left operator right
          requirements coercions owned leftValue}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program context evidence source
          environment before left leftValue after)
        (invalid : BinaryLeftOperandInvalid operator leftValue) :
        ExpressionFormFaults program context evidence source environment before
          (.binary left operator right) requirements coercions
          (.invalidBinaryOperands operator) after
    | binaryRight
        {context evidence source environment before leftHeap after left operator
          right requirements coercions owned leftValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (fault : ExpressionFaults program context evidence source environment
          leftHeap right reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | binaryApply
        {context evidence source environment before leftHeap rightHeap after left
          operator right requirements coercions owned leftValue rightValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (right_evaluates : ExpressionEvaluates program context evidence source
          environment leftHeap right rightValue rightHeap)
        (fault : BinaryOperationFaults program context evidence rightHeap operator
          owned leftValue rightValue reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | conditionalCondition
        {context evidence source environment before after condition thenBranch
          elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program context evidence source environment
          before condition reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | conditionalType
        {context evidence source environment before after condition thenBranch
          elseBranch requirements coercions value actual}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        ExpressionFormFaults program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          (.typeMismatch .bool actual) after
    | conditionalTrueBranch
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) middle)
        (fault : ExpressionFaults program context evidence source environment
          middle thenBranch reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | conditionalFalseBranch
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) middle)
        (fault : ExpressionFaults program context evidence source environment
          middle elseBranch reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | directCalleeMissing
        {context evidence source environment heap callee arguments instantiation
          requirements coercions}
        (absent : ExpressionMissing source callee) :
        ExpressionFormFaults program context evidence source environment heap
          (.call callee arguments (.declaration instantiation)) requirements
          coercions (.missingExpression callee) heap
    | directArguments
        {context evidence source environment before after callee arguments
          instantiation requirements coercions calleeNode name reason}
        (callee_contains : ContainsExpression source callee calleeNode)
        (callee_form : calleeNode.form =
          .reference name (.declaration instantiation))
        (fault : ExpressionsFault program context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions reason after
    | directRequirements
        {context evidence source environment before after callee arguments
          instantiation requirements coercions argumentValues failed}
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments argumentValues after)
        (fault : RequirementsFault context evidence requirements
          instantiation.predicates failed) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions (.unsatisfiedRequirement failed) after
    | directApply
        {context evidence source environment before argumentsHeap after callee
          arguments instantiation requirements coercions argumentValues
          calleeEvidence reason}
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments argumentValues argumentsHeap)
        (call_evidence : DirectCallProducesEvidence context evidence requirements
          coercions instantiation.predicates calleeEvidence)
        (fault : CallableFaults program context evidence calleeEvidence
          argumentsHeap (.global ⟨instantiation, calleeEvidence⟩) argumentValues
          reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions reason after
    | builtinArguments
        {context evidence source environment before after callee
          arguments function requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions reason after
    | builtinApply
        {context evidence source environment before argumentsHeap after
          callee arguments function requirements coercions argumentValues reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments argumentValues argumentsHeap)
        (fault : CallableFaults program context evidence [] argumentsHeap
          (.builtin ⟨function⟩) argumentValues reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions reason after
    | indirectCallee
        {context evidence source environment before after callee arguments metadata
          requirements coercions reason}
        (fault : ExpressionFaults program context evidence source environment
          before callee reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectNotCallable
        {context evidence source environment before after callee arguments metadata
          requirements coercions callable}
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable after)
        (not_callable : ¬ CallableValue callable) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          .notCallable after
    | indirectArguments
        {context evidence source environment before calleeHeap after callee arguments
          metadata requirements coercions callable reason}
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable calleeHeap)
        (callable_shape : CallableValue callable)
        (fault : ExpressionsFault program context evidence source environment
          calleeHeap arguments reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectSourceArity
        {context evidence source environment before calleeHeap argumentsHeap callee
          arguments metadata requirements coercions callable argumentValues}
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment calleeHeap arguments argumentValues argumentsHeap)
        (mismatch : metadata.argumentCount ≠ arguments.length) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          (.argumentArityMismatch metadata.argumentCount arguments.length)
          argumentsHeap
    | indirectArgumentCoercion
        {context evidence source environment before calleeHeap argumentHeap after
          callee arguments metadata requirements coercions callable argumentValues
          packed reason}
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (source_arity : arguments.length = metadata.argumentCount)
        (pack : ValuesPack argumentValues packed)
        (fault : CoercionPathFaults program context evidence argumentHeap
          metadata.argumentCoercions packed reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectApply
        {context evidence source environment before calleeHeap argumentHeap
          coercedHeap after callee arguments metadata requirements coercions
          callable argumentValues packed coerced appliedArguments reason
          invocationEvidence}
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (pack_before : ValuesPack argumentValues packed)
        (argument_coercions : CoercionPathExecutes program context evidence
          argumentHeap metadata.argumentCoercions packed coerced coercedHeap)
        (pack_after : ValuesPack appliedArguments coerced)
        (source_arity : arguments.length = metadata.argumentCount)
        (applied_arity : appliedArguments.length = metadata.argumentCount)
        (fault : CallableFaults program context evidence invocationEvidence
          coercedHeap callable appliedArguments reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | constructorArgument
        {context evidence source environment before after instantiation arguments
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.constructor instantiation arguments) requirements coercions reason after
    | constructorMetadata
        {context evidence source environment heap instantiation arguments
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ConstructorMetadataFaults context instantiation reason) :
        ExpressionFormFaults program context evidence source environment heap
          (.constructor instantiation arguments) requirements coercions
          reason heap
    | memberBase
        {context evidence source environment before after base name index
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program context evidence source environment
          before base reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.member base name index) requirements coercions reason after
    | memberShape
        {context evidence source environment before after base name index
          requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base value after)
        (not_constructed : ¬ ConstructedValue value) :
        ExpressionFormFaults program context evidence source environment before
          (.member base name index) requirements coercions .invalidProjection after
    | memberIndex
        {context evidence source environment before after base name index
          requirements coercions instantiation arguments}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base (.constructed instantiation arguments) after)
        (missing : ValueIndexMissing arguments index) :
        ExpressionFormFaults program context evidence source environment before
          (.member base name index) requirements coercions .invalidProjection after
    | indexBase
        {context evidence source environment before after base index requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program context evidence source environment
          before base reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.index base index) requirements coercions reason after
    | indexKey
        {context evidence source environment before middle after base index
          requirements coercions baseValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base baseValue middle)
        (fault : ExpressionFaults program context evidence source environment
          middle index reason after) :
        ExpressionFormFaults program context evidence source environment before
          (.index base index) requirements coercions reason after
    | indexShape
        {context evidence source environment before middle after base index
          requirements coercions baseValue key}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base baseValue middle)
        (index_evaluates : ExpressionEvaluates program context evidence source
          environment middle index key after)
        (not_mapping : ¬ MappingValue baseValue) :
        ExpressionFormFaults program context evidence source environment before
          (.index base index) requirements coercions .invalidProjection after
    | indexKeyType
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key actual}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program context evidence source
          environment middle index key after)
        (actual_type : ValueRuntimeType key actual)
        (mismatch : actual ≠ keyType) :
        ExpressionFormFaults program context evidence source environment before
          (.index base index) requirements coercions
          (.typeMismatch keyType actual) after

  /-- First fault in a left-to-right expression vector. -/
  inductive ExpressionsFault (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List ExpressionId → SemanticFault → Heap → Prop where
    | head
        {context evidence source environment before after expression expressions
          reason}
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        ExpressionsFault program context evidence source environment before
          (expression :: expressions) reason after
    | tail
        {context evidence source environment before middle after expression
          expressions value reason}
        (head : ExpressionEvaluates program context evidence source environment
          before expression value middle)
        (fault : ExpressionsFault program context evidence source environment
          middle expressions reason after) :
        ExpressionsFault program context evidence source environment before
          (expression :: expressions) reason after

  /-- Primitive/method-selected unary application fault. -/
  inductive UnaryOperationFaults (program : Program) :
      Context → EvidenceEnvironment → Heap → Syntax.UnaryOp →
        List RequirementId → Value → SemanticFault → Heap → Prop where
    | primitive
        {context evidence heap operator input}
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        UnaryOperationFaults program context evidence heap operator [] input
          (.invalidUnaryOperand operator) heap
    | requirement
        {context evidence heap operator requirements input failed}
        (fault : RequirementListFaults context evidence requirements failed) :
        UnaryOperationFaults program context evidence heap operator requirements
          input (.unsatisfiedRequirement failed) heap
    | method
        {context evidence before after operator requirements input traitName
          methodName bodyInstance calleeEvidence reason}
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program bodyInstance calleeEvidence before [input]
          reason after) :
        UnaryOperationFaults program context evidence before operator requirements
          input reason after

  /-- Primitive/method-selected strict binary application fault. -/
  inductive BinaryOperationFaults (program : Program) :
      Context → EvidenceEnvironment → Heap → Syntax.BinaryOp →
        List RequirementId → Value → Value → SemanticFault → Heap → Prop where
    | primitive
        {context evidence heap operator left right}
        (invalid : BinaryPrimitiveOperandsInvalid operator left right) :
        BinaryOperationFaults program context evidence heap operator [] left right
          (.invalidBinaryOperands operator) heap
    | requirement
        {context evidence heap operator requirements left right failed}
        (fault : RequirementListFaults context evidence requirements failed) :
        BinaryOperationFaults program context evidence heap operator requirements
          left right (.unsatisfiedRequirement failed) heap
    | method
        {context evidence before after operator requirements left right traitName
          methodName bodyInstance calleeEvidence reason}
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program bodyInstance calleeEvidence before [left, right]
          reason after) :
        BinaryOperationFaults program context evidence before operator requirements
          left right reason after

  /-- Fault in one evidence-checked coercion edge. -/
  inductive CoercionStepFaults (program : Program) :
      Context → EvidenceEnvironment → Heap → CoercionStep → Value →
        SemanticFault → Heap → Prop where
    | requirement
        {context evidence heap step input failed}
        (fault : RequirementListFaults context evidence step.requirements failed) :
        CoercionStepFaults program context evidence heap step input
          (.unsatisfiedRequirement failed) heap
    | primitiveInput
        {context evidence heap step input actual}
        (no_source_method : ∀ bodyInstance calleeEvidence,
          ¬ OperatorMethodSelected program context evidence "Coerce" "coerce"
            step.requirements bodyInstance calleeEvidence)
        (invalid : PrimitiveCoercionInputInvalid step input)
        (actual_type : ValueRuntimeType input actual) :
        CoercionStepFaults program context evidence heap step input
          (.typeMismatch step.source actual) heap
    | method
        {context evidence before after step input bodyInstance calleeEvidence reason}
        (selected : OperatorMethodSelected program context evidence "Coerce"
          "coerce" step.requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program bodyInstance calleeEvidence before [input]
          reason after) :
        CoercionStepFaults program context evidence before step input reason after

  /-- First fault in a retained coercion path. -/
  inductive CoercionPathFaults (program : Program) :
      Context → EvidenceEnvironment → Heap → List CoercionStep → Value →
        SemanticFault → Heap → Prop where
    | head
        {context evidence before after step steps input reason}
        (fault : CoercionStepFaults program context evidence before step input
          reason after) :
        CoercionPathFaults program context evidence before (step :: steps) input
          reason after
    | tail
        {context evidence before middle after step steps input converted reason}
        (head : CoercionStepExecutes program context evidence before step input
          converted middle)
        (fault : CoercionPathFaults program context evidence middle steps converted
          reason after) :
        CoercionPathFaults program context evidence before (step :: steps) input
          reason after

  /-- Fault while applying an already evaluated callee. -/
  inductive CallableFaults (program : Program) :
      Context → EvidenceEnvironment → EvidenceEnvironment → Heap →
        Value → List Value → SemanticFault → Heap → Prop where
    | notCallable
        {context callerEvidence invocationEvidence heap callable arguments}
        (invalid : ¬ CallableValue callable) :
        CallableFaults program context callerEvidence invocationEvidence heap
          callable arguments .notCallable heap
    | builtinArity
        {context callerEvidence invocationEvidence heap function arguments}
        (mismatch : function.id.parameterTypes.length ≠ arguments.length) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.builtin function) arguments
          (.argumentArityMismatch function.id.parameterTypes.length
            arguments.length) heap
    | builtinArgumentType
        {context callerEvidence invocationEvidence heap function arguments
          expected actual}
        (arity : function.id.parameterTypes.length = arguments.length)
        (mismatch : ValuesFirstTypeMismatch arguments function.id.parameterTypes
          expected actual) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.builtin function) arguments (.typeMismatch expected actual) heap
    | globalSignatureMissing
        {context callerEvidence invocationEvidence heap function arguments}
        (missing : FunctionSignatureMissing program
          function.instantiation.declaration) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.missingDeclaration function.instantiation.declaration) heap
    | globalBodyMissing
        {context callerEvidence invocationEvidence heap function arguments}
        (missing : FunctionBodyMissing program function.instantiation.declaration) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.missingDeclaration function.instantiation.declaration) heap
    | globalArity
        {context callerEvidence invocationEvidence heap function arguments
          bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.argumentArityMismatch bodyInstance.source.inputs.length
            arguments.length) heap
    | globalBody
        {context callerEvidence invocationEvidence before after function arguments
          bodyInstance reason}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (invocation_eq : invocationEvidence = function.evidence)
        (fault : BodyFaults program bodyInstance invocationEvidence before arguments
          reason after) :
        CallableFaults program context callerEvidence invocationEvidence before
          (.global function) arguments reason after
    | closureArity
        {context callerEvidence invocationEvidence heap function arguments}
        (mismatch : function.parameters.length ≠ arguments.length) :
        CallableFaults program context callerEvidence invocationEvidence heap
          (.closure function) arguments
          (.argumentArityMismatch function.parameters.length arguments.length) heap
    | closureBody
        {context callerEvidence invocationEvidence before bound after function
          arguments environment parameterTypes callContext finalContext reason}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (fault : FunctionStatementsFault program callContext function.evidence
          function.source environment bound function.body finalContext reason after) :
        CallableFaults program context callerEvidence invocationEvidence before
          (.closure function) arguments reason after
    | closureControlEscape
        {context callerEvidence invocationEvidence before bound after function
          arguments environment parameterTypes callContext finalContext outcome}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (escaped : (∃ escapedEnvironment, outcome = .breaking escapedEnvironment) ∨
          (∃ escapedEnvironment, outcome = .continuing escapedEnvironment)) :
        CallableFaults program context callerEvidence invocationEvidence before
          (.closure function) arguments .controlEscapedFunction after

  /-- Fault while invoking an instantiated catalog body. -/
  inductive BodyFaults (program : Program) :
      BodyInstance → EvidenceEnvironment → Heap → List Value →
        SemanticFault → Heap → Prop where
    | arity
        {bodyInstance evidence heap arguments}
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        BodyFaults program bodyInstance evidence heap arguments
          (.argumentArityMismatch bodyInstance.source.inputs.length
            arguments.length) heap
    | statements
        {bodyInstance evidence before bound after arguments environment roots
          inputTypes lexicalContext finalContext reason}
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (fault : FunctionStatementsFault program lexicalContext evidence
          bodyInstance.source environment bound roots finalContext reason after) :
        BodyFaults program bodyInstance evidence before arguments reason after
    | controlEscape
        {bodyInstance evidence before bound after arguments environment roots outcome
          inputTypes lexicalContext finalContext}
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (escaped : (∃ escapedEnvironment, outcome = .breaking escapedEnvironment) ∨
          (∃ escapedEnvironment, outcome = .continuing escapedEnvironment)) :
        BodyFaults program bodyInstance evidence before arguments
          .controlEscapedFunction after

  /-- Fault while executing one statement occurrence.  A generalized local
  reports an explicit unsupported-runtime fault before its initializer is
  evaluated; initializer faults therefore propagate only for monomorphic
  locals. -/
  inductive StatementFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → StatementId → SemanticFault → Heap → Prop where
    | missing
        {context evidence source environment heap id}
        (absent : StatementMissing source id) :
        StatementFaults program context evidence source environment heap id
          (.missingStatement id) heap
    | polymorphicLet
        {context evidence source environment heap id node binder initializer}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder initializer)
        (polymorphic : binder.scheme.quantified ≠ []) :
        StatementFaults program context evidence source environment heap id
          (.unsupportedPolymorphicBinder binder.id) heap
    | letInitializer
        {context evidence source environment before after id node binder initializer
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (monomorphic : binder.scheme.quantified = [])
        (fault : ExpressionFaults program context evidence source environment
          before initializer reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | returnValue
        {context evidence source environment before after id node expression reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some expression))
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | expression
        {context evidence source environment before after id node expression
          semicolon reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression semicolon)
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | assignValue
        {context evidence source environment before after id node assignment
          operator rhs reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator rhs)
        (fault : SourcePlaceAssignmentFaults program context evidence source
          environment before assignment.target operator rhs reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | assignBitNot
        {context evidence source environment before after id node assignment reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (fault : SourcePlaceBitNotFaults program context evidence source environment
          before assignment.target reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | ifCondition
        {context evidence source environment before after id node condition thenBody
          elseBody reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (fault : ExpressionFaults program context evidence source environment
          before condition reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | ifConditionType
        {context evidence source environment before after id node condition thenBody
          elseBody value actual}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (evaluate : ExpressionEvaluates program context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        StatementFaults program context evidence source environment before id
          (.typeMismatch .bool actual) after
    | ifTrueBody
        {context evidence source environment before middle after id node condition
          thenBody elseBody finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (evaluate : ExpressionEvaluates program context evidence source environment
          before condition (.bool true) middle)
        (fault : StatementsFault program context evidence source environment middle
          thenBody finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | ifFalseBody
        {context evidence source environment before middle after id node condition
          thenBody body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some body))
        (evaluate : ExpressionEvaluates program context evidence source environment
          before condition (.bool false) middle)
        (fault : StatementsFault program context evidence source environment middle
          body finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | block
        {context evidence source environment before after id node body finalContext
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (fault : StatementsFault program context evidence source environment before
          body finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | matchScrutinee
        {context evidence source environment before after id node resolution reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (fault : ExpressionFaults program context evidence source environment
          before resolution.scrutinee reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | matchPattern
        {context evidence source environment before scrutineeHeap hiddenHeap id node
          resolution scrutinee scrutineeNode location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (fault : MatchCasesPatternFault context scrutinee resolution.cases) :
        StatementFaults program context evidence source environment before id
          .invalidPattern hiddenHeap
    | matchArmBody
        {context evidence source environment before scrutineeHeap hiddenHeap after id
          node resolution scrutinee scrutineeNode location armBody bindings binders
          values armContext armEnvironment bound finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.arm armBody bindings))
        (binders_eq : binders = bindings.map Prod.fst)
        (values_eq : values = bindings.map Prod.snd)
        (binders_extend : BindersExtend source.owner context binders armContext)
        (allocate_bindings : BindersAllocate environment hiddenHeap binders values
          armEnvironment bound)
        (fault : StatementsFault program armContext evidence source armEnvironment
          bound armBody finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | matchDefaultBody
        {context evidence source environment before scrutineeHeap hiddenHeap after id
          node resolution scrutinee scrutineeNode location body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.default body))
        (fault : StatementsFault program context evidence source environment
          hiddenHeap body finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | forInitializer
        {context evidence source environment before after id node initializer
          condition post body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (fault : ForItemsFault program context evidence source environment before
          initializer finalContext reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | forIteration
        {context evidence source environment before initialized after id node
          initializer condition post body loopContext loopEnvironment reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializer_executes : ForItemsExecute program context evidence source
          environment before initializer loopContext loopEnvironment initialized)
        (fault : ForLoopFaults program loopContext evidence source loopEnvironment
          initialized condition post body reason after) :
        StatementFaults program context evidence source environment before id
          reason after
    | whileIteration
        {context evidence source environment before after id node condition body
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (fault : WhileFaults program context evidence source environment before
          condition body reason after) :
        StatementFaults program context evidence source environment before id
          reason after

  /-- First fault in ordinary statement sequencing. -/
  inductive StatementsFault (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List StatementId → Context → SemanticFault → Heap → Prop where
    | head
        {context evidence source environment before after statement statements reason}
        (fault : StatementFaults program context evidence source environment before
          statement reason after) :
        StatementsFault program context evidence source environment before
          (statement :: statements) context reason after
    | tail
        {context middleContext finalContext evidence source environment before
          middle after statement statements nextEnvironment reason}
        (head : StatementExecutes program context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (fault : StatementsFault program middleContext evidence source
          nextEnvironment middle statements finalContext reason after) :
        StatementsFault program context evidence source environment before
          (statement :: statements) finalContext reason after

  /-- First fault in function sequencing, including a final expression. -/
  inductive FunctionStatementsFault (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List StatementId → Context → SemanticFault → Heap → Prop where
    | singleton
        {context evidence source environment before after statement reason}
        (fault : StatementFaults program context evidence source environment before
          statement reason after) :
        FunctionStatementsFault program context evidence source environment before
          [statement] context reason after
    | tailExpression
        {context evidence source environment before after statement node expression
          reason}
        (contains : ContainsStatement source statement node)
        (form_eq : node.form = .expression expression false)
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        FunctionStatementsFault program context evidence source environment before
          [statement] context reason after
    | head
        {context evidence source environment before after statement next rest reason}
        (fault : StatementFaults program context evidence source environment before
          statement reason after) :
        FunctionStatementsFault program context evidence source environment before
          (statement :: next :: rest) context reason after
    | tail
        {context middleContext finalContext evidence source environment before
          middle after statement next rest nextEnvironment reason}
        (head : StatementExecutes program context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (fault : FunctionStatementsFault program middleContext evidence source
          nextEnvironment middle (next :: rest) finalContext reason after) :
        FunctionStatementsFault program context evidence source environment before
          (statement :: next :: rest) finalContext reason after

  /-- Fault while evaluating place-index expressions or resolving the root. -/
  inductive SourcePlaceFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        PlaceResolution → SemanticFault → Heap → Prop where
    | unbound
        {context evidence source environment heap place}
        (missing : environment.Unbound place.root) :
        SourcePlaceFaults program context evidence source environment heap place
          (.unboundLocal place.root) heap
    | dangling
        {context evidence source environment heap place location}
        (lookup : Environment.LooksUp environment place.root location)
        (missing : heap.Dangling location) :
        SourcePlaceFaults program context evidence source environment heap place
          (.danglingLocation location) heap
    | projectionExpression
        {context evidence source environment before after place location cell reason}
        (lookup : Environment.LooksUp environment place.root location)
        (read : Heap.Reads before location cell)
        (fault : SourceProjectionsFault program context evidence source environment
          before place.projections reason after) :
        SourcePlaceFaults program context evidence source environment before place
          reason after
    | danglingAfterProjections
        {context evidence source environment before after place location cell
          evaluated}
        (lookup : Environment.LooksUp environment place.root location)
        (read : Heap.Reads before location cell)
        (evaluate : SourceProjectionsEvaluate program context evidence source
          environment before place.projections evaluated after)
        (missing : after.Dangling location) :
        SourcePlaceFaults program context evidence source environment before place
          (.danglingLocation location) after
    | uninitialized
        {context evidence source environment before after place location initialCell
          currentCell evaluated}
        (lookup : Environment.LooksUp environment place.root location)
        (initial_read : Heap.Reads before location initialCell)
        (evaluate : SourceProjectionsEvaluate program context evidence source
          environment before place.projections evaluated after)
        (current_read : Heap.Reads after location currentCell)
        (empty : currentCell.value = none)
        (not_mapping : ¬ ∃ keyType valueType,
          currentCell.type = .mapping keyType valueType)
        (has_projection : evaluated ≠ []) :
        SourcePlaceFaults program context evidence source environment before place
          (.uninitializedLocation location) after

  /-- First fault in left-to-right place projection evaluation. -/
  inductive SourceProjectionsFault (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        List PlaceProjection → SemanticFault → Heap → Prop where
    | indexHead
        {context evidence source environment before after expression projections
          reason}
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        SourceProjectionsFault program context evidence source environment before
          (.index expression :: projections) reason after
    | indexTail
        {context evidence source environment before middle after expression key
          projections reason}
        (head : ExpressionEvaluates program context evidence source environment
          before expression key middle)
        (fault : SourceProjectionsFault program context evidence source environment
          middle projections reason after) :
        SourceProjectionsFault program context evidence source environment before
          (.index expression :: projections) reason after
    | memberTail
        {context evidence source environment before after name index projections
          reason}
        (fault : SourceProjectionsFault program context evidence source environment
          before projections reason after) :
        SourceProjectionsFault program context evidence source environment before
          (.member name index :: projections) reason after

  /-- Fault in target-before-RHS assignment, preserving prefix effects. -/
  inductive SourcePlaceAssignmentFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        PlaceResolution → Syntax.ValueAssignOp → ExpressionId → SemanticFault →
        Heap → Prop where
    | target
        {context evidence source environment before after place operator rhs reason}
        (fault : SourcePlaceFaults program context evidence source environment
          before place reason after) :
        SourcePlaceAssignmentFaults program context evidence source environment
          before place operator rhs reason after
    | rhs
        {context evidence source environment before targetHeap after place operator
          rhs target reason}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target targetHeap)
        (fault : ExpressionFaults program context evidence source environment
          targetHeap rhs reason after) :
        SourcePlaceAssignmentFaults program context evidence source environment
          before place operator rhs reason after
    | operands
        {context evidence source environment before targetHeap rhsHeap place operator
          rhs target right}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target targetHeap)
        (evaluate : ExpressionEvaluates program context evidence source environment
          targetHeap rhs right rhsHeap)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        SourcePlaceAssignmentFaults program context evidence source environment
          before place operator rhs (.invalidAssignmentOperands operator) rhsHeap

  /-- Fault in snapshot-only bit-not assignment. -/
  inductive SourcePlaceBitNotFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        PlaceResolution → SemanticFault → Heap → Prop where
    | target
        {context evidence source environment before after place reason}
        (fault : SourcePlaceFaults program context evidence source environment
          before place reason after) :
        SourcePlaceBitNotFaults program context evidence source environment before
          place reason after
    | uninitialized
        {context evidence source environment before after place target}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target after)
        (empty : target.selected = none) :
        SourcePlaceBitNotFaults program context evidence source environment before
          place (.invalidUnaryOperand .bitNot) after
    | operand
        {context evidence source environment before after place target value}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target after)
        (selected : target.selected = some value)
        (invalid : UnaryPrimitiveOperandInvalid .bitNot value) :
        SourcePlaceBitNotFaults program context evidence source environment before
          place (.invalidUnaryOperand .bitNot) after

  /-- Fault in one canonical `for` header item, including the explicit
  generalized-local runtime boundary. -/
  inductive ForItemFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        ForItemForm → SemanticFault → Heap → Prop where
    | polymorphicLet
        {context evidence source environment heap binder initializer}
        (polymorphic : binder.scheme.quantified ≠ []) :
        ForItemFaults program context evidence source environment heap
          (.letDecl binder initializer)
          (.unsupportedPolymorphicBinder binder.id) heap
    | letInitializer
        {context evidence source environment before after binder initializer reason}
        (monomorphic : binder.scheme.quantified = [])
        (fault : ExpressionFaults program context evidence source environment
          before initializer reason after) :
        ForItemFaults program context evidence source environment before
          (.letDecl binder (some initializer)) reason after
    | expression
        {context evidence source environment before after expression reason}
        (fault : ExpressionFaults program context evidence source environment
          before expression reason after) :
        ForItemFaults program context evidence source environment before
          (.expression expression) reason after
    | assignValue
        {context evidence source environment before after assignment operator rhs
          reason}
        (fault : SourcePlaceAssignmentFaults program context evidence source
          environment before assignment.target operator rhs reason after) :
        ForItemFaults program context evidence source environment before
          (.assignValue assignment operator rhs) reason after
    | assignBitNot
        {context evidence source environment before after assignment reason}
        (fault : SourcePlaceBitNotFaults program context evidence source environment
          before assignment.target reason after) :
        ForItemFaults program context evidence source environment before
          (.assignBitNot assignment) reason after

  /-- First fault in a canonical `for` header vector. -/
  inductive ForItemsFault (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        List ForItemForm → Context → SemanticFault → Heap → Prop where
    | head
        {context evidence source environment before after item items reason}
        (fault : ForItemFaults program context evidence source environment before
          item reason after) :
        ForItemsFault program context evidence source environment before
          (item :: items) context reason after
    | tail
        {context middleContext finalContext evidence source environment before
          middle after item items nextEnvironment reason}
        (head : ForItemExecutes program context evidence source environment before
          item middleContext nextEnvironment middle)
        (fault : ForItemsFault program middleContext evidence source nextEnvironment
          middle items finalContext reason after) :
        ForItemsFault program context evidence source environment before
          (item :: items) finalContext reason after

  /-- Fault during fuel-free while iteration. -/
  inductive WhileFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        ExpressionId → List StatementId → SemanticFault → Heap → Prop where
    | condition
        {context evidence source environment before after condition body reason}
        (fault : ExpressionFaults program context evidence source environment
          before condition reason after) :
        WhileFaults program context evidence source environment before condition
          body reason after
    | conditionType
        {context evidence source environment before after condition body value actual}
        (evaluate : ExpressionEvaluates program context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        WhileFaults program context evidence source environment before condition
          body (.typeMismatch .bool actual) after
    | body
        {context evidence source environment before conditionHeap after condition
          body finalContext reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (fault : StatementsFault program context evidence source environment
          conditionHeap body finalContext reason after) :
        WhileFaults program context evidence source environment before condition
          body reason after
    | nextFallthrough
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (fault : WhileFaults program context evidence source environment bodyHeap
          condition body reason after) :
        WhileFaults program context evidence source environment before condition
          body reason after
    | nextContinue
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (fault : WhileFaults program context evidence source environment bodyHeap
          condition body reason after) :
        WhileFaults program context evidence source environment before condition
          body reason after

  /-- Fault during the iterative portion of a canonical `for` loop. -/
  inductive ForLoopFaults (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        ExpressionId → List ForItemForm → List StatementId → SemanticFault →
        Heap → Prop where
    | condition
        {context evidence source environment before after condition post body reason}
        (fault : ExpressionFaults program context evidence source environment
          before condition reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after
    | conditionType
        {context evidence source environment before after condition post body value
          actual}
        (evaluate : ExpressionEvaluates program context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        ForLoopFaults program context evidence source environment before condition
          post body (.typeMismatch .bool actual) after
    | body
        {context evidence source environment before conditionHeap after condition
          post body finalContext reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (fault : StatementsFault program context evidence source environment
          conditionHeap body finalContext reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after
    | postFallthrough
        {context evidence source environment before conditionHeap bodyHeap after
          condition post body bodyFinalContext bodyEnvironment finalContext reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (fault : ForItemsFault program context evidence source environment bodyHeap
          post finalContext reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after
    | postContinue
        {context evidence source environment before conditionHeap bodyHeap after
          condition post body bodyFinalContext bodyEnvironment finalContext reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (fault : ForItemsFault program context evidence source environment bodyHeap
          post finalContext reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after
    | nextFallthrough
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (fault : ForLoopFaults program context evidence source environment postHeap
          condition post body reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after
    | nextContinue
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (fault : ForLoopFaults program context evidence source environment postHeap
          condition post body reason after) :
        ForLoopFaults program context evidence source environment before condition
          post body reason after

end

/-! ## Public outcome closures -/

/-- The disjoint tagged closure of successful and faulting expression steps. -/
inductive ExpressionEvaluatesOutcome (program : Program) :
    Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → ExpressionOutcome → Heap → Prop where
  | value
      {context evidence source environment before after id result}
      (evaluates : ExpressionEvaluates program context evidence source environment
        before id result after) :
      ExpressionEvaluatesOutcome program context evidence source environment before
        id (.value result) after
  | fault
      {context evidence source environment before after id reason}
      (faults : ExpressionFaults program context evidence source environment before
        id reason after) :
      ExpressionEvaluatesOutcome program context evidence source environment before
        id (.fault reason) after

/-- At the Core-representable residualization boundary, a successful
mathematical source value must additionally be materializable. Keeping this
phase explicit prevents rejection here from being confused with a fault in
ordinary source evaluation. -/
inductive RuntimeExpressionEvaluatesOutcome (program : Program) :
    Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → ExpressionOutcome → Heap → Prop where
  | value
      {context evidence source environment before after id result}
      (evaluates : ExpressionEvaluates program context evidence source environment
        before id result after)
      (accepted : RuntimeBoundaryAccepts result) :
      RuntimeExpressionEvaluatesOutcome program context evidence source environment
        before id (.value result) after
  | semanticFault
      {context evidence source environment before after id reason}
      (faults : ExpressionFaults program context evidence source environment before
        id reason after) :
      RuntimeExpressionEvaluatesOutcome program context evidence source environment
        before id (.fault reason) after
  | stagingViolation
      {context evidence source environment before after id result}
      (evaluates : ExpressionEvaluates program context evidence source environment
        before id result after)
      (rejected : RuntimeBoundaryRejects result) :
      RuntimeExpressionEvaluatesOutcome program context evidence source environment
        before id (.fault .stagingViolation) after

/-- One statement either follows the existing control semantics or faults. -/
inductive StatementExecutesOutcome (program : Program) :
    Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      StatementId → Context → ControlOutcome → Heap → Prop where
  | control
      {context finalContext evidence source environment before after id outcome}
      (executes : StatementExecutes program context evidence source environment
        before id finalContext outcome after) :
      StatementExecutesOutcome program context evidence source environment before id
        finalContext outcome after
  | fault
      {context evidence source environment before after id reason}
      (faults : StatementFaults program context evidence source environment before
        id reason after) :
      StatementExecutesOutcome program context evidence source environment before id
        context (.fault reason) after

/-- A statement sequence exposes `ControlOutcome.fault` at the exact prefix. -/
inductive StatementsExecuteOutcome (program : Program) :
    Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      List StatementId → Context → ControlOutcome → Heap → Prop where
  | control
      {context finalContext evidence source environment before after statements
        outcome}
      (executes : StatementsExecute program context evidence source environment
        before statements finalContext outcome after) :
      StatementsExecuteOutcome program context evidence source environment before
        statements finalContext outcome after
  | fault
      {context finalContext evidence source environment before after statements
        reason}
      (faults : StatementsFault program context evidence source environment before
        statements finalContext reason after) :
      StatementsExecuteOutcome program context evidence source environment before
        statements finalContext (.fault reason) after

/-- Function sequencing similarly reifies fault control. -/
inductive FunctionStatementsExecuteOutcome (program : Program) :
    Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      List StatementId → Context → ControlOutcome → Heap → Prop where
  | control
      {context finalContext evidence source environment before after statements
        outcome}
      (executes : FunctionStatementsExecute program context evidence source
        environment before statements finalContext outcome after) :
      FunctionStatementsExecuteOutcome program context evidence source environment
        before statements finalContext outcome after
  | fault
      {context finalContext evidence source environment before after statements
        reason}
      (faults : FunctionStatementsFault program context evidence source environment
        before statements finalContext reason after) :
      FunctionStatementsExecuteOutcome program context evidence source environment
        before statements finalContext (.fault reason) after

namespace ExpressionEvaluatesOutcome

theorem contains_or_missing
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {outcome : ExpressionOutcome}
    (evaluation : ExpressionEvaluatesOutcome program context evidence source
      environment before id outcome after) :
    (∃ node, ContainsExpression source id node) ∨ ExpressionMissing source id := by
  cases evaluation with
  | value evaluates => exact .inl evaluates.contains
  | fault faults =>
      cases faults with
      | missing absent => exact .inr absent
      | form contains _ => exact .inl ⟨_, contains⟩
      | coercion contains _ _ => exact .inl ⟨_, contains⟩

end ExpressionEvaluatesOutcome

end Solcore.SourceSemantics.Dynamic
