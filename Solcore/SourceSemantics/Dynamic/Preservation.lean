import Solcore.SourceSemantics.Dynamic.Default
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Operators
import Solcore.SourceSemantics.TraitSubstitutionProperties

/-!
Type-preservation lemmas for the proof-facing source dynamics.

This module starts below whole-expression evaluation.  Each theorem relates a
declarative dynamic operation to the corresponding source type, without using
the executable runtime.  The final section records the invariants required of
the mutually recursive whole-language evaluation relation.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

private theorem exactSubstitution_eq_nil
    {substitution : Substitution}
    (exact : ExactSubstitution substitution []) :
    substitution = [] := by
  cases substitution with
  | nil => rfl
  | cons binding rest =>
      have member : binding.1 ∈ Substitution.domain (binding :: rest) := by
        simp [Substitution.domain]
      have impossible := (exact.mem_domain_iff binding.1).mp member
      simp at impossible

private theorem monomorphicInstance_eq_body
    {context : Context} {scheme : Scheme} {type : Ty}
    (monomorphic : scheme.quantified = [])
    (instantiates : SchemeInstantiatesAt context scheme type) :
    type = scheme.body := by
  cases instantiates with
  | intro scheme_well_formed substitution exact range_well_formed result =>
      rw [monomorphic] at exact
      have substitution_eq := exactSubstitution_eq_nil exact
      subst substitution
      have body_eq : scheme.body = type := by
        simpa only [SchemeInstantiates.empty_apply] using result
      exact body_eq.symm

private theorem cellAt_member
    {cells : List Cell} {index : Nat} {cell : Cell}
    (selected : Heap.CellAt cells index cell) :
    cell ∈ cells := by
  induction selected with
  | head => simp
  | tail _ inductionHypothesis => exact List.mem_cons_of_mem _ inductionHypothesis

namespace Heap.Reads

theorem member
    {heap : Heap} {location : Location} {cell : Cell}
    (read : Heap.Reads heap location cell) :
    cell ∈ heap.cells := by
  cases read with
  | intro selected => exact cellAt_member selected

end Heap.Reads

namespace LiteralConstructs

theorem hasType
    {context : Context} {heap : Heap} {source : Syntax.CoreLiteralValue}
    {value : Value} (construction : LiteralConstructs source value) :
    ValueHasType context heap value .word := by
  cases construction
  exact .word _

end LiteralConstructs

namespace ResolvedIntegerLiteralConstructs

theorem hasType
    {context : Context} {heap : Heap} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {value : Value}
    (construction :
      ResolvedIntegerLiteralConstructs context source resolution value) :
    ValueHasType context heap value resolution.targetType := by
  cases construction with
  | word => exact .word _
  | integer => exact .integer _

end ResolvedIntegerLiteralConstructs

/-- The primitive unary fragment of source operator typing. -/
inductive PrimitiveUnaryHasType :
    Syntax.UnaryOp -> Ty -> Ty -> Prop where
  | logicalNot : PrimitiveUnaryHasType .logicalNot .bool .bool
  | wordBitNot : PrimitiveUnaryHasType .bitNot .word .word
  | integerBitNot : PrimitiveUnaryHasType .bitNot .integer .integer

namespace PrimitiveUnaryHasType

theorem sourceTyping {context : Context} {operator : Syntax.UnaryOp}
    {operand result : Ty}
    (typing : PrimitiveUnaryHasType operator operand result) :
    UnaryOperatorHasType context operator operand result [] := by
  cases typing with
  | logicalNot => exact .logicalNot
  | wordBitNot => exact .wordBitNot
  | integerBitNot => exact .integerBitNot

end PrimitiveUnaryHasType

namespace UnaryPrimitiveApplies

theorem preserves
    {context : Context} {heap : Heap} {operator : Syntax.UnaryOp}
    {operand result : Value} {operandType resultType : Ty}
    (typing : PrimitiveUnaryHasType operator operandType resultType)
    (operand_typed : ValueHasType context heap operand operandType)
    (application : UnaryPrimitiveApplies operator operand result) :
    ValueHasType context heap result resultType := by
  cases typing <;> cases application <;> try { cases operand_typed }
  · exact .bool _
  · exact .word _
  · exact .integer _

theorem hasSourceTyping
    {context : Context} {heap : Heap} {operator : Syntax.UnaryOp}
    {operand result : Value}
    (application : UnaryPrimitiveApplies operator operand result) :
    exists operandType resultType,
      ValueHasType context heap operand operandType /\
      ValueHasType context heap result resultType /\
      UnaryOperatorHasType context operator operandType resultType [] := by
  cases application with
  | logicalNot value =>
      exact ⟨.bool, .bool, .bool value, .bool _, .logicalNot⟩
  | wordBitNot value =>
      exact ⟨.word, .word, .word value, .word _, .wordBitNot⟩
  | integerBitNot value =>
      exact ⟨.integer, .integer, .integer value, .integer _, .integerBitNot⟩

end UnaryPrimitiveApplies

/-- The primitive, non-trait subset of binary source operator typing. -/
inductive PrimitiveBinaryHasType :
    Syntax.BinaryOp -> Ty -> Ty -> Prop where
  | wordArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      PrimitiveBinaryHasType operator .word .word
  | integerArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      PrimitiveBinaryHasType operator .integer .integer
  | wordComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      PrimitiveBinaryHasType operator .word .bool
  | integerComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      PrimitiveBinaryHasType operator .integer .bool
  | booleanAnd : PrimitiveBinaryHasType .logicalAnd .bool .bool
  | booleanOr : PrimitiveBinaryHasType .logicalOr .bool .bool

namespace PrimitiveBinaryHasType

theorem sourceTyping {context : Context} {operator : Syntax.BinaryOp}
    {operand result : Ty}
    (typing : PrimitiveBinaryHasType operator operand result) :
    BinaryOperatorHasType context operator operand operand result [] := by
  cases typing with
  | wordArithmetic kind => exact .wordArithmetic kind
  | integerArithmetic kind => exact .integerArithmetic kind
  | wordComparison kind => exact .wordComparison kind
  | integerComparison kind => exact .integerComparison kind
  | booleanAnd => exact .booleanAnd
  | booleanOr => exact .booleanOr

end PrimitiveBinaryHasType

namespace BinaryPrimitiveApplies

/-- Primitive results preserve the exact primitive source profile.  Operand
typing is included because equality constructors intentionally accept any
comparable values, while the source primitive profile is narrower. -/
theorem preserves
    {context : Context} {heap : Heap} {operator : Syntax.BinaryOp}
    {left right result : Value} {operandType resultType : Ty}
    (typing : PrimitiveBinaryHasType operator operandType resultType)
    (left_typed : ValueHasType context heap left operandType)
    (right_typed : ValueHasType context heap right operandType)
    (application : BinaryPrimitiveApplies operator left right result) :
    ValueHasType context heap result resultType := by
  cases typing with
  | wordArithmetic kind =>
      cases kind <;> cases application <;>
        try { cases left_typed } <;> try { cases right_typed } <;>
        exact ValueHasType.word _
  | integerArithmetic kind =>
      cases kind <;> cases application <;>
        try { cases left_typed } <;> try { cases right_typed } <;>
        exact ValueHasType.integer _
  | wordComparison kind =>
      cases kind <;> cases application <;>
        try { cases left_typed } <;> try { cases right_typed } <;>
        exact ValueHasType.bool _
  | integerComparison kind =>
      cases kind <;> cases application <;>
        try { cases left_typed } <;> try { cases right_typed } <;>
        exact ValueHasType.bool _
  | booleanAnd =>
      cases application
      exact .bool _
  | booleanOr =>
      cases application
      exact .bool _

end BinaryPrimitiveApplies

namespace ShortCircuits

theorem preserves
    {context : Context} {heap : Heap} {operator : Syntax.BinaryOp}
    {left result : Value}
    (circuit : ShortCircuits operator left result) :
    ValueHasType context heap result .bool := by
  cases circuit <;> exact .bool _

end ShortCircuits

namespace BuiltinApplies

theorem preserves
    {context : Context} {heap : Heap} {function : BuiltinFunctionId}
    {arguments : List Value} {result : Value}
    (application : BuiltinApplies function arguments result) :
    ValuesHaveTypes context heap arguments function.parameterTypes /\
      ValueHasType context heap result function.returnType := by
  cases application <;>
    constructor <;>
    repeat' first | exact .nil | apply ValuesHaveTypes.cons | constructor

end BuiltinApplies

namespace AssignmentValueApplies

/-- Plain assignment returns its right-hand value at any source type. -/
theorem equalPreserves
    {context : Context} {heap : Heap} {current : Option Value}
    {right result : Value} {type : Ty}
    (right_typed : ValueHasType context heap right type)
    (applies : AssignmentValueApplies .equal current right result) :
    ValueHasType context heap result type := by
  cases applies
  exact right_typed

/-- Every currently supported compound assignment is a homogeneous Word
operation. -/
theorem wordCompoundPreserves
    {context : Context} {heap : Heap} {operator : Syntax.ValueAssignOp}
    {current : Option Value} {right result : Value}
    (kind : WordCompoundAssignmentOperator operator)
    (current_typed : OptionalValueHasType context heap current .word)
    (right_typed : ValueHasType context heap right .word)
    (applies : AssignmentValueApplies operator current right result) :
    ValueHasType context heap result .word := by
  cases kind with
  | add =>
      cases applies with
      | add primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .add) left_typed
                right_typed
  | subtract =>
      cases applies with
      | subtract primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .subtract) left_typed
                right_typed
  | multiply =>
      cases applies with
      | multiply primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .multiply) left_typed
                right_typed
  | divide =>
      cases applies with
      | divide primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .divide) left_typed
                right_typed
  | modulo =>
      cases applies with
      | modulo primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .modulo) left_typed
                right_typed
  | bitAnd =>
      cases applies with
      | bitAnd primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .bitAnd) left_typed
                right_typed
  | bitXor =>
      cases applies with
      | bitXor primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .bitXor) left_typed
                right_typed
  | bitOr =>
      cases applies with
      | bitOr primitive =>
          cases current_typed with
          | some left_typed =>
              exact primitive.preserves (.wordArithmetic .bitOr) left_typed
                right_typed

end AssignmentValueApplies

namespace BitNotSnapshot

theorem preserves
    {context : Context} {heap : Heap} {current : Option Value}
    {result : Value}
    (current_typed : OptionalValueHasType context heap current .word)
    (applies : BitNotSnapshot current result) :
    ValueHasType context heap result .word := by
  cases applies
  exact .word _

end BitNotSnapshot

namespace PrimitiveCoercionApplies

theorem preserves
    {context : Context} {heap : Heap} {step : CoercionStep}
    {input output : Value}
    (input_typed : ValueHasType context heap input step.source)
    (application : PrimitiveCoercionApplies step input output) :
    ValueHasType context heap output step.target := by
  cases application with
  | identity sameType => simpa [sameType] using input_typed
  | integerToWord value _ target_eq =>
      rw [target_eq]
      exact .word _
  | wordToInteger value _ target_eq =>
      rw [target_eq]
      exact .integer _

end PrimitiveCoercionApplies

namespace CoercionApplies

theorem preserves
    {context : Context} {heap : Heap} {step : CoercionStep}
    {input output : Value}
    (input_typed : ValueHasType context heap input step.source)
    (application : CoercionApplies context step input output) :
    ValueHasType context heap output step.target := by
  cases application with
  | intro _ primitive => exact primitive.preserves input_typed

end CoercionApplies

namespace CoercionPathApplies

theorem preserves
    {context : Context} {heap : Heap} {source target : Ty}
    {steps : List CoercionStep} {input output : Value}
    (valid : CoercionPathValid context source target steps)
    (input_typed : ValueHasType context heap input source)
    (application : CoercionPathApplies context steps input output) :
    ValueHasType context heap output target := by
  induction valid generalizing input output with
  | nil type =>
      cases application
      exact input_typed
  | cons head tail inductionHypothesis =>
      cases application with
      | cons applicationHead applicationTail =>
          exact inductionHypothesis
            (applicationHead.preserves input_typed) applicationTail

end CoercionPathApplies

namespace ValuesPack

theorem exists_pack (values : List Value) : exists packed, ValuesPack values packed := by
  cases values with
  | nil => exact ⟨.unit, .nil⟩
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, .singleton first⟩
      | cons second rest =>
          rcases exists_pack (second :: rest) with ⟨packed, tail⟩
          exact ⟨.product first packed, .cons tail⟩

theorem hasType
    {context : Context} {heap : Heap} {values : List Value}
    {types : List Ty} {packed : Value}
    (packing : ValuesPack values packed)
    (values_typed : ValuesHaveTypes context heap values types) :
    ValueHasType context heap packed (Ty.productMany types) := by
  induction packing generalizing types with
  | nil =>
      cases values_typed
      exact .unit
  | singleton value =>
      cases values_typed with
      | cons head tail =>
          cases tail
          exact head
  | cons tail inductionHypothesis =>
      cases values_typed with
      | cons first_typed remaining_typed =>
          cases remaining_typed with
          | cons second_typed rest_typed =>
              exact .product first_typed
                (inductionHypothesis (.cons second_typed rest_typed))

end ValuesPack

namespace MappingLookup

theorem preserves
    {context : Context} {heap : Heap} {key selected : Value}
    {entries : List (Value × Value)} {keyType valueType : Ty}
    (entries_typed :
      MappingEntriesHaveTypes context heap entries keyType valueType)
    (lookup : MappingLookup key entries selected) :
    ValueHasType context heap selected valueType := by
  induction lookup with
  | head =>
      cases entries_typed with
      | cons _ value_typed _ => exact value_typed
  | tail _ _ inductionHypothesis =>
      cases entries_typed with
      | cons _ _ tail_typed => exact inductionHypothesis tail_typed

end MappingLookup

namespace MappingUpdate

theorem preserves
    {context : Context} {heap : Heap} {key value : Value}
    {entries updated : List (Value × Value)} {keyType valueType : Ty}
    (key_typed : ValueHasType context heap key keyType)
    (value_typed : ValueHasType context heap value valueType)
    (entries_typed :
      MappingEntriesHaveTypes context heap entries keyType valueType)
    (update : MappingUpdate key value entries updated) :
    MappingEntriesHaveTypes context heap updated keyType valueType := by
  induction update with
  | head =>
      cases entries_typed with
      | cons _ _ tail_typed => exact .cons key_typed value_typed tail_typed
  | tail _ _ inductionHypothesis =>
      cases entries_typed with
      | cons storedKey_typed storedValue_typed tail_typed =>
          exact .cons storedKey_typed storedValue_typed
            (inductionHypothesis tail_typed)

end MappingUpdate

namespace MappingInsert

theorem preserves
    {context : Context} {heap : Heap} {key value : Value}
    {entries updated : List (Value × Value)} {keyType valueType : Ty}
    (key_typed : ValueHasType context heap key keyType)
    (value_typed : ValueHasType context heap value valueType)
    (entries_typed :
      MappingEntriesHaveTypes context heap entries keyType valueType)
    (insertion : MappingInsert key value entries updated) :
    MappingEntriesHaveTypes context heap updated keyType valueType := by
  cases insertion with
  | update replacement =>
      exact replacement.preserves key_typed value_typed entries_typed
  | append absent =>
      induction entries with
      | nil =>
          cases entries_typed
          exact .cons key_typed value_typed (.nil keyType valueType)
      | cons entry entries inductionHypothesis =>
          cases entries_typed with
          | cons storedKey_typed storedValue_typed tail_typed =>
              cases absent with
              | cons _ rest_absent =>
                  exact .cons storedKey_typed storedValue_typed
                    (inductionHypothesis tail_typed rest_absent)

end MappingInsert

namespace ValueAt

theorem preserves
    {context : Context} {heap : Heap} {values : List Value}
    {types : List Ty} {index : Nat} {value : Value} {type : Ty}
    (values_typed : ValuesHaveTypes context heap values types)
    (selected : ValueAt values index value)
    (type_at : types[index]? = some type) :
    ValueHasType context heap value type := by
  induction selected generalizing types type with
  | head =>
      cases values_typed with
      | cons head _ =>
          simp at type_at
          subst type
          exact head
  | tail _ inductionHypothesis =>
      cases values_typed with
      | cons _ tail_typed =>
          simp only [List.getElem?_cons_succ] at type_at
          exact inductionHypothesis tail_typed type_at

end ValueAt

namespace ValuesReplaceAt

theorem preserves
    {context : Context} {heap : Heap} {values updated : List Value}
    {types : List Ty} {index : Nat} {replacement : Value} {type : Ty}
    (values_typed : ValuesHaveTypes context heap values types)
    (type_at : types[index]? = some type)
    (replacement_typed : ValueHasType context heap replacement type)
    (replaced : ValuesReplaceAt values index replacement updated) :
    ValuesHaveTypes context heap updated types := by
  induction replaced generalizing types type with
  | head =>
      cases values_typed with
      | cons _ tail_typed =>
          simp at type_at
          subst type
          exact .cons replacement_typed tail_typed
  | tail _ inductionHypothesis =>
      cases values_typed with
      | cons head_typed tail_typed =>
          simp only [List.getElem?_cons_succ] at type_at
          exact .cons head_typed
            (inductionHypothesis tail_typed type_at replacement_typed)

end ValuesReplaceAt

namespace DefaultValue

theorem preserves
    {context : Context} {heap : Heap} {type : Ty} {value : Value}
    (defaulted : DefaultValue type value) :
    ValueHasType context heap value type :=
  defaulted.hasType

end DefaultValue

namespace RequirementsProduceEnvironment

/-- Producing exactly the assumptions of a lexical context yields a closed,
complete runtime evidence environment for that context. -/
theorem covers
    {context : Context} {caller : EvidenceEnvironment}
    {requirements : List RequirementId} {predicates : List ProgramPredicate}
    {environment : EvidenceEnvironment}
    (produces : RequirementsProduceEnvironment context caller requirements
      predicates environment)
    (predicates_eq : predicates = context.assumptions) :
    environment.Covers context := by
  constructor
  · exact produces.valid
  · intro predicate member
    apply produces.supplies predicate
    simpa [predicates_eq] using member

end RequirementsProduceEnvironment

namespace Binds

/-- Allocating one lexical binding realizes the corresponding static context
extension in the runtime environment. -/
theorem preservesEnvironmentAgreement
    {owner : Resolved.DeclarationId} {context finalContext : Context}
    {binder : TypedBinder} {environment finalEnvironment : Environment}
    {before after : Heap} {value : Option Value}
    (extension : BinderExtends owner context binder finalContext)
    (monomorphic : binder.scheme.quantified = [])
    (agrees : EnvironmentAgrees before context.locals environment)
    (bound : Binds environment before binder.id binder.scheme.body value
      finalEnvironment after) :
    EnvironmentAgrees after finalContext.locals finalEnvironment := by
  cases extension with
  | intro wellFormed fresh =>
      cases bound with
      | intro allocation =>
          exact .cons allocation.reads_new rfl (.ordinary monomorphic rfl)
            (agrees.mono (HeapTypesExtend.of_allocation allocation))

end Binds

namespace BindingsBind

theorem preservesHeapTyping
    {context : Context} {environment finalEnvironment : Environment}
    {before after : Heap} {bindings : List (TypedBinder × Value)}
    (before_typed : HeapWellTyped context before)
    (bindings_typed : BindingValuesHaveTypes context before bindings)
    (bound : BindingsBind environment before bindings finalEnvironment after) :
    HeapWellTyped context after :=
  before_typed.bind bindings_typed bound

theorem extendsHeapTypes
    {environment finalEnvironment : Environment}
    {before after : Heap} {bindings : List (TypedBinder × Value)}
    (bound : BindingsBind environment before bindings finalEnvironment after) :
    HeapTypesExtend before after := by
  induction bound with
  | nil => exact .refl _
  | cons head _ inductionHypothesis =>
      cases head with
      | intro allocation =>
          exact (HeapTypesExtend.of_allocation allocation).trans
            inductionHypothesis

/-- A source-ordered vector of dynamic bindings realizes the matching static
sequence of context extensions. -/
theorem preservesEnvironmentAgreement
    {owner : Resolved.DeclarationId} {context finalContext : Context}
    {environment finalEnvironment : Environment}
    {before after : Heap} {bindings : List (TypedBinder × Value)}
    (extension : BindersExtend owner context (bindings.map Prod.fst)
      finalContext)
    (monomorphic : forall binding, binding ∈ bindings ->
      binding.1.scheme.quantified = [])
    (agrees : EnvironmentAgrees before context.locals environment)
    (bound : BindingsBind environment before bindings finalEnvironment after) :
    EnvironmentAgrees after finalContext.locals finalEnvironment := by
  induction bound generalizing context finalContext with
  | nil =>
      cases extension
      exact agrees
  | cons head tail inductionHypothesis =>
      cases extension with
      | cons headExtension tailExtension =>
          exact inductionHypothesis tailExtension
            (fun binding member => monomorphic binding (by simp [member]))
            (head.preservesEnvironmentAgreement headExtension
              (monomorphic _ (by simp)) agrees)

end BindingsBind

namespace BindingValuesHaveTypes

theorem unzip
    {context : Context} {heap : Heap}
    {bindings : List (TypedBinder × Value)}
    (typed : BindingValuesHaveTypes context heap bindings) :
    ValuesHaveTypes context heap (bindings.map Prod.snd)
      (bindings.map fun binding => binding.1.scheme.body) := by
  induction typed with
  | nil => exact .nil
  | cons head tail induction => exact .cons head induction

theorem append
    {context : Context} {heap : Heap}
    {left right : List (TypedBinder × Value)}
    (left_typed : BindingValuesHaveTypes context heap left)
    (right_typed : BindingValuesHaveTypes context heap right) :
    BindingValuesHaveTypes context heap (left ++ right) := by
  induction left_typed with
  | nil => exact right_typed
  | cons head _ inductionHypothesis =>
      exact .cons head inductionHypothesis

end BindingValuesHaveTypes

private theorem foldlApplication_ne_comptime
    (head : Ty) (arguments : List Ty)
    (head_ne : forall inner, head ≠ .comptime inner) (inner : Ty) :
    arguments.foldl Ty.application head ≠ .comptime inner := by
  induction arguments generalizing head with
  | nil => exact head_ne inner
  | cons argument arguments inductionHypothesis =>
      exact inductionHypothesis (.application head argument)
        (by intro candidate equality; cases equality)

private theorem nominal_ne_comptime
    (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  apply foldlApplication_ne_comptime
  intro candidate equality
  cases equality

namespace ValueHasType

theorem mappingComponents
    {context : Context} {heap : Heap}
    {keyType valueType expectedKey expectedValue : Ty}
    {entries : List (Value × Value)}
    (typed : ValueHasType context heap (.mapping keyType valueType entries)
      (.mapping expectedKey expectedValue)) :
    keyType = expectedKey /\ valueType = expectedValue /\
      MappingEntriesHaveTypes context heap entries expectedKey expectedValue := by
  cases typed with
  | mapping entries_typed => exact ⟨rfl, rfl, entries_typed⟩

/-- Catalog validity rules out confusing a nominal constructor result with a
staging wrapper, so constructor payload typing can be recovered exactly. -/
theorem constructedPayloads
    {context : Context} {heap : Heap}
    {instantiation : DataConstructorInstantiation} {arguments : List Value}
    (valid : DataConstructorInstantiation.Valid context instantiation)
    (typed : ValueHasType context heap
      (.constructed instantiation arguments) instantiation.resultType) :
    ValuesHaveTypes context heap arguments instantiation.payloadTypes := by
  rcases typed.constructed_inv with ordinary | staged
  · exact ordinary.2.2
  · rcases staged with ⟨inner, result_eq, _⟩
    cases valid with
    | intro dataType signature dataType_mem signature_mem signature_owner
        constructor_eq substitution_exact substitution_range payloadTypes_eq resultType_eq =>
        have impossible :
            Ty.nominal dataType.id
              (ParameterSubstitution.orderedArguments
                instantiation.parameterSubstitution dataType.parameters) =
              .comptime inner := by
          exact resultType_eq.symm.trans result_eq
        exact (nominal_ne_comptime _ _ _ impossible).elim

/-- Pattern matching intentionally ignores association-list order in rigid
parameter substitutions.  Exact payload/result agreement is sufficient to
recover the statically expected payload typing. -/
theorem constructedPayloadsOfAgreement
    {context : Context} {heap : Heap}
    {actual expected : DataConstructorInstantiation} {arguments : List Value}
    (valid : DataConstructorInstantiation.Admissible context expected)
    (agreement : ConstructorInstantiationsAgree actual expected)
    (typed : ValueHasType context heap (.constructed actual arguments)
      expected.resultType) :
    ValuesHaveTypes context heap arguments expected.payloadTypes := by
  rcases typed.constructed_inv with ordinary | staged
  · simpa [agreement.payload_types_eq] using ordinary.2.2
  · rcases staged with ⟨inner, result_eq, _⟩
    cases valid with
    | intro dataType signature dataType_mem signature_mem signature_owner
        constructor_eq substitution_exact substitution_range payloadTypes_eq
        resultType_eq =>
        have impossible :
            Ty.nominal dataType.id
              (ParameterSubstitution.orderedArguments
                expected.parameterSubstitution dataType.parameters) =
              .comptime inner := by
          exact resultType_eq.symm.trans result_eq
        exact (nominal_ne_comptime _ _ _ impossible).elim

end ValueHasType

namespace ValuesPack

/-- A typed packed value and a matching arity recover pointwise element
typing.  The singleton case also covers a staging-wrapped element. -/
theorem unpackTypes
    {context : Context} {heap : Heap} {values : List Value}
    {types : List Ty} {packed : Value}
    (packing : ValuesPack values packed)
    (packed_typed : ValueHasType context heap packed (Ty.productMany types))
    (same_length : values.length = types.length) :
    ValuesHaveTypes context heap values types := by
  induction packing generalizing types with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons type types => simp at same_length
  | singleton value =>
      cases types with
      | nil => simp at same_length
      | cons type types =>
          cases types with
          | nil => exact .cons packed_typed .nil
          | cons second rest => simp at same_length
  | @cons first second rest packed tail inductionHypothesis =>
      cases types with
      | nil => simp at same_length
      | cons firstType types =>
          cases types with
          | nil => simp at same_length
          | cons secondType restTypes =>
              rcases packed_typed.product_inv with
                ⟨first_typed, tail_typed⟩
              have tail_length :
                  (second :: rest).length =
                    (secondType :: restTypes).length := by
                simpa using Nat.succ.inj same_length
              exact .cons first_typed
                (inductionHypothesis tail_typed tail_length)

end ValuesPack

namespace MatchPatternSourceRepresents

theorem rootArity_unique
    {context : Context} {source : MatchPatternSource}
    {resolution : MatchPatternResolution} {left right : Nat}
    (left_represents :
      MatchPatternSourceRepresents context source resolution left)
    (right_represents :
      MatchPatternSourceRepresents context source resolution right) :
    left = right := by
  induction left_represents generalizing right with
  | wildcard => cases right_represents; rfl
  | integerLiteral => cases right_represents; rfl
  | binder => cases right_represents; rfl
  | constructor => cases right_represents; rfl
  | tuple => cases right_represents; rfl
  | group _ inductionHypothesis =>
      cases right_represents with
      | group inner => exact inductionHypothesis inner

end MatchPatternSourceRepresents

namespace PatternInstructionHasType

theorem rest_length_lt
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {type : Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionHasType context instructions type requirements
      binders rest) :
    rest.length < instructions.length := by
  refine PatternInstructionHasType.rec
    (motive_1 := fun instructions _ _ _ rest _ =>
      rest.length < instructions.length)
    (motive_2 := fun instructions _ _ _ rest _ =>
      rest.length ≤ instructions.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  all_goals intros
  all_goals try simp_all only [List.length_cons]
  all_goals omega

end PatternInstructionHasType

namespace PatternInstructionsHaveTypes

theorem rest_length_le
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {types : List Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionsHaveTypes context instructions types
      requirements binders rest) :
    rest.length ≤ instructions.length := by
  refine PatternInstructionsHaveTypes.rec
    (motive_1 := fun instructions _ _ _ rest _ =>
      rest.length < instructions.length)
    (motive_2 := fun instructions _ _ _ rest _ =>
      rest.length ≤ instructions.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  all_goals intros
  all_goals try simp_all only [List.length_cons]
  all_goals omega

end PatternInstructionsHaveTypes

set_option maxHeartbeats 800000 in
mutual

  theorem PatternInstructionMatches.preserves
      {context : Context} {heap : Heap} {value : Value}
      {instructions typedRest matchedRest : List MatchPatternInstruction}
      {type : Ty} {requirements : List RequirementId}
      {binders : List TypedBinder} {bindings : List (TypedBinder × Value)}
      (typing : PatternInstructionHasType context instructions type
        requirements binders typedRest)
      (value_typed : ValueHasType context heap value type)
      (matched : PatternInstructionMatches context value instructions
        bindings matchedRest) :
      matchedRest = typedRest /\
        BindingValuesHaveTypes context heap bindings /\
        bindings.map Prod.fst = binders := by
    cases typing with
    | wildcard =>
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | integerLiteral =>
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | binder valid =>
        cases matched
        refine ⟨rfl, .cons ?_ .nil, rfl⟩
        rw [valid.scheme_eq]
        exact value_typed
    | constructor valid arity arguments_typing =>
        cases matched with
        | constructor instantiations_agree dynamic_arity children =>
            exact PatternInstructionsMatch.preserves arguments_typing
              (value_typed.constructedPayloadsOfAgreement valid
                instantiations_agree) children
    | tuple arity elements_typing =>
        cases matched with
        | tuple packing dynamic_arity children =>
            have same_length := dynamic_arity.trans arity
            exact PatternInstructionsMatch.preserves elements_typing
              (packing.unpackTypes value_typed same_length) children
    termination_by instructions.length * 2
    decreasing_by
      all_goals simp_all
      all_goals omega

  theorem PatternInstructionsMatch.preserves
      {context : Context} {heap : Heap} {values : List Value}
      {instructions typedRest matchedRest : List MatchPatternInstruction}
      {types : List Ty} {requirements : List RequirementId}
      {binders : List TypedBinder} {bindings : List (TypedBinder × Value)}
      (typing : PatternInstructionsHaveTypes context instructions types
        requirements binders typedRest)
      (values_typed : ValuesHaveTypes context heap values types)
      (matched : PatternInstructionsMatch context values instructions
        bindings matchedRest) :
      matchedRest = typedRest /\
        BindingValuesHaveTypes context heap bindings /\
        bindings.map Prod.fst = binders := by
    cases typing with
    | nil =>
        cases values_typed
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | cons head_typing tail_typing =>
        cases values_typed with
        | cons head_value_typed tail_values_typed =>
            cases matched with
            | cons head_match tail_match =>
                rcases head_match.preserves head_typing head_value_typed with
                  ⟨middle_eq, head_bindings_typed, head_binders_eq⟩
                subst middle_eq
                rcases tail_match.preserves tail_typing tail_values_typed with
                  ⟨rest_eq, tail_bindings_typed, tail_binders_eq⟩
                refine ⟨rest_eq, head_bindings_typed.append tail_bindings_typed,
                  ?_⟩
                simp [head_binders_eq, tail_binders_eq]
    termination_by instructions.length * 2 + 1
    decreasing_by
      · omega
      · have shorter :=
          Solcore.SourceSemantics.Dynamic.PatternInstructionHasType.rest_length_lt
            head_typing
        omega

end

namespace PatternMatches

theorem preserves
    {context : Context} {heap : Heap} {pattern : TypedMatchPattern}
    {type : Ty} {binders : List TypedBinder} {rootArity : Nat}
    {value : Value} {bindings : List (TypedBinder × Value)}
    (typing :
      TypedMatchPatternHasType context pattern type binders rootArity)
    (value_typed : ValueHasType context heap value type)
    (matched : PatternMatches context pattern value bindings) :
    BindingValuesHaveTypes context heap bindings /\
      bindings.map Prod.fst = binders := by
  cases matched with
  | intro dynamic_source dynamic_match =>
      rename_i dynamicArity
      have arity_eq :=
        Solcore.SourceSemantics.Dynamic.MatchPatternSourceRepresents.rootArity_unique
          typing.source_represents dynamic_source
      subst dynamicArity
      rcases dynamic_match.preserves typing.resolution_type value_typed with
        ⟨_, bindings_typed, binders_eq⟩
      exact ⟨bindings_typed, binders_eq⟩

end PatternMatches

set_option maxHeartbeats 400000 in
mutual

  theorem PatternInstructionHasType.binders_monomorphic
      {context : Context} {instructions rest : List MatchPatternInstruction}
      {type : Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (typing : PatternInstructionHasType context instructions type requirements
        binders rest) :
      forall binder, binder ∈ binders -> binder.scheme.quantified = [] := by
    cases typing with
    | wildcard => simp
    | integerLiteral valid => simp
    | binder valid =>
        intro binder member
        simp only [List.mem_singleton] at member
        subst binder
        simp [valid.scheme_eq, TypeSystem.Scheme.mono]
    | constructor valid arity arguments =>
        exact
          Solcore.SourceSemantics.Dynamic.PatternInstructionsHaveTypes.binders_monomorphic
            arguments
    | tuple arity elements =>
        exact
          Solcore.SourceSemantics.Dynamic.PatternInstructionsHaveTypes.binders_monomorphic
            elements
  termination_by instructions.length * 2
  decreasing_by all_goals simp_all; all_goals omega

  theorem PatternInstructionsHaveTypes.binders_monomorphic
      {context : Context} {instructions rest : List MatchPatternInstruction}
      {types : List Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (typing : PatternInstructionsHaveTypes context instructions types
        requirements binders rest) :
      forall binder, binder ∈ binders -> binder.scheme.quantified = [] := by
    cases typing with
    | nil => simp
    | cons head tail =>
        intro binder member
        simp only [List.mem_append] at member
        exact member.elim
          (Solcore.SourceSemantics.Dynamic.PatternInstructionHasType.binders_monomorphic
            head binder)
          (Solcore.SourceSemantics.Dynamic.PatternInstructionsHaveTypes.binders_monomorphic
            tail binder)
  termination_by instructions.length * 2 + 1
  decreasing_by
    · simp_all
    · have shorter := PatternInstructionHasType.rest_length_lt head
      simp_all

end

namespace TypedMatchPatternHasType

theorem binders_monomorphic
    {context : Context} {pattern : TypedMatchPattern} {type : Ty}
    {binders : List TypedBinder} {rootArity : Nat}
    (typing : TypedMatchPatternHasType context pattern type binders rootArity) :
    forall binder, binder ∈ binders -> binder.scheme.quantified = [] :=
  Solcore.SourceSemantics.Dynamic.PatternInstructionHasType.binders_monomorphic
    typing.resolution_type

end TypedMatchPatternHasType

namespace MatchCasesSelect

theorem defaultBody_eq
    {context : Context} {value : Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {body : List StatementId}
    (selected : MatchCasesSelect context value cases fallback (.default body)) :
    fallback = some body := by
  induction cases generalizing fallback with
  | nil =>
      cases selected
      rfl
  | cons arm rest induction =>
      cases selected with
      | tail does_not_match selected => exact induction selected

theorem noBranch_defaultBody_eq
    {context : Context} {value : Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)}
    (selected : MatchCasesSelect context value cases fallback .noBranch) :
    fallback = none := by
  induction cases generalizing fallback with
  | nil =>
      cases selected
      rfl
  | cons arm rest induction =>
      cases selected with
      | tail does_not_match selected => exact induction selected

theorem armPreserves
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Value} {body : List StatementId}
    {bindings : List (TypedBinder × Value)} {heap : Heap}
    (cases_typed : MatchCasesHaveType source control context scrutineeType cases
      caseFacts)
    (value_typed : ValueHasType context heap value scrutineeType)
    (selected : MatchCasesSelect context value cases fallback
      (.arm body bindings)) :
    exists binders armContext finalContext facts,
      BindingValuesHaveTypes context heap bindings /\
        bindings.map Prod.fst = binders /\
        BindersExtend source.owner context binders armContext /\
        StatementsHaveType source control armContext body finalContext facts /\
        (forall binder, binder ∈ binders ->
          binder.scheme.quantified = []) := by
  cases selected with
  | head matched =>
      cases cases_typed with
      | cons head_type tail_type =>
          cases head_type with
          | intro pattern_type binders_extend body_type =>
              rcases matched.preserves pattern_type value_typed with
                ⟨bindings_typed, binders_eq⟩
              exact ⟨_, _, _, _, bindings_typed, binders_eq, binders_extend,
                body_type,
                Solcore.SourceSemantics.Dynamic.TypedMatchPatternHasType.binders_monomorphic
                  pattern_type⟩
  | tail does_not_match tail_selected =>
      cases cases_typed with
      | cons head_type tail_type =>
          exact MatchCasesSelect.armPreserves tail_type value_typed tail_selected
termination_by cases.length
decreasing_by simp_all

end MatchCasesSelect

namespace RootInitialValue

theorem preserves
    {context : Context} {heap : Heap} {cell : Cell}
    {initial : Option Value}
    (cell_typed : CellWellTyped context heap cell)
    (initial_value : RootInitialValue cell initial) :
    OptionalValueHasType context heap initial cell.type := by
  cases initial_value with
  | initialized => exact cell_typed.value
  | emptyMapping keyType valueType =>
      exact .some (.mapping (.nil keyType valueType))
  | uninitialized => exact .none _

end RootInitialValue

/-- The semantic payload invariant required by a positional member path.
The static catalog projection is retained separately below.  Keeping this
invariant explicit is necessary because a bare `Context` does not itself say
that declaration identities in its signature lists are unique. -/
structure MemberProjectionPreservesType
    (context : Context) (heap : Heap)
    (baseType : Ty) (index : Nat) (memberType : Ty) : Prop where
  read : forall instantiation arguments selected,
    ValueHasType context heap (.constructed instantiation arguments) baseType ->
    ValueAt arguments index selected ->
    ValueHasType context heap selected memberType
  update : forall instantiation arguments selected replacement updated,
    ValueHasType context heap (.constructed instantiation arguments) baseType ->
    ValueAt arguments index selected ->
    ValueHasType context heap replacement memberType ->
    ValuesReplaceAt arguments index replacement updated ->
    ValueHasType context heap (.constructed instantiation updated) baseType

namespace UniformMemberProjection

/-- The static uniform-member judgment now carries precisely the constructor
payload invariant needed by both reads and writes. -/
theorem preservesType
    {context : Context} {heap : Heap}
    {baseType memberType : Ty} {index : Nat}
    (projection : UniformMemberProjection context baseType index memberType) :
    MemberProjectionPreservesType context heap baseType index memberType := by
  have base_ne_comptime : forall inner, baseType ≠ .comptime inner := by
    intro inner equality
    cases projection with
    | intro dataType_mem substitution_exact base_eq base_well_formed
        member_well_formed constructors_nonempty member_uniform
        valid_instantiations =>
        exact nominal_ne_comptime _ _ _ (base_eq.symm.trans equality)
  constructor
  · intro instantiation arguments selected typed selected_at
    rcases typed.constructed_inv with ordinary | staged
    · rcases ordinary with ⟨result_eq, valid, arguments_typed⟩
      exact selected_at.preserves arguments_typed
        (projection.valid_payload valid result_eq.symm)
    · rcases staged with ⟨inner, result_eq, _⟩
      exact (base_ne_comptime inner result_eq).elim
  · intro instantiation arguments selected replacement updated typed selected_at
      replacement_typed replaced
    rcases typed.constructed_inv with ordinary | staged
    · rcases ordinary with ⟨result_eq, valid, arguments_typed⟩
      have updated_typed := replaced.preserves arguments_typed
        (projection.valid_payload valid result_eq.symm) replacement_typed
      have reconstructed : ValueHasType context heap
          (.constructed instantiation updated) instantiation.resultType :=
        .constructed valid updated_typed
      exact result_eq.symm ▸ reconstructed
    · rcases staged with ⟨inner, result_eq, _⟩
      exact (base_ne_comptime inner result_eq).elim

end UniformMemberProjection

/-- Type path for evaluated projections.  Index expressions have already run,
so an index carries its value typing.  A member retains both its static
catalog rule and the payload invariant supplied by a well-formed program. -/
inductive EvaluatedProjectionsHaveType (context : Context) (heap : Heap) :
    Ty -> List EvaluatedProjection -> Ty -> Prop where
  | nil (type : Ty) : EvaluatedProjectionsHaveType context heap type [] type
  | index
      {key : Value} {keyType valueType finalType : Ty}
      {rest : List EvaluatedProjection}
      (key_typed : ValueHasType context heap key keyType)
      (tail : EvaluatedProjectionsHaveType context heap valueType rest finalType) :
      EvaluatedProjectionsHaveType context heap (.mapping keyType valueType)
        (.index key :: rest) finalType
  | member
      {name : String} {index : Nat} {baseType memberType finalType : Ty}
      {rest : List EvaluatedProjection}
      (catalog : UniformMemberProjection context baseType index memberType)
      (payload : MemberProjectionPreservesType context heap baseType index
        memberType)
      (tail : EvaluatedProjectionsHaveType context heap memberType rest finalType) :
      EvaluatedProjectionsHaveType context heap baseType
        (.member name index :: rest) finalType

namespace EvaluatedProjectionsHaveType

theorem mono
    {context : Context} {before after : Heap}
    {sourceType finalType : Ty} {projections : List EvaluatedProjection}
    (extension : HeapTypesExtend before after)
    (typed : EvaluatedProjectionsHaveType context before sourceType projections
      finalType) :
    EvaluatedProjectionsHaveType context after sourceType projections finalType := by
  induction typed with
  | nil type => exact .nil type
  | index key_typed tail induction =>
      exact .index (key_typed.mono extension) induction
  | member catalog payload tail induction =>
      exact .member catalog
        (Solcore.SourceSemantics.Dynamic.UniformMemberProjection.preservesType
          catalog) induction

end EvaluatedProjectionsHaveType

/-- A leaf relation preserves one selected type, including absence before an
initializing assignment. -/
def LeafModificationPreservesType
    (context : Context) (heap : Heap)
    (Modify : Option Value -> Value -> Prop) (type : Ty) : Prop :=
  forall current updated,
    OptionalValueHasType context heap current type ->
    Modify current updated ->
    ValueHasType context heap updated type

namespace ProjectionsRead

theorem preserves
    {context : Context} {heap : Heap}
    {current result : Option Value} {projections : List EvaluatedProjection}
    {sourceType finalType : Ty}
    (path_typed : EvaluatedProjectionsHaveType context heap sourceType
      projections finalType)
    (current_typed : OptionalValueHasType context heap current sourceType)
    (read : ProjectionsRead current projections result) :
    OptionalValueHasType context heap result finalType := by
  induction path_typed generalizing current result with
  | nil =>
      cases read
      exact current_typed
  | index key_typed tail inductionHypothesis =>
      cases read with
      | indexFound lookup next =>
          cases current_typed with
          | some mapping_typed =>
              rcases mapping_typed.mappingComponents with
                ⟨rfl, rfl, entries_typed⟩
              exact inductionHypothesis
                (.some (lookup.preserves entries_typed)) next
      | indexDefault absent defaulted next =>
          cases current_typed with
          | some mapping_typed =>
              rcases mapping_typed.mappingComponents with ⟨rfl, rfl, _⟩
              exact inductionHypothesis (.some defaulted.hasType) next
  | member catalog payload tail inductionHypothesis =>
      cases read with
      | member selectedAt next =>
          cases current_typed with
          | some constructed_typed =>
              exact inductionHypothesis
                (.some (payload.read _ _ _ constructed_typed selectedAt)) next

end ProjectionsRead

namespace ProjectionsUpdate

theorem preserves
    {context : Context} {heap : Heap}
    {Modify : Option Value -> Value -> Prop}
    {current : Option Value} {projections : List EvaluatedProjection}
    {updated : Value} {sourceType finalType : Ty}
    (path_typed : EvaluatedProjectionsHaveType context heap sourceType
      projections finalType)
    (current_typed : OptionalValueHasType context heap current sourceType)
    (modify_typed :
      LeafModificationPreservesType context heap Modify finalType)
    (update : ProjectionsUpdate Modify current projections updated) :
    ValueHasType context heap updated sourceType := by
  induction path_typed generalizing current updated with
  | nil =>
      cases update with
      | leaf modified => exact modify_typed _ _ current_typed modified
  | index key_typed tail inductionHypothesis =>
      cases update with
      | indexFound lookup child insertion =>
          cases current_typed with
          | some mapping_typed =>
              rcases mapping_typed.mappingComponents with
                ⟨rfl, rfl, entries_typed⟩
              have selected_typed := lookup.preserves entries_typed
              have child_typed := inductionHypothesis (.some selected_typed)
                modify_typed child
              exact .mapping
                (insertion.preserves key_typed child_typed entries_typed)
      | indexDefault absent defaulted child insertion =>
          cases current_typed with
          | some mapping_typed =>
              rcases mapping_typed.mappingComponents with
                ⟨rfl, rfl, entries_typed⟩
              have child_typed := inductionHypothesis
                (.some defaulted.hasType) modify_typed child
              exact .mapping
                (insertion.preserves key_typed child_typed entries_typed)
  | member catalog payload tail inductionHypothesis =>
      cases update with
      | member selectedAt child replacement =>
          cases current_typed with
          | some constructed_typed =>
              have selected_typed :=
                payload.read _ _ _ constructed_typed selectedAt
              have child_typed := inductionHypothesis (.some selected_typed)
                modify_typed child
              exact payload.update _ _ _ _ _ constructed_typed selectedAt
                child_typed replacement

end ProjectionsUpdate

namespace ReplacesWith

theorem preservesType
    {context : Context} {heap : Heap} {replacement : Value} {type : Ty}
    (replacement_typed : ValueHasType context heap replacement type) :
    LeafModificationPreservesType context heap (ReplacesWith replacement)
      type := by
  intro current updated current_typed replaced
  cases replaced
  exact replacement_typed

end ReplacesWith

namespace ResolvedPlaceWrites

theorem preservesHeapTyping
    {context : Context} {Modify : Option Value -> Value -> Prop}
    {before after : Heap} {place : ResolvedPlace} {updatedRoot : Value}
    (before_typed : HeapWellTyped context before)
    (updated_typed : ValueHasType context before updatedRoot place.rootType)
    (written : ResolvedPlaceWrites Modify before place updatedRoot after) :
    HeapWellTyped context after := by
  cases written with
  | intro current_read root_type_eq initial_value update write =>
      apply before_typed.write current_read _ write
      apply OptionalValueHasType.some
      rw [root_type_eq]
      exact updated_typed

end ResolvedPlaceWrites

namespace BindersAllocate

theorem length_eq
    {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) : binders.length = values.length := by
  induction allocated with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem extendsHeapTypes
    {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) :
    HeapTypesExtend before after := by
  induction allocated with
  | nil => exact .refl _
  | cons allocation _ inductionHypothesis =>
      exact (HeapTypesExtend.of_allocation allocation).trans inductionHypothesis

theorem preservesHeapTyping
    {context : Context} {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (before_typed : HeapWellTyped context before)
    (values_typed : ValuesHaveTypes context before values
      (binders.map fun binder => binder.scheme.body))
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) :
    HeapWellTyped context after := by
  induction allocated generalizing context with
  | nil => exact before_typed
  | cons allocation tail inductionHypothesis =>
      cases values_typed with
      | cons value_typed remaining_typed =>
          have middle_typed := before_typed.allocate (.some value_typed) allocation
          have extension := HeapTypesExtend.of_allocation allocation
          exact inductionHypothesis middle_typed
            (remaining_typed.mono extension)

/-- Parameter allocation realizes the same lexical extension as its static
binder sequence.  This statement deliberately depends only on retained cell
types, so it is reusable for function, closure, and pattern entry. -/
theorem preservesEnvironmentAgreement
    {owner : Resolved.DeclarationId} {context finalContext : Context}
    {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (extension : BindersExtend owner context binders finalContext)
    (monomorphic : forall binder, binder ∈ binders ->
      binder.scheme.quantified = [])
    (agrees : EnvironmentAgrees before context.locals environment)
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) :
    EnvironmentAgrees after finalContext.locals finalEnvironment := by
  induction allocated generalizing context finalContext with
  | nil =>
      cases extension
      exact agrees
  | cons allocation tail inductionHypothesis =>
      cases extension with
      | cons headExtension tailExtension =>
          cases headExtension
          exact inductionHypothesis tailExtension
            (fun binder member => monomorphic binder (by simp [member]))
            (.cons allocation.reads_new rfl
              (.ordinary (monomorphic _ (by simp)) rfl)
              (agrees.mono (HeapTypesExtend.of_allocation allocation)))

end BindersAllocate

/-- Successful expression evaluation preserves the source result type and the
deep heap invariant. -/
structure ExpressionEvaluationPreserved
    (context : Context) (before after : Heap)
    (value : Value) (type : Ty) : Prop where
  value_typed : ValueHasType context after value type
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after

/-- Preservation obligation for one executable coercion edge.  Primitive
edges satisfy it below; method-backed edges are discharged by body-invocation
preservation in the whole-language theorem. -/
def CoercionStepExecutionPreserves
    (program : Program) (context : Context)
    (evidence : EvidenceEnvironment) : Prop :=
  forall before after step input output,
    HeapWellTyped context before ->
    ValueHasType context before input step.source ->
    CoercionStepValid context step ->
    CoercionStepExecutes program context evidence before step input output after ->
    ValueHasType context after output step.target /\
      HeapWellTyped context after /\ HeapTypesExtend before after

namespace CoercionStepExecutes

theorem primitivePreserves
    {context : Context} {heap : Heap} {step : CoercionStep}
    {input output : Value}
    (heap_typed : HeapWellTyped context heap)
    (input_typed : ValueHasType context heap input step.source)
    (applies : CoercionApplies context step input output) :
    ValueHasType context heap output step.target /\
      HeapWellTyped context heap /\ HeapTypesExtend heap heap := by
  exact ⟨applies.preserves input_typed, heap_typed, .refl heap⟩

end CoercionStepExecutes

namespace CoercionPathExecutes

/-- Once method-backed edges meet the same local obligation as primitive
edges, every retained path preserves both its endpoint type and heap world. -/
theorem preserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {before after : Heap} {source target : Ty}
    {steps : List CoercionStep} {input output : Value}
    (step_preserves : CoercionStepExecutionPreserves program context evidence)
    (valid : CoercionPathValid context source target steps)
    (before_typed : HeapWellTyped context before)
    (input_typed : ValueHasType context before input source)
    (executes : CoercionPathExecutes program context evidence before steps input
      output after) :
    ValueHasType context after output target /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  induction valid generalizing before input output after with
  | nil =>
      cases executes
      exact ⟨input_typed, before_typed, .refl before⟩
  | cons head tail inductionHypothesis =>
      cases executes with
      | cons head_executes tail_executes =>
          rcases step_preserves _ _ _ _ _ before_typed input_typed head
              head_executes with
            ⟨middle_value_typed, middle_heap_typed, head_extension⟩
          rcases inductionHypothesis middle_heap_typed middle_value_typed
              tail_executes with
            ⟨output_typed, after_heap_typed, tail_extension⟩
          exact ⟨output_typed, after_heap_typed,
            head_extension.trans tail_extension⟩

end CoercionPathExecutes

namespace CoercionPathValid

theorem append
    {context : Context} {source middle target : Ty}
    {first second : List CoercionStep}
    (left : CoercionPathValid context source middle first)
    (right : CoercionPathValid context middle target second) :
    CoercionPathValid context source target (first ++ second) := by
  induction left with
  | nil => exact right
  | cons head tail inductionHypothesis =>
      exact .cons head (inductionHypothesis right)

end CoercionPathValid

namespace ExpressionRequirementPlan.Valid

theorem outputPath
    {context : Context} {rawType finalType : Ty}
    {plan : ExpressionRequirementPlan} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan
      requirements coercions) :
    CoercionPathValid context rawType finalType coercions := by
  cases valid with
  | ordinary _ path _ => exact path
  | directCall direct =>
      cases direct with
      | intro selected contextual signature coercions_eq requirements_eq =>
          subst coercions
          exact CoercionPathValid.append selected contextual
  | indirectCall _ output _ => exact output

end ExpressionRequirementPlan.Valid

private theorem containsExpression_unique
    {source : TypedSource} {id : ExpressionId}
    {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (left_contains : ContainsExpression source id left)
    (right_contains : ContainsExpression source id right) :
    left = right := by
  have left_lookup := lookupExpression?_complete unique left_contains
  have right_lookup := lookupExpression?_complete unique right_contains
  rw [left_lookup] at right_lookup
  exact Option.some.inj right_lookup

private theorem containsStatement_unique
    {source : TypedSource} {id : StatementId}
    {left right : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (left_contains : ContainsStatement source id left)
    (right_contains : ContainsStatement source id right) :
    left = right := by
  have left_lookup := lookupStatement?_complete unique left_contains
  have right_lookup := lookupStatement?_complete unique right_contains
  rw [left_lookup] at right_lookup
  exact Option.some.inj right_lookup

/-- Recursive expression-preservation interface used by vector, projection,
operator, and raw-form cases. -/
def ExpressionExecutionPreserves
    (program : Program) (context : Context) (evidence : EvidenceEnvironment)
    (source : TypedSource) (environment : Environment) : Prop :=
  forall before after id value type,
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    ExpressionHasType source context id type ->
    ExpressionEvaluates program context evidence source environment before id
      value after ->
    ExpressionEvaluationPreserved context before after value type

namespace ExpressionsEvaluate

theorem preserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {ids : List ExpressionId} {values : List Value}
    {types : List Ty}
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : ExpressionsHaveTypes source context ids types)
    (evaluation : ExpressionsEvaluate program context evidence source environment
      before ids values after) :
    ValuesHaveTypes context after values types /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases evaluation with
  | nil =>
      cases typing
      exact ⟨.nil, before_typed, .refl before⟩
  | cons head tail =>
      cases typing with
      | cons head_type tail_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed head_type head with
            ⟨head_typed, middle_typed, head_extension⟩
          rcases ExpressionsEvaluate.preserves expression_preserves
              evidence_covers (environment_agrees.mono head_extension)
              middle_typed tail_type tail with
            ⟨tail_typed, after_typed, tail_extension⟩
          exact ⟨.cons (head_typed.mono tail_extension) tail_typed,
            after_typed, head_extension.trans tail_extension⟩
termination_by ids.length
decreasing_by simp_all

end ExpressionsEvaluate

namespace SourceProjectionsEvaluate

theorem preserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {projections : List PlaceProjection}
    {evaluated : List EvaluatedProjection} {sourceType finalType : Ty}
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : SourceProjectionsHaveType source context sourceType projections
      finalType)
    (evaluation : SourceProjectionsEvaluate program context evidence source
      environment before projections evaluated after) :
    EvaluatedProjectionsHaveType context after sourceType evaluated finalType /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases evaluation with
  | nil =>
      cases typing
      exact ⟨.nil _, before_typed, .refl before⟩
  | member tail =>
      cases typing with
      | member selected rest_type =>
          rcases SourceProjectionsEvaluate.preserves expression_preserves
              evidence_covers environment_agrees before_typed rest_type tail with
            ⟨path_typed, after_typed, extension⟩
          exact ⟨.member selected
              (Solcore.SourceSemantics.Dynamic.UniformMemberProjection.preservesType
                selected) path_typed,
            after_typed, extension⟩
  | index head tail =>
      cases typing with
      | index key_type rest_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed key_type head with
            ⟨key_typed, middle_typed, head_extension⟩
          rcases SourceProjectionsEvaluate.preserves expression_preserves
              evidence_covers (environment_agrees.mono head_extension)
              middle_typed rest_type tail with
            ⟨path_typed, after_typed, tail_extension⟩
          exact ⟨.index (key_typed.mono tail_extension) path_typed,
            after_typed, head_extension.trans tail_extension⟩
termination_by projections.length
decreasing_by all_goals simp_all

end SourceProjectionsEvaluate

/-- Dynamic information retained by a resolved place, aligned with its static
root and selected leaf types. -/
structure ResolvedPlaceHasType (context : Context) (heap : Heap)
    (place : ResolvedPlace) (rootType valueType : Ty) : Prop where
  root_type : place.rootType = rootType
  value_type : place.valueType = valueType
  projections : EvaluatedProjectionsHaveType context heap rootType
    place.projections valueType
  selected : OptionalValueHasType context heap place.selected valueType

namespace ResolvedPlaceHasType

theorem mono
    {context : Context} {before after : Heap} {place : ResolvedPlace}
    {rootType valueType : Ty}
    (extension : HeapTypesExtend before after)
    (typed : ResolvedPlaceHasType context before place rootType valueType) :
    ResolvedPlaceHasType context after place rootType valueType := {
  root_type := typed.root_type
  value_type := typed.value_type
  projections := typed.projections.mono extension
  selected := typed.selected.mono extension
}

end ResolvedPlaceHasType

namespace SourcePlaceResolves

theorem preserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {type : Ty}
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : SourcePlaceHasType source context place type)
    (resolution : SourcePlaceResolves program context evidence source environment
      before place target after) :
    exists rootType,
      ResolvedPlaceHasType context after target rootType type /\
        HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases typing with
  | @intro _ _ rootType finalType writable projections_type stored_type_eq =>
      rcases writable.scheme with
        ⟨scheme, static_lookup, scheme_well_formed, monomorphic, body_eq⟩
      cases resolution with
      | @intro _ _ _ _ _ _ _ location initialCell currentCell evaluated initial
          selected dynamic_lookup initial_read evaluate current_read initial_value
          selection =>
          rcases evaluate.preserves expression_preserves evidence_covers
              environment_agrees before_typed projections_type with
            ⟨evaluated_typed, after_typed, extension⟩
          rcases environment_agrees.lookup static_lookup with
            ⟨staticLocation, staticCell, static_lookup_runtime, static_read,
              static_cell_type, _storage⟩
          have location_eq := dynamic_lookup.functional static_lookup_runtime
          subst staticLocation
          have initial_cell_eq := initial_read.functional static_read
          subst staticCell
          rcases extension _ _ initial_read with
            ⟨updatedCell, updated_read, updated_type, _⟩
          have updated_cell_eq := current_read.functional updated_read
          subst updatedCell
          have root_type : currentCell.type = rootType :=
            updated_type.trans (static_cell_type.trans body_eq)
          have initial_typed :=
            initial_value.preserves (after_typed _ current_read.member)
          have initial_at_root :
              OptionalValueHasType context after initial rootType := by
            rw [← root_type]
            exact initial_typed
          have selected_typed :=
            selection.preserves evaluated_typed initial_at_root
          refine ⟨rootType, ?_, after_typed, extension⟩
          exact {
            root_type := root_type
            value_type := stored_type_eq
            projections := evaluated_typed
            selected := by simpa [stored_type_eq] using selected_typed
          }

end SourcePlaceResolves

namespace SourcePlaceAssignment

theorem preserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {right : ExpressionId}
    {updatedRoot : Value}
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : SourceAssignmentHasType source context assignment operator right)
    (execution : SourcePlaceAssignment program context evidence source
      (AssignmentValueApplies operator) environment before assignment.target
      right updatedRoot after) :
    HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases typing with
  | @equal _ _ _ type target_type value_type requirements_eq =>
      cases execution with
      | @intro _ _ _ _ _ _ targetHeap rhsHeap _ _ target _ rightValue _
          resolve evaluate_right write =>
          rcases resolve.preserves expression_preserves evidence_covers
              environment_agrees before_typed target_type with
            ⟨rootType, target_typed, target_heap_typed, target_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono target_extension) target_heap_typed
              value_type evaluate_right with
            ⟨right_typed, rhs_heap_typed, rhs_extension⟩
          have target_rhs_typed := target_typed.mono rhs_extension
          cases write with
          | intro current_read root_type_eq initial_value update heap_write =>
              rename_i currentCell initial
              have initial_typed :=
                initial_value.preserves (rhs_heap_typed _ current_read.member)
              have initial_root_typed :
                  OptionalValueHasType context rhsHeap initial rootType := by
                rw [← target_rhs_typed.root_type, ← root_type_eq]
                exact initial_typed
              have modify_typed : LeafModificationPreservesType context rhsHeap
                  (fun _ updated =>
                    AssignmentValueApplies .equal target.selected rightValue
                      updated) type := by
                intro current updated current_typed applies
                exact applies.equalPreserves right_typed
              have updated_typed := update.preserves
                target_rhs_typed.projections initial_root_typed modify_typed
              have updated_cell_typed :
                  ValueHasType context rhsHeap updatedRoot currentCell.type := by
                rw [root_type_eq, target_rhs_typed.root_type]
                exact updated_typed
              have final_typed := rhs_heap_typed.write current_read
                (.some updated_cell_typed) heap_write
              exact ⟨final_typed,
                (target_extension.trans rhs_extension).trans
                  (HeapTypesExtend.of_write heap_write)⟩
  | wordCompound kind target_type value_type requirements_eq =>
      cases execution with
      | @intro _ _ _ _ _ _ targetHeap rhsHeap _ _ target _ rightValue _
          resolve evaluate_right write =>
          rcases resolve.preserves expression_preserves evidence_covers
              environment_agrees before_typed target_type with
            ⟨rootType, target_typed, target_heap_typed, target_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono target_extension) target_heap_typed
              value_type evaluate_right with
            ⟨right_typed, rhs_heap_typed, rhs_extension⟩
          have target_rhs_typed := target_typed.mono rhs_extension
          cases write with
          | intro current_read root_type_eq initial_value update heap_write =>
              rename_i currentCell initial
              have initial_typed :=
                initial_value.preserves (rhs_heap_typed _ current_read.member)
              have initial_root_typed :
                  OptionalValueHasType context rhsHeap initial rootType := by
                rw [← target_rhs_typed.root_type, ← root_type_eq]
                exact initial_typed
              have modify_typed : LeafModificationPreservesType context rhsHeap
                  (fun _ updated =>
                    AssignmentValueApplies operator target.selected rightValue
                      updated) .word := by
                intro current updated current_typed applies
                exact applies.wordCompoundPreserves kind
                  target_rhs_typed.selected right_typed
              have updated_typed := update.preserves
                target_rhs_typed.projections initial_root_typed modify_typed
              have updated_cell_typed :
                  ValueHasType context rhsHeap updatedRoot currentCell.type := by
                rw [root_type_eq, target_rhs_typed.root_type]
                exact updated_typed
              have final_typed := rhs_heap_typed.write current_read
                (.some updated_cell_typed) heap_write
              exact ⟨final_typed,
                (target_extension.trans rhs_extension).trans
                  (HeapTypesExtend.of_write heap_write)⟩

end SourcePlaceAssignment

namespace SourcePlaceSnapshotUpdate

theorem bitNotPreserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {assignment : AssignmentResolution}
    {updatedRoot : Value}
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : SourceBitNotAssignmentValid source context assignment)
    (execution : SourcePlaceSnapshotUpdate program context evidence source
      BitNotSnapshot environment before assignment.target updatedRoot after) :
    HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases typing with
  | intro target_type requirements_eq =>
      cases execution with
      | @intro _ _ _ _ _ _ selectedHeap _ _ target _ resolve write =>
          rcases resolve.preserves expression_preserves evidence_covers
              environment_agrees before_typed target_type with
            ⟨rootType, target_typed, selected_heap_typed, target_extension⟩
          cases write with
          | intro current_read root_type_eq initial_value update heap_write =>
              rename_i currentCell initial
              have initial_typed := initial_value.preserves
                (selected_heap_typed _ current_read.member)
              have initial_root_typed :
                  OptionalValueHasType context selectedHeap initial rootType := by
                rw [← target_typed.root_type, ← root_type_eq]
                exact initial_typed
              have modify_typed : LeafModificationPreservesType context
                  selectedHeap (fun _ updated =>
                    BitNotSnapshot target.selected updated) .word := by
                intro current updated current_typed modifies
                exact modifies.preserves target_typed.selected
              have updated_typed := update.preserves target_typed.projections
                initial_root_typed modify_typed
              have updated_cell_typed : ValueHasType context selectedHeap
                  updatedRoot currentCell.type := by
                rw [root_type_eq, target_typed.root_type]
                exact updated_typed
              have final_typed := selected_heap_typed.write current_read
                (.some updated_cell_typed) heap_write
              exact ⟨final_typed,
                target_extension.trans (HeapTypesExtend.of_write heap_write)⟩

end SourcePlaceSnapshotUpdate

theorem MonoBindersExtend.bodyTypes_eq
    {owner : Resolved.DeclarationId} {context finalContext : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types finalContext) :
    binders.map (fun binder => binder.scheme.body) = types := by
  induction extension with
  | nil => rfl
  | cons scheme_eq _ _ induction =>
      simp [scheme_eq, TypeSystem.Scheme.mono, induction]

/-- Local preservation interface for primitive or source-method unary
application.  The whole-language induction supplies the method case. -/
def UnaryOperationExecutionPreserves
    (program : Program) (context : Context) (evidence : EvidenceEnvironment) :
    Prop :=
  forall before after operator requirements input output operandType resultType,
    HeapWellTyped context before ->
    ValueHasType context before input operandType ->
    UnaryOperatorHasType context operator operandType resultType requirements ->
    UnaryOperationApplies program context evidence before operator requirements
      input output after ->
    ValueHasType context after output resultType /\
      HeapWellTyped context after /\ HeapTypesExtend before after

/-- Local preservation interface for strict primitive or source-method binary
application. -/
def BinaryOperationExecutionPreserves
    (program : Program) (context : Context) (evidence : EvidenceEnvironment) :
    Prop :=
  forall before after operator requirements left right output operandType
      resultType,
    HeapWellTyped context before ->
    ValueHasType context before left operandType ->
    ValueHasType context before right operandType ->
    BinaryOperatorHasType context operator operandType operandType resultType
      requirements ->
    BinaryOperationApplies program context evidence before operator requirements
      left right output after ->
    ValueHasType context after output resultType /\
      HeapWellTyped context after /\ HeapTypesExtend before after

/-- Local preservation interface for first-class application.  Argument types
remain pointwise so body-input allocation can consume them directly. -/
def CallableApplicationPreserves
    (program : Program) (context : Context)
    (callerEvidence : EvidenceEnvironment) : Prop :=
  forall invocationEvidence before after callable arguments result parameterType
      resultType packed,
    HeapWellTyped context before ->
    ValueHasType context before callable
      (.function parameterType resultType) ->
    ValuesPack arguments packed ->
    ValueHasType context before packed parameterType ->
    CallableApplies program context callerEvidence invocationEvidence before
      callable arguments result after ->
    ValueHasType context after result resultType /\
      HeapWellTyped context after /\ HeapTypesExtend before after

private theorem ordinaryRequirementLayout_eq
    {context : Context} {rawType finalType : Ty}
    {requirements owned staticOwned : List RequirementId}
    {coercions : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType finalType
      (.ordinary staticOwned) requirements coercions)
    (layout : OrdinaryRequirementLayout requirements coercions owned) :
    owned = staticOwned := by
  cases valid with
  | ordinary _ _ requirements_eq =>
      unfold OrdinaryRequirementLayout at layout
      rw [requirements_eq] at layout
      exact List.append_cancel_right layout.symm

/-- The mutually recursive raw-form preservation obligation.  It isolates
recursive source evaluation from the generic output-coercion theorem below. -/
def ExpressionFormExecutionPreserves
    (program : Program) (context : Context) (evidence : EvidenceEnvironment)
    (source : TypedSource) (environment : Environment) : Prop :=
  forall before after form requirements coercions raw rawType finalType plan,
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    (exists id node,
      ContainsExpression source id node /\ node.form = form /\
        node.rawType = rawType) ->
    ExpressionFormHasRawType source context form rawType plan ->
    ExpressionRequirementPlan.Valid context rawType finalType plan requirements
      coercions ->
    ExpressionFormEvaluates program context evidence source environment before
      form requirements coercions raw after ->
    ValueHasType context after raw rawType /\
      HeapWellTyped context after /\ HeapTypesExtend before after

namespace ExpressionEvaluates

/-- Generic output coercions turn raw-form preservation into preservation for
the complete expression occurrence judgment. -/
theorem preservesOfForm
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : Ty}
    (graph : OccurrenceGraphWellFormed source)
    (form_preserves :
      ExpressionFormExecutionPreserves program context evidence source environment)
    (step_preserves : CoercionStepExecutionPreserves program context evidence)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : ExpressionHasType source context id type)
    (evaluation : ExpressionEvaluates program context evidence source environment
      before id value after) :
    ExpressionEvaluationPreserved context before after value type := by
  cases typing with
  | @intro _ _ typedNode rawType plan typed_contains form_type raw_type_eq
      raw_well_formed type_well_formed requirements =>
      cases evaluation with
      | @intro _ _ _ _ _ middle _ _ evaluatedNode raw result evaluated_contains
          form_evaluation coercion_evaluation =>
          have node_eq := containsExpression_unique
            graph.nodeOccurrencesUnique typed_contains evaluated_contains
          subst evaluatedNode
          rcases form_preserves _ _ _ _ _ _ _ _ _ environment_agrees
              before_typed ⟨_, typedNode, typed_contains, rfl, raw_type_eq⟩
              form_type requirements form_evaluation with
            ⟨raw_typed, middle_typed, raw_extension⟩
          rcases coercion_evaluation.preserves step_preserves
              (ExpressionRequirementPlan.Valid.outputPath requirements)
              middle_typed raw_typed with
            ⟨result_typed, after_typed, coercion_extension⟩
          exact {
            value_typed := result_typed
            heap_typed := after_typed
            heap_extends := raw_extension.trans coercion_extension
          }

end ExpressionEvaluates

namespace ExpressionFormEvaluates

theorem referencePreserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {name : String} {resolution : ReferenceResolution}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    {value : Value} {rawType : Ty} {plan : ExpressionRequirementPlan}
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : ExpressionFormHasRawType source context
      (.reference name resolution) rawType plan)
    (evaluation : ExpressionFormEvaluates program context evidence source
      environment before (.reference name resolution) requirements coercions
      value after) :
    ValueHasType context after value rawType /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases typing with
  | reference reference_use =>
      have reference_type := reference_use.raw_type
      cases reference_type with
      | «local» static_lookup instantiates =>
          cases evaluation with
          | «local» layout dynamic_lookup read descriptor_empty initialized =>
              have monomorphic :=
                environment_agrees.lookup_monomorphic_of_descriptor_empty
                  static_lookup dynamic_lookup read descriptor_empty
              have raw_eq := monomorphicInstance_eq_body monomorphic instantiates
              rcases environment_agrees.lookup static_lookup with
                ⟨typedLocation, typedCell, typed_lookup, typed_read, cell_type,
                  _storage⟩
              have location_eq := dynamic_lookup.functional typed_lookup
              subst typedLocation
              have cell_eq := read.functional typed_read
              subst typedCell
              have cell_value := (before_typed _ read.member).value
              rw [initialized] at cell_value
              cases cell_value with
              | some value_typed =>
                  have result_typed :
                      ValueHasType context before value rawType := by
                    rw [raw_eq, ← cell_type]
                    exact value_typed
                  exact ⟨result_typed, before_typed, .refl before⟩
          | @localEmptyMapping _ _ _ _ _ _ _ _ _ _ location cell keyType
              valueType layout dynamic_lookup read descriptor_empty type_eq empty
              write =>
              have monomorphic :=
                environment_agrees.lookup_monomorphic_of_descriptor_empty
                  static_lookup dynamic_lookup read descriptor_empty
              have raw_eq := monomorphicInstance_eq_body monomorphic instantiates
              rcases environment_agrees.lookup static_lookup with
                ⟨typedLocation, typedCell, typed_lookup, typed_read, cell_type,
                  _storage⟩
              have location_eq := dynamic_lookup.functional typed_lookup
              subst typedLocation
              have cell_eq := read.functional typed_read
              subst typedCell
              have mapping_typed : ValueHasType context before
                  (.mapping keyType valueType []) (.mapping keyType valueType) :=
                .mapping (.nil _ _)
              have mapping_at_cell : ValueHasType context before
                  (.mapping keyType valueType []) cell.type := by
                rw [type_eq]
                exact mapping_typed
              have after_typed := before_typed.write read
                (.some mapping_at_cell) write
              have extension := HeapTypesExtend.of_write write
              have result_typed := mapping_at_cell.mono extension
              have raw_cell : rawType = cell.type :=
                raw_eq.trans cell_type.symm
              rw [raw_cell]
              exact ⟨result_typed, after_typed, extension⟩
      | declaration valid =>
          cases evaluation with
          | declaration layout dynamic_valid requirements_close =>
              refine ⟨.global dynamic_valid ?_, before_typed,
                .refl before⟩
              constructor
              · exact requirements_close.valid
              · intro predicate member
                exact requirements_close.supplies predicate member
      | builtinFunction function =>
          cases evaluation
          exact ⟨.builtin ⟨function⟩, before_typed, .refl before⟩
      | builtinBoolean boolean =>
          cases evaluation
          exact ⟨.bool boolean, before_typed, .refl before⟩

theorem literalPreserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {literal : Syntax.CoreLiteralValue}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    {value : Value}
    (before_typed : HeapWellTyped context before)
    (evaluation : ExpressionFormEvaluates program context evidence source
      environment before (.literal literal) requirements coercions value after) :
    ValueHasType context after value .word /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases evaluation with
  | literal layout constructs =>
      exact ⟨constructs.hasType, before_typed, .refl before⟩

theorem integerLiteralPreserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    {value : Value}
    (before_typed : HeapWellTyped context before)
    (evaluation : ExpressionFormEvaluates program context evidence source
      environment before (.integerLiteral literal resolution) requirements
      coercions value after) :
    ValueHasType context after value resolution.targetType /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases evaluation with
  | integerLiteral layout constructs =>
      exact ⟨constructs.hasType, before_typed, .refl before⟩

theorem proxyPreserves
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {inner : Ty}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    {value : Value}
    (before_typed : HeapWellTyped context before)
    (evaluation : ExpressionFormEvaluates program context evidence source
      environment before (.proxy inner) requirements coercions value after) :
    ValueHasType context after value (.proxy inner) /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases evaluation with
  | proxy => exact ⟨.proxy inner, before_typed, .refl before⟩

/-- Raw expression preservation, with the genuinely recursive operation and
call edges supplied as local induction hypotheses. -/
theorem preservesWith
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {form : ExpressionForm}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    {raw : Value} {rawType finalType : Ty}
    {plan : ExpressionRequirementPlan}
    (graph : OccurrenceGraphWellFormed source)
    (owner : context.currentDeclaration = some source.owner)
    (closed : context.typeParameters = [])
    (variables_closed : context.typeVariables = [])
    (residual_variables_open : context.residualTypeVariables = true)
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (unary_preserves :
      UnaryOperationExecutionPreserves program context evidence)
    (binary_preserves :
      BinaryOperationExecutionPreserves program context evidence)
    (step_preserves : CoercionStepExecutionPreserves program context evidence)
    (callable_preserves :
      CallableApplicationPreserves program context evidence)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (occurrence : exists id node,
      ContainsExpression source id node /\ node.form = form /\
        node.rawType = rawType)
    (typing : ExpressionFormHasRawType source context form rawType plan)
    (requirements_valid : ExpressionRequirementPlan.Valid context rawType
      finalType plan requirements coercions)
    (evaluation : ExpressionFormEvaluates program context evidence source
      environment before form requirements coercions raw after) :
    ValueHasType context after raw rawType /\
      HeapWellTyped context after /\ HeapTypesExtend before after := by
  cases typing with
  | literal valid =>
      exact evaluation.literalPreserves before_typed
  | integerLiteral valid =>
      exact evaluation.integerLiteralPreserves before_typed
  | reference reference_use =>
      exact evaluation.referencePreserves environment_agrees before_typed
        (.reference reference_use)
  | group inner_type =>
      cases evaluation with
      | group layout inner_evaluates =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed inner_type inner_evaluates with
            ⟨value_typed, after_typed, extension⟩
          exact ⟨value_typed, after_typed, extension⟩
  | tuple elements_type =>
      cases evaluation with
      | tuple layout elements_evaluate pack =>
          rcases elements_evaluate.preserves expression_preserves evidence_covers
              environment_agrees before_typed elements_type with
            ⟨values_typed, after_typed, extension⟩
          exact ⟨pack.hasType values_typed, after_typed, extension⟩
  | unary operand_type operator_type =>
      cases evaluation with
      | unary layout operand_evaluates applies =>
          have owned_eq := ordinaryRequirementLayout_eq requirements_valid layout
          subst owned_eq
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed operand_type operand_evaluates with
            ⟨operand_typed, middle_typed, operand_extension⟩
          rcases unary_preserves _ _ _ _ _ _ _ _ middle_typed operand_typed
              operator_type applies with
            ⟨result_typed, after_typed, operation_extension⟩
          exact ⟨result_typed, after_typed,
            operand_extension.trans operation_extension⟩
  | binary left_type right_type operator_type =>
      cases evaluation with
      | binaryShortCircuit layout left_evaluates circuit owned_empty =>
          have owned_eq := ordinaryRequirementLayout_eq requirements_valid layout
          subst owned_eq
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed left_type left_evaluates with
            ⟨left_typed, after_typed, extension⟩
          cases circuit <;> cases operator_type
          all_goals try { rename_i kind; cases kind }
          all_goals try { rename_i dispatch profile proof; cases dispatch }
          all_goals exact ⟨.bool _, after_typed, extension⟩
      | binaryEvaluateRight layout left_evaluates evaluate_right right_evaluates
          applies =>
          have owned_eq := ordinaryRequirementLayout_eq requirements_valid layout
          subst owned_eq
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed left_type left_evaluates with
            ⟨left_typed, left_heap_typed, left_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono left_extension) left_heap_typed right_type
              right_evaluates with
            ⟨right_typed, right_heap_typed, right_extension⟩
          rcases binary_preserves _ _ _ _ _ _ _ _ _ right_heap_typed
              (left_typed.mono right_extension) right_typed operator_type applies with
            ⟨result_typed, after_typed, operation_extension⟩
          exact ⟨result_typed, after_typed,
            (left_extension.trans right_extension).trans operation_extension⟩
  | conditional condition_type then_type else_type =>
      cases evaluation with
      | conditionalTrue layout condition_evaluates branch_evaluates =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨_, middle_typed, condition_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono condition_extension) middle_typed then_type
              branch_evaluates with
            ⟨value_typed, after_typed, branch_extension⟩
          exact ⟨value_typed, after_typed,
            condition_extension.trans branch_extension⟩
      | conditionalFalse layout condition_evaluates branch_evaluates =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨_, middle_typed, condition_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono condition_extension) middle_typed else_type
              branch_evaluates with
            ⟨value_typed, after_typed, branch_extension⟩
          exact ⟨value_typed, after_typed,
            condition_extension.trans branch_extension⟩
  | @lambda _ lambdaContext finalContext parameters parameterTypes returnType
      body bodyFacts names_unique parameters_extend body_type body_completes =>
      cases evaluation with
      | lambda layout =>
          rcases occurrence with ⟨id, node, contains, node_form, node_raw⟩
          have body_types :=
            Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
              parameters_extend
          have form_typed := ExpressionFormHasRawType.lambda names_unique
            parameters_extend body_type body_completes
          have code : ClosureCodeValid context {
              parameters := parameters
              resultType := returnType
              body := body
              source := source
              captured := environment
              context := context
              evidence := evidence
            } := {
            owner := owner
            closed := closed
            variables_closed := variables_closed
            residual_variables_open := residual_variables_open
            graph := graph
            occurrence := ⟨id, node, contains, node_form, by
                simpa [body_types] using node_raw, by
                rw [node_form]
                simpa [body_types] using form_typed⟩
          }
          exact ⟨by
              simpa [body_types] using
                (ValueHasType.closure (context := context) (heap := before)
                  (function := {
                    parameters := parameters
                    resultType := returnType
                    body := body
                    source := source
                    captured := environment
                    context := context
                    evidence := evidence
                  }) rfl code evidence_covers environment_agrees),
            before_typed, .refl before⟩
  | @directCall _ callee arguments instantiation parameterTypes resultType
      predicates callee_valid application arguments_type =>
      cases evaluation with
      | @directCall _ _ _ _ _ argumentsHeap _ _ _ instantiation _ _
          argumentValues calleeEvidence _ _ _ callee_contains callee_form
          callee_requirements
          callee_coercions dynamic_valid arguments_evaluate call_evidence applies =>
          rcases arguments_evaluate.preserves expression_preserves evidence_covers
              environment_agrees before_typed arguments_type with
            ⟨arguments_typed, arguments_heap_typed, arguments_extension⟩
          cases application with
          | intro signature_mem valid declaration_eq parameter_types_eq
              result_type_eq function_type_eq predicates_eq =>
              cases call_evidence with
              | intro coercions_eq requirements_eq produces =>
                  have callee_typed : ValueHasType context argumentsHeap
                      (.global ⟨instantiation, calleeEvidence⟩)
                      (.function (Ty.productMany parameterTypes) rawType) := by
                    rw [← function_type_eq]
                    exact .global dynamic_valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  rcases ValuesPack.exists_pack argumentValues with
                    ⟨packed, pack⟩
                  have packed_typed := pack.hasType arguments_typed
                  rcases callable_preserves _ _ _ _ _ _ _ _ _
                      arguments_heap_typed callee_typed pack packed_typed applies with
                    ⟨result_typed, after_typed, call_extension⟩
                  exact ⟨result_typed, after_typed,
                    arguments_extension.trans call_extension⟩
  | @builtinCall _ callee arguments function callee_valid arguments_type =>
      cases evaluation with
      | @builtinCall _ _ _ _ _ argumentsHeap _ _ _ function _ _ argumentValues _ layout
          arguments_evaluate applies =>
          rcases arguments_evaluate.preserves expression_preserves evidence_covers
              environment_agrees before_typed arguments_type with
            ⟨arguments_typed, arguments_heap_typed, arguments_extension⟩
          have callee_typed : ValueHasType context argumentsHeap
              (.builtin ⟨function⟩)
              (.function (Ty.productMany function.parameterTypes)
                function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap)
                ⟨function⟩)
          rcases ValuesPack.exists_pack argumentValues with ⟨packed, pack⟩
          have packed_typed := pack.hasType arguments_typed
          rcases callable_preserves _ _ _ _ _ _ _ _ _ arguments_heap_typed
              callee_typed pack packed_typed applies with
            ⟨result_typed, after_typed, call_extension⟩
          exact ⟨result_typed, after_typed,
            arguments_extension.trans call_extension⟩
  | indirectCall callee_type arguments_type application =>
      cases evaluation with
      | indirectCall requirements_eq callee_evaluates arguments_evaluate pack_before
          argument_coercions pack_after source_arity applied_arity applies =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed callee_type callee_evaluates with
            ⟨callee_typed, callee_heap_typed, callee_extension⟩
          rcases arguments_evaluate.preserves expression_preserves evidence_covers
              (environment_agrees.mono callee_extension) callee_heap_typed
              arguments_type with
            ⟨arguments_typed, argument_heap_typed, argument_extension⟩
          cases application with
          | intro count_eq before_eq after_eq path_valid =>
              have packed_typed := pack_before.hasType arguments_typed
              rw [← before_eq] at packed_typed
              rcases argument_coercions.preserves step_preserves path_valid
                  argument_heap_typed packed_typed with
                ⟨coerced_typed, coerced_heap_typed, coercion_extension⟩
              have callable_typed := callee_typed.mono
                (argument_extension.trans coercion_extension)
              rcases callable_preserves _ _ _ _ _ _ _ _ _ coerced_heap_typed
                  callable_typed pack_after coerced_typed applies with
                ⟨result_typed, after_typed, call_extension⟩
              exact ⟨result_typed, after_typed,
                ((callee_extension.trans argument_extension).trans
                  coercion_extension).trans call_extension⟩
  | constructor valid arguments_type =>
      cases evaluation with
      | constructor layout dynamic_valid arguments_evaluate =>
          rcases arguments_evaluate.preserves expression_preserves evidence_covers
              environment_agrees before_typed arguments_type with
            ⟨arguments_typed, after_typed, extension⟩
          exact ⟨.constructed dynamic_valid arguments_typed, after_typed,
            extension⟩
  | member base_type member_type =>
      cases evaluation with
      | member layout base_evaluates selected_at =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed base_type base_evaluates with
            ⟨base_typed, after_typed, extension⟩
          exact ⟨(Solcore.SourceSemantics.Dynamic.UniformMemberProjection.preservesType
              member_type).read _ _ _ base_typed selected_at,
            after_typed, extension⟩
  | proxy inner_well_formed =>
      exact evaluation.proxyPreserves before_typed
  | @index _ base key keyType valueType base_type key_type =>
      cases evaluation with
      | indexFound layout base_evaluates index_evaluates lookup =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed base_type base_evaluates with
            ⟨base_typed, middle_typed, base_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono base_extension) middle_typed key_type
              index_evaluates with
            ⟨key_typed, after_typed, index_extension⟩
          rcases (base_typed.mono index_extension).mappingComponents with
            ⟨rfl, rfl, entries_typed⟩
          exact ⟨lookup.preserves entries_typed, after_typed,
            base_extension.trans index_extension⟩
      | indexDefault layout base_evaluates index_evaluates absent defaulted =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed base_type base_evaluates with
            ⟨base_typed, middle_typed, base_extension⟩
          rcases expression_preserves _ _ _ _ _ evidence_covers
              (environment_agrees.mono base_extension) middle_typed key_type
              index_evaluates with
            ⟨key_typed, after_typed, index_extension⟩
          rcases (base_typed.mono index_extension).mappingComponents with
            ⟨rfl, rfl, entries_typed⟩
          exact ⟨defaulted.hasType, after_typed,
            base_extension.trans index_extension⟩

end ExpressionFormEvaluates

namespace CallableApplies

theorem builtinPreserves
    {program : Program} {context : Context}
    {callerEvidence invocationEvidence : EvidenceEnvironment}
    {before after : Heap} {function : BuiltinFunction}
    {arguments : List Value} {result : Value}
    (application : CallableApplies program context callerEvidence
      invocationEvidence before (.builtin function) arguments result after) :
    after = before /\
      ValuesHaveTypes context before arguments function.id.parameterTypes /\
      ValueHasType context before result function.id.returnType := by
  cases application with
  | builtin applies =>
      rcases applies.preserves with ⟨arguments_typed, result_typed⟩
      exact ⟨rfl, arguments_typed, result_typed⟩

end CallableApplies

/-- Lexical extension changes only locals; these are the non-local fields used
by dynamic typing, evidence, and closure-code provenance. -/
structure RuntimeContextFields (source target : Context) : Prop where
  signatures : target.signatures = source.signatures
  currentDeclaration :
    target.currentDeclaration = source.currentDeclaration
  typeParameters : target.typeParameters = source.typeParameters
  typeVariables : target.typeVariables = source.typeVariables
  residualTypeVariables :
    target.residualTypeVariables = source.residualTypeVariables
  assumptions : target.assumptions = source.assumptions
  solvedRequirements :
    target.solvedRequirements = source.solvedRequirements

namespace RuntimeContextFields

theorem refl (context : Context) : RuntimeContextFields context context :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {first middle last : Context}
    (left : RuntimeContextFields first middle)
    (right : RuntimeContextFields middle last) :
    RuntimeContextFields first last :=
  ⟨right.signatures.trans left.signatures,
    right.currentDeclaration.trans left.currentDeclaration,
    right.typeParameters.trans left.typeParameters,
    right.typeVariables.trans left.typeVariables,
    right.residualTypeVariables.trans left.residualTypeVariables,
    right.assumptions.trans left.assumptions,
    right.solvedRequirements.trans left.solvedRequirements⟩

theorem ofBinderExtends
    {owner : Resolved.DeclarationId} {source target : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner source binder target) :
    RuntimeContextFields source target := by
  cases extension
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sourceClosed
    {source target : Context} (fields : RuntimeContextFields source target)
    (target_closed : target.typeParameters = []) :
    source.typeParameters = [] := by
  rw [← fields.typeParameters]
  exact target_closed

theorem targetClosed
    {source target : Context} (fields : RuntimeContextFields source target)
    (source_closed : source.typeParameters = []) :
    target.typeParameters = [] := fields.typeParameters.trans source_closed

theorem sourceVariablesClosed
    {source target : Context} (fields : RuntimeContextFields source target)
    (target_closed : target.typeVariables = []) :
    source.typeVariables = [] := by
  rw [← fields.typeVariables]
  exact target_closed

theorem targetVariablesClosed
    {source target : Context} (fields : RuntimeContextFields source target)
    (source_closed : source.typeVariables = []) :
    target.typeVariables = [] := fields.typeVariables.trans source_closed

theorem sourceResidualVariablesOpen
    {source target : Context} (fields : RuntimeContextFields source target)
    (target_open : target.residualTypeVariables = true) :
    source.residualTypeVariables = true := by
  rw [← fields.residualTypeVariables]
  exact target_open

theorem targetResidualVariablesOpen
    {source target : Context} (fields : RuntimeContextFields source target)
    (source_open : source.residualTypeVariables = true) :
    target.residualTypeVariables = true :=
  fields.residualTypeVariables.trans source_open

theorem covers
    {source target : Context} {evidence : EvidenceEnvironment}
    (fields : RuntimeContextFields source target)
    (covers : evidence.Covers source) : evidence.Covers target := by
  constructor
  · simpa [fields.signatures] using covers.1
  · intro predicate member
    apply covers.2 predicate
    simpa [fields.assumptions] using member

end RuntimeContextFields

/-- Static invariants shared by every successful execution rooted in one
rigidly and lexically closed, residual-open source body.  In particular,
ledger identity uniqueness is needed to identify the predicate selected
independently by static typing and dynamic method dispatch.  Entry validity
remains local to the corresponding typing derivations. -/
structure SourceRuntimeValid (program : Program) (context : Context)
    (source : TypedSource) : Prop where
  signatures : context.signatures = program.signatures
  graph : OccurrenceGraphWellFormed source
  owner : context.currentDeclaration = some source.owner
  closed : context.typeParameters = []
  variables_closed : context.typeVariables = []
  residual_variables_open : context.residualTypeVariables = true
  ledger : RequirementIdsUnique context

namespace SourceRuntimeValid

theorem transport
    {program : Program} {source target : Context} {typedSource : TypedSource}
    (valid : SourceRuntimeValid program source typedSource)
    (fields : RuntimeContextFields source target) :
    SourceRuntimeValid program target typedSource := by
  refine {
    signatures := fields.signatures.trans valid.signatures
    graph := valid.graph
    owner := fields.currentDeclaration.trans valid.owner
    closed := fields.typeParameters.trans valid.closed
    variables_closed := fields.typeVariables.trans valid.variables_closed
    residual_variables_open :=
      fields.residualTypeVariables.trans valid.residual_variables_open
    ledger := ?_
  }
  simpa [RequirementIdsUnique, fields.solvedRequirements] using valid.ledger

end SourceRuntimeValid

private theorem expressionHasType_details
    {source : TypedSource} {context : Context}
    {initializer : ExpressionId} {type : Ty}
    (typing : ExpressionHasType source context initializer type) :
    ∃ node rawType plan,
      ContainsExpression source initializer node ∧
      node.type = type ∧
      ExpressionFormHasRawType source context node.form rawType plan ∧
      node.rawType = rawType := by
  cases typing with
  | intro contains form_type raw_type_eq raw_well_formed type_well_formed
      requirements =>
      exact ⟨_, _, _, contains, rfl, form_type, raw_type_eq⟩

namespace GeneralizedClosureCaptures

/-- A canonical generalized direct-lambda capture inherits deep runtime
typing from its static initializer, lexical binder formation, and the current
environment/heap agreement. -/
theorem wellTyped
    {program : Program} {context finalContext : Context}
    {source : TypedSource} {environment : Environment} {heap : Heap}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function)
    (runtime : SourceRuntimeValid program context source)
    (environment_agrees :
      EnvironmentAgrees heap context.locals environment)
    (polymorphic : binder.scheme.quantified ≠ [])
    (requirements_well_formed :
      LocalSchemeRequirementsWellFormed context binder)
    (generalizes : SchemeGeneralizesExcept context
      (localSchemeTemplateIds binder) binder.scheme)
    (initializer_type : ExpressionHasType source
      (localSchemeInitializerContext context binder) initializer
      binder.scheme.body)
    (extension : BinderExtends source.owner context binder finalContext) :
    GeneralizedClosureWellTyped context heap function := by
  cases extension with
  | intro binder_well_formed fresh =>
      cases captures with
      | @directLambda node parameters resultType body contains form_eq
          raw_type_eq type_eq requirements_empty coercions_empty =>
          rcases expressionHasType_details initializer_type with
            ⟨typedNode, rawType, plan, typed_contains, stored_type_eq,
              form_type, typed_raw_type_eq⟩
          have node_eq := containsExpression_unique
            runtime.graph.nodeOccurrencesUnique typed_contains contains
          subst typedNode
          have retained_raw_type_eq : rawType = binder.scheme.body :=
            typed_raw_type_eq.symm.trans raw_type_eq
          rw [form_eq] at form_type
          cases form_type with
          | lambda names_unique parameters_extend body_type body_completes =>
              refine {
                same_signatures := rfl
                code := {
                  owner := runtime.owner
                  closed := runtime.closed
                  variables_closed := runtime.variables_closed
                  residual_variables_open := runtime.residual_variables_open
                  polymorphic := polymorphic
                  binder_well_formed := binder_well_formed
                  requirements_well_formed := requirements_well_formed
                  generalizes := generalizes
                  graph := runtime.graph
                  occurrence := ⟨node, contains, form_eq, raw_type_eq,
                    type_eq, requirements_empty, coercions_empty, ?_⟩
                }
                captures := environment_agrees
              }
              change ExpressionFormHasRawType source
                (localSchemeInitializerContext context binder) node.form
                binder.scheme.body (.ordinary [])
              rw [form_eq, ← retained_raw_type_eq]
              exact .lambda names_unique parameters_extend body_type
                body_completes

end GeneralizedClosureCaptures

namespace BindersExtend

theorem functional
    {owner : Resolved.DeclarationId} {context left right : Context}
    {binders : List TypedBinder}
    (left_extension : BindersExtend owner context binders left)
    (right_extension : BindersExtend owner context binders right) : left = right := by
  induction left_extension generalizing right with
  | nil =>
      cases right_extension
      rfl
  | cons left_head left_tail induction =>
      cases right_extension with
      | cons right_head right_tail =>
          cases left_head
          cases right_head
          exact induction right_tail

theorem runtimeContextFields
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner source binders target) :
    RuntimeContextFields source target := by
  induction extension with
  | nil => exact .refl _
  | cons head tail induction =>
      exact (RuntimeContextFields.ofBinderExtends head).trans induction

end BindersExtend

namespace BinderExtends

theorem functional
    {owner : Resolved.DeclarationId} {context left right : Context}
    {binder : TypedBinder}
    (left_extension : BinderExtends owner context binder left)
    (right_extension : BinderExtends owner context binder right) : left = right := by
  cases left_extension
  cases right_extension
  rfl

end BinderExtends

namespace MonoBindersExtend

theorem functional
    {owner : Resolved.DeclarationId} {context left right : Context}
    {binders : List TypedBinder} {leftTypes rightTypes : List Ty}
    (left_extension : MonoBindersExtend owner context binders leftTypes left)
    (right_extension : MonoBindersExtend owner context binders rightTypes right) :
    left = right := by
  induction left_extension generalizing right rightTypes with
  | nil =>
      cases right_extension
      rfl
  | cons left_scheme left_head left_tail induction =>
      cases right_extension with
      | cons right_scheme right_head right_tail =>
          cases left_head
          cases right_head
          exact induction right_tail

theorem runtimeContextFields
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner source binders types target) :
    RuntimeContextFields source target := by
  induction extension with
  | nil => exact .refl _
  | cons scheme_eq head tail induction =>
      exact (RuntimeContextFields.ofBinderExtends head).trans induction

end MonoBindersExtend

namespace StatementHasType

/-- Form-indexed inversion view of statement typing.  Unlike the occurrence
judgment, this view can be aligned directly with an evaluator constructor
after occurrence uniqueness identifies their nodes. -/
inductive FormTyping (source : TypedSource) (control : ControlContext)
    (context : Context) : StatementForm -> Context -> Prop where
  | letUninitialized {binder final}
      (monomorphic : binder.scheme.quantified = [])
      (extension : BinderExtends source.owner context binder final) :
      FormTyping source control context (.letDecl binder none) final
  | letInitialized {binder initializer final}
      (initializer_type : ExpressionHasType source context initializer
        binder.scheme.body)
      (monomorphic : binder.scheme.quantified = [])
      (extension : BinderExtends source.owner context binder final) :
      FormTyping source control context (.letDecl binder (some initializer)) final
  | letInitializedGeneralized {binder initializer final}
      (polymorphic : binder.scheme.quantified ≠ [])
      (requirements_well_formed :
        LocalSchemeRequirementsWellFormed context binder)
      (generalizes : SchemeGeneralizesExcept context
        (localSchemeTemplateIds binder) binder.scheme)
      (initializer_type : ExpressionHasType source
        (localSchemeInitializerContext context binder) initializer
        binder.scheme.body)
      (extension : BinderExtends source.owner context binder final) :
      FormTyping source control context (.letDecl binder (some initializer)) final
  | returnUnit (return_type_eq : control.returnType = .unit) :
      FormTyping source control context (.returnStmt none) context
  | returnValue {value}
      (value_type : ExpressionHasType source context value control.returnType) :
      FormTyping source control context (.returnStmt (some value)) context
  | expressionValue {expression type}
      (expression_type : ExpressionHasType source context expression type) :
      FormTyping source control context (.expression expression false) context
  | expressionDiscard {expression type}
      (expression_type : ExpressionHasType source context expression type) :
      FormTyping source control context (.expression expression true) context
  | assignValue {assignment operator value}
      (assignment_type : SourceAssignmentHasType source context assignment
        operator value) :
      FormTyping source control context (.assignValue assignment operator value)
        context
  | assignBitNot {assignment}
      (assignment_type : SourceBitNotAssignmentValid source context assignment) :
      FormTyping source control context (.assignBitNot assignment) context
  | ifWithoutElse {condition thenBody thenFinal thenFacts}
      (condition_type : ExpressionHasType source context condition .bool)
      (then_type : StatementsHaveType source control context thenBody thenFinal
        thenFacts) :
      FormTyping source control context (.ifThen condition thenBody none) context
  | ifWithElse {condition thenBody elseBody thenFinal elseFinal thenFacts elseFacts}
      (condition_type : ExpressionHasType source context condition .bool)
      (then_type : StatementsHaveType source control context thenBody thenFinal
        thenFacts)
      (else_type : StatementsHaveType source control context elseBody elseFinal
        elseFacts) :
      FormTyping source control context
        (.ifThen condition thenBody (some elseBody)) context
  | block {body innerFinal bodyFacts}
      (body_type : StatementsHaveType source control context body innerFinal
        bodyFacts) :
      FormTyping source control context (.block body) context
  | matchWithoutDefault {resolution scrutineeType caseFacts}
      (default_eq : resolution.defaultBody = none)
      (scrutinee_type : ExpressionHasType source context resolution.scrutinee
        scrutineeType)
      (cases_type : MatchCasesHaveType source control context scrutineeType
        resolution.cases caseFacts) :
      FormTyping source control context (.matchWith resolution) context
  | matchWithDefault {resolution defaultBody scrutineeType caseFacts defaultFinal
      defaultFacts}
      (default_eq : resolution.defaultBody = some defaultBody)
      (scrutinee_type : ExpressionHasType source context resolution.scrutinee
        scrutineeType)
      (cases_type : MatchCasesHaveType source control context scrutineeType
        resolution.cases caseFacts)
      (default_type : StatementsHaveType source control context defaultBody
        defaultFinal defaultFacts) :
      FormTyping source control context (.matchWith resolution) context
  | forLoop {initializer condition post body loopContext postContext bodyFinal
      bodyFacts}
      (initializer_type : ForItemsHaveType source control context initializer
        loopContext)
      (condition_type : ExpressionHasType source loopContext condition .bool)
      (body_type : StatementsHaveType source control.enterLoop loopContext body
        bodyFinal bodyFacts)
      (post_type : ForItemsHaveType source control.enterLoop loopContext post
        postContext) :
      FormTyping source control context
        (.forLoop initializer condition post body) context
  | whileLoop {condition body bodyFinal bodyFacts}
      (condition_type : ExpressionHasType source context condition .bool)
      (body_type : StatementsHaveType source control.enterLoop context body
        bodyFinal bodyFacts) :
      FormTyping source control context (.whileLoop condition body) context
  | breakStmt (allowed : control.loopAllowed) :
      FormTyping source control context .breakStmt context
  | continueStmt (allowed : control.loopAllowed) :
      FormTyping source control context .continueStmt context

theorem contains
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {facts : StatementFacts}
    (typing : StatementHasType source control context statement finalContext
      facts) : exists node, ContainsStatement source statement node := by
  cases typing <;> exact ⟨_, by assumption⟩

theorem formTyping
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {facts : StatementFacts}
    (typing : StatementHasType source control context statement finalContext
      facts) : exists node,
      ContainsStatement source statement node /\
        FormTyping source control context node.form finalContext := by
  cases typing with
  | letUninitialized contains form_eq monomorphic generalizes extension type_eq =>
      exact ⟨_, contains, form_eq ▸ .letUninitialized monomorphic extension⟩
  | letInitialized contains form_eq initializer_type monomorphic generalizes
      extension type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .letInitialized initializer_type monomorphic extension⟩
  | letInitializedGeneralized contains form_eq polymorphic
      requirements_well_formed generalizes initializer_type extension type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .letInitializedGeneralized polymorphic
          requirements_well_formed generalizes initializer_type extension⟩
  | returnUnit contains form_eq return_type_eq type_eq =>
      exact ⟨_, contains, form_eq ▸ .returnUnit return_type_eq⟩
  | returnValue contains form_eq value_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .returnValue value_type⟩
  | expressionValue contains form_eq expression_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .expressionValue expression_type⟩
  | expressionDiscard contains form_eq expression_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .expressionDiscard expression_type⟩
  | assignValue contains form_eq assignment_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .assignValue assignment_type⟩
  | assignBitNot contains form_eq assignment_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .assignBitNot assignment_type⟩
  | ifWithoutElse contains form_eq condition_type then_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .ifWithoutElse condition_type then_type⟩
  | ifWithElse contains form_eq condition_type then_type else_type type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .ifWithElse condition_type then_type else_type⟩
  | block contains form_eq body_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .block body_type⟩
  | matchWithoutDefault contains form_eq default_eq scrutinee_type cases_type
      requirements_eq exhaustive merged type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .matchWithoutDefault default_eq scrutinee_type cases_type⟩
  | matchWithDefault contains form_eq default_eq scrutinee_type cases_type
      default_type requirements_eq merged type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .matchWithDefault default_eq scrutinee_type cases_type
          default_type⟩
  | forLoop contains form_eq initializer_type condition_type body_type post_type
      type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .forLoop initializer_type condition_type body_type post_type⟩
  | whileLoop contains form_eq condition_type body_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .whileLoop condition_type body_type⟩
  | breakStmt contains form_eq allowed type_eq =>
      exact ⟨_, contains, form_eq ▸ .breakStmt allowed⟩
  | continueStmt contains form_eq allowed type_eq =>
      exact ⟨_, contains, form_eq ▸ .continueStmt allowed⟩

theorem runtimeContextFields
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {facts : StatementFacts}
    (typing : StatementHasType source control context statement finalContext
      facts) : RuntimeContextFields context finalContext := by
  cases typing <;> try { exact .refl _ }
  all_goals exact RuntimeContextFields.ofBinderExtends (by assumption)

end StatementHasType

namespace StatementsHaveType

theorem runtimeContextFields
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statements : List StatementId}
    {facts : BodyFacts}
    (typing : StatementsHaveType source control context statements finalContext
      facts) : RuntimeContextFields context finalContext := by
  induction statements generalizing context finalContext facts with
  | nil =>
      cases typing
      exact .refl _
  | cons statement statements induction =>
      cases typing with
      | singleton head =>
          exact
            Solcore.SourceSemantics.Dynamic.StatementHasType.runtimeContextFields
              head
      | cons head tail =>
          exact
            (Solcore.SourceSemantics.Dynamic.StatementHasType.runtimeContextFields
              head).trans (induction tail)

end StatementsHaveType

namespace ForItemHasType

theorem runtimeContextFields
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {item : ForItemForm}
    (typing : ForItemHasType source control context item finalContext) :
    RuntimeContextFields context finalContext := by
  cases typing <;> try { exact .refl _ }
  all_goals exact RuntimeContextFields.ofBinderExtends (by assumption)

end ForItemHasType

namespace ForItemsHaveType

theorem runtimeContextFields
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {items : List ForItemForm}
    (typing : ForItemsHaveType source control context items finalContext) :
    RuntimeContextFields context finalContext := by
  induction items generalizing context finalContext with
  | nil =>
      cases typing
      exact .refl _
  | cons item items induction =>
      cases typing with
      | cons head tail =>
          exact
            (Solcore.SourceSemantics.Dynamic.ForItemHasType.runtimeContextFields
              head).trans (induction tail)

end ForItemsHaveType

/-- Control outcomes preserve exactly the information observable after the
statement sequence finishes.  Only ordinary fallthrough reaches the end of
the statically typed sequence, so only it carries the final lexical scope.
Return carries its declared value type.  Break and continue discard their
intermediate lexical scope when the enclosing construct restores its entry
environment. -/
inductive ControlOutcomePreserved
    (context finalContext : Context) (heap : Heap) (returnType : Ty) :
    ControlOutcome -> Prop where
  | fallthrough {environment : Environment}
      (agrees : EnvironmentAgrees heap finalContext.locals environment) :
      ControlOutcomePreserved context finalContext heap returnType
        (.fallthrough environment)
  | returned {value : Value}
      (typed : ValueHasType context heap value returnType) :
      ControlOutcomePreserved context finalContext heap returnType
        (.returned value)
  | breaking {environment : Environment} :
      ControlOutcomePreserved context finalContext heap returnType
        (.breaking environment)
  | continuing {environment : Environment} :
      ControlOutcomePreserved context finalContext heap returnType
        (.continuing environment)

namespace ControlOutcomePreserved

theorem retargetTerminal
    {context leftFinal rightFinal : Context} {heap : Heap} {returnType : Ty}
    {outcome : ControlOutcome}
    (terminal : TerminalControl outcome)
    (preserved : ControlOutcomePreserved context leftFinal heap returnType
      outcome) :
    ControlOutcomePreserved context rightFinal heap returnType outcome := by
  cases terminal <;> cases preserved
  · exact .returned (by assumption)
  · exact .breaking
  · exact .continuing

theorem transportEntry
    {source target finalContext : Context} {heap : Heap} {returnType : Ty}
    {outcome : ControlOutcome}
    (fields : RuntimeContextFields target source)
    (target_closed : target.typeParameters = [])
    (target_variables_closed : target.typeVariables = [])
    (target_residual_variables_open :
      target.residualTypeVariables = true)
    (preserved : ControlOutcomePreserved source finalContext heap returnType
      outcome) :
    ControlOutcomePreserved target finalContext heap returnType outcome := by
  cases preserved with
  | fallthrough agrees => exact .fallthrough agrees
  | returned typed =>
      exact .returned (typed.transportClosed fields.signatures.symm
        (fields.targetClosed target_closed) target_closed
        (fields.targetVariablesClosed target_variables_closed)
        target_residual_variables_open)
  | breaking => exact .breaking
  | continuing => exact .continuing

theorem restore
    {outer inner innerFinal : Context} {heap : Heap} {returnType : Ty}
    {outerEnvironment : Environment} {outcome : ControlOutcome}
    (fields : RuntimeContextFields outer inner)
    (outer_closed : outer.typeParameters = [])
    (outer_variables_closed : outer.typeVariables = [])
    (outer_residual_variables_open :
      outer.residualTypeVariables = true)
    (outer_agrees :
      EnvironmentAgrees heap outer.locals outerEnvironment)
    (preserved : ControlOutcomePreserved inner innerFinal heap returnType
      outcome) :
    ControlOutcomePreserved outer outer heap returnType
      (restoreControl outerEnvironment outcome) := by
  cases preserved with
  | fallthrough agrees => exact .fallthrough outer_agrees
  | returned typed =>
      exact .returned (typed.transportClosed fields.signatures.symm
        (fields.targetClosed outer_closed) outer_closed
        (fields.targetVariablesClosed outer_variables_closed)
        outer_residual_variables_open)
  | breaking => exact .breaking
  | continuing => exact .continuing

end ControlOutcomePreserved

/-- Successful statement sequencing preserves heap typing, location types,
the declared return type, and the ordinary final lexical context. -/
structure StatementEvaluationPreserved
    (context finalContext : Context) (returnType : Ty)
    (before after : Heap) (outcome : ControlOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  outcome_typed :
    ControlOutcomePreserved context finalContext after returnType outcome

/-- Recursive statement-sequence interface used by blocks, branches, loops,
closures, and catalog body invocation. -/
def StatementsExecutionPreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  forall control context environment before statements staticFinalContext
      runtimeFinalContext outcome after facts,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    StatementsHaveType source control context statements staticFinalContext facts ->
    StatementsExecute program context evidence source environment before
      statements runtimeFinalContext outcome after ->
    StatementEvaluationPreserved context staticFinalContext control.returnType
      before after outcome

/-- Recursive `for`-header interface. -/
def ForItemsExecutionPreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  forall control context environment before items staticFinalContext
      runtimeFinalContext finalEnvironment after,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    ForItemsHaveType source control context items staticFinalContext ->
    ForItemsExecute program context evidence source environment before items
      runtimeFinalContext finalEnvironment after ->
    runtimeFinalContext = staticFinalContext /\
      HeapWellTyped context after /\ HeapTypesExtend before after /\
        EnvironmentAgrees after staticFinalContext.locals finalEnvironment

/-- Recursive while-loop interface. -/
def WhileExecutionPreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  forall (control : ControlContext) context environment before condition body finalContext outcome
      after bodyFinal bodyFacts,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    ExpressionHasType source context condition .bool ->
    StatementsHaveType source control.enterLoop context body bodyFinal bodyFacts ->
    WhileExecutes program context evidence source environment before condition
      body finalContext outcome after ->
    StatementEvaluationPreserved context finalContext control.returnType before
      after outcome

/-- Recursive iterative `for`-loop interface after its initializer. -/
def ForLoopExecutionPreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  forall (control : ControlContext) context environment before condition post body finalContext
      outcome after postContext bodyFinal bodyFacts,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    ExpressionHasType source context condition .bool ->
    ForItemsHaveType source control.enterLoop context post postContext ->
    StatementsHaveType source control.enterLoop context body bodyFinal bodyFacts ->
    ForLoopExecutes program context evidence source environment before condition
      post body finalContext outcome after ->
    StatementEvaluationPreserved context finalContext control.returnType before
      after outcome

namespace StatementExecutes

theorem preservesWith
    {program : Program} {context finalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statement : StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (runtime : SourceRuntimeValid program context source)
    (expression_preserves :
      ExpressionExecutionPreserves program context evidence source environment)
    (statements_preserves : StatementsExecutionPreserves program evidence source)
    (for_items_preserves : ForItemsExecutionPreserves program evidence source)
    (while_preserves : WhileExecutionPreserves program evidence source)
    (for_loop_preserves : ForLoopExecutionPreserves program evidence source)
    (evidence_covers : evidence.Covers context)
    (environment_agrees :
      EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : StatementHasType source control context statement finalContext facts)
    (execution : StatementExecutes program context evidence source environment
      before statement finalContext outcome after) :
    StatementEvaluationPreserved context finalContext control.returnType before
      after outcome := by
  have graph : OccurrenceGraphWellFormed source := runtime.graph
  have owner : context.currentDeclaration = some source.owner := runtime.owner
  have closed : context.typeParameters = [] := runtime.closed
  have variables_closed : context.typeVariables = [] := runtime.variables_closed
  have residual_variables_open : context.residualTypeVariables = true :=
    runtime.residual_variables_open
  rcases
      Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
    ⟨typedNode, typed_contains, form_typing⟩
  cases execution with
  | letUninitialized contains form_eq runtime_monomorphic extension allocate =>
      have node_eq := containsStatement_unique runtime.graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letUninitialized monomorphic static_extension =>
          cases static_extension
          have allocation_extension := HeapTypesExtend.of_allocation allocate
          have after_typed := before_typed.allocate (.none _) allocate
          exact {
            heap_typed := after_typed
            heap_extends := allocation_extension
            outcome_typed := .fallthrough
              (.cons allocate.reads_new rfl
                (.ordinary runtime_monomorphic rfl)
                (environment_agrees.mono allocation_extension))
          }
  | letInitialized contains form_eq evaluate runtime_monomorphic extension allocate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letInitialized initializer_type monomorphic static_extension =>
          cases static_extension
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed initializer_type evaluate with
            ⟨value_typed, middle_typed, evaluation_extension⟩
          have allocation_extension := HeapTypesExtend.of_allocation allocate
          have after_typed := middle_typed.allocate (.some value_typed) allocate
          exact {
            heap_typed := after_typed
            heap_extends := evaluation_extension.trans allocation_extension
            outcome_typed := .fallthrough
              (.cons allocate.reads_new rfl
                (.ordinary runtime_monomorphic rfl)
                ((environment_agrees.mono evaluation_extension).mono
                  allocation_extension))
          }
      | letInitializedGeneralized polymorphic _requirements_well_formed
          _generalizes initializer_type static_extension =>
          exact (polymorphic runtime_monomorphic).elim
  | letInitializedGeneralized contains form_eq captures runtime_polymorphic
      extension allocate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letInitialized initializer_type static_monomorphic static_extension =>
          exact (runtime_polymorphic static_monomorphic).elim
      | letInitializedGeneralized static_polymorphic
          requirements_well_formed generalizes initializer_type
          static_extension =>
          have function_typed := captures.wellTyped runtime
            environment_agrees static_polymorphic requirements_well_formed
            generalizes initializer_type static_extension
          have allocation_extension :=
            HeapTypesExtend.of_generalized_allocation allocate
          have after_typed := before_typed.allocateGeneralized function_typed
            allocate
          cases static_extension
          exact {
            heap_typed := after_typed
            heap_extends := allocation_extension
            outcome_typed := .fallthrough
              (.cons allocate.reads_new
                (by simpa only using (congrArg
                  (fun retained : TypedBinder => retained.scheme.body)
                  captures.binder_eq))
                (.generalized rfl
                  (by simpa only using (congrArg TypedBinder.id
                    captures.binder_eq))
                  (by simpa only using (congrArg TypedBinder.scheme
                    captures.binder_eq)))
                (environment_agrees.mono allocation_extension))
          }
  | returnUnit contains form_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | returnUnit return_type_eq =>
          exact {
            heap_typed := before_typed
            heap_extends := .refl before
            outcome_typed := .returned (return_type_eq ▸ ValueHasType.unit)
          }
  | returnValue contains form_eq evaluate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | returnValue value_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed value_type evaluate with
            ⟨value_typed, after_typed, extension⟩
          exact {
            heap_typed := after_typed
            heap_extends := extension
            outcome_typed := .returned value_typed
          }
  | expression contains form_eq evaluate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | expressionValue expression_type | expressionDiscard expression_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed expression_type evaluate with
            ⟨value_typed, after_typed, extension⟩
          exact {
            heap_typed := after_typed
            heap_extends := extension
            outcome_typed := .fallthrough (environment_agrees.mono extension)
          }
  | assignValue contains form_eq assignment_executes =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | assignValue assignment_type =>
          rcases assignment_executes.preserves expression_preserves evidence_covers
              environment_agrees before_typed assignment_type with
            ⟨after_typed, extension⟩
          exact {
            heap_typed := after_typed
            heap_extends := extension
            outcome_typed := .fallthrough (environment_agrees.mono extension)
          }
  | assignBitNot contains form_eq assignment_executes =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | assignBitNot assignment_type =>
          rcases assignment_executes.bitNotPreserves expression_preserves
              evidence_covers environment_agrees before_typed assignment_type with
            ⟨after_typed, extension⟩
          exact {
            heap_typed := after_typed
            heap_extends := extension
            outcome_typed := .fallthrough (environment_agrees.mono extension)
          }
  | ifTrue contains form_eq condition_evaluates body_executes =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | ifWithoutElse condition_type then_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨condition_typed, middle_typed, condition_extension⟩
          rcases statements_preserves _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers (environment_agrees.mono condition_extension)
              middle_typed then_type body_executes with
            body_preserved
          rcases body_preserved with
            ⟨body_heap_typed, body_extension, body_outcome⟩
          have extension := condition_extension.trans body_extension
          exact {
            heap_typed := body_heap_typed
            heap_extends := extension
            outcome_typed := body_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
      | ifWithElse condition_type then_type else_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨condition_typed, middle_typed, condition_extension⟩
          rcases statements_preserves _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers (environment_agrees.mono condition_extension)
              middle_typed then_type body_executes with
            body_preserved
          rcases body_preserved with
            ⟨body_heap_typed, body_extension, body_outcome⟩
          have extension := condition_extension.trans body_extension
          exact {
            heap_typed := body_heap_typed
            heap_extends := extension
            outcome_typed := body_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | ifFalseWithoutElse contains form_eq condition_evaluates =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | ifWithoutElse condition_type then_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨condition_typed, after_typed, extension⟩
          exact {
            heap_typed := after_typed
            heap_extends := extension
            outcome_typed := .fallthrough (environment_agrees.mono extension)
          }
  | ifFalseWithElse contains form_eq condition_evaluates body_executes =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | ifWithElse condition_type then_type else_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed condition_type condition_evaluates with
            ⟨condition_typed, middle_typed, condition_extension⟩
          rcases statements_preserves _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers (environment_agrees.mono condition_extension)
              middle_typed else_type body_executes with
            body_preserved
          rcases body_preserved with
            ⟨body_heap_typed, body_extension, body_outcome⟩
          have extension := condition_extension.trans body_extension
          exact {
            heap_typed := body_heap_typed
            heap_extends := extension
            outcome_typed := body_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | block contains form_eq body_executes =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | block body_type =>
          rcases statements_preserves _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers environment_agrees before_typed body_type
              body_executes with
            body_preserved
          rcases body_preserved with
            ⟨body_heap_typed, extension, body_outcome⟩
          exact {
            heap_typed := body_heap_typed
            heap_extends := extension
            outcome_typed := body_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | matchArm contains form_eq scrutinee_contains scrutinee_evaluates
      allocate_hidden select binders_eq values_eq binders_extend
      allocate_bindings execute =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
        scrutineeNode location armBody bindings binders values armContext
        armFinalContext armEnvironment bound outcome
      have preserve_arm :
          ∀ {scrutineeType caseFacts},
            ExpressionHasType source context resolution.scrutinee scrutineeType ->
            MatchCasesHaveType source control context scrutineeType
              resolution.cases caseFacts ->
            StatementEvaluationPreserved context context control.returnType
              before after (restoreControl environment outcome) := by
        intro scrutineeType caseFacts scrutinee_type cases_type
        rcases expression_preserves _ _ _ _ _ evidence_covers
            environment_agrees before_typed scrutinee_type
            scrutinee_evaluates with
          ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
        rcases scrutinee_type.stored_type with
          ⟨staticScrutineeNode, static_contains, static_type_eq⟩
        have scrutinee_node_eq := containsExpression_unique
          graph.nodeOccurrencesUnique static_contains scrutinee_contains
        subst staticScrutineeNode
        have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
            scrutineeNode.type := static_type_eq ▸ scrutinee_typed
        have hidden_heap_typed := scrutinee_heap_typed.allocate
          (.some hidden_value_typed) allocate_hidden
        have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
        have scrutinee_hidden_typed := scrutinee_typed.mono hidden_extension
        rcases select.armPreserves cases_type scrutinee_hidden_typed with
          ⟨staticBinders, staticArmContext, staticFinalContext, armFacts,
            bindings_typed, static_binders_eq, static_binders_extend,
            arm_type, binders_monomorphic⟩
        have dynamic_static_binders : binders = staticBinders :=
          binders_eq.trans static_binders_eq
        have static_binders_extend' :
            BindersExtend source.owner context binders staticArmContext := by
          rw [dynamic_static_binders]
          exact static_binders_extend
        have arm_context_eq :=
          Solcore.SourceSemantics.Dynamic.BindersExtend.functional
            binders_extend static_binders_extend'
        subst armContext
        have values_typed : ValuesHaveTypes context hiddenHeap values
            (staticBinders.map fun binder => binder.scheme.body) := by
          rw [values_eq, ← static_binders_eq, List.map_map]
          change ValuesHaveTypes context hiddenHeap (bindings.map Prod.snd)
            (bindings.map fun binding => binding.1.scheme.body)
          exact bindings_typed.unzip
        have values_typed_dynamic : ValuesHaveTypes context hiddenHeap values
            (binders.map fun binder => binder.scheme.body) := by
          simpa [dynamic_static_binders] using values_typed
        have bound_heap_typed :=
          Solcore.SourceSemantics.Dynamic.BindersAllocate.preservesHeapTyping
            hidden_heap_typed values_typed_dynamic allocate_bindings
        have bound_extension := allocate_bindings.extendsHeapTypes
        have arm_environment_agrees :=
          allocate_bindings.preservesEnvironmentAgreement
            static_binders_extend'
            (by
              intro binder member
              exact binders_monomorphic binder
                (by simpa [dynamic_static_binders] using member))
            (environment_agrees.mono
              (scrutinee_extension.trans hidden_extension))
        have arm_fields :=
          Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields
            static_binders_extend
        have arm_closed := arm_fields.targetClosed closed
        have arm_owner :
            staticArmContext.currentDeclaration = some source.owner := by
          rw [arm_fields.currentDeclaration]
          exact owner
        have arm_evidence := arm_fields.covers evidence_covers
        have bound_heap_at_arm := bound_heap_typed.transportClosed
          arm_fields.signatures closed arm_closed variables_closed
          (arm_fields.targetResidualVariablesOpen residual_variables_open)
        rcases statements_preserves _ _ _ _ _ _ _ _ _ _
            (runtime.transport arm_fields) arm_evidence arm_environment_agrees bound_heap_at_arm
            arm_type execute with
          arm_preserved
        rcases arm_preserved with
          ⟨arm_heap_typed, arm_extension, arm_outcome⟩
        have arm_heap_at_outer := arm_heap_typed.transportClosed
          arm_fields.signatures.symm arm_closed closed
          (arm_fields.targetVariablesClosed variables_closed)
          residual_variables_open
        have extension := ((scrutinee_extension.trans hidden_extension).trans
          bound_extension).trans arm_extension
        exact {
          heap_typed := arm_heap_at_outer
          heap_extends := extension
          outcome_typed := arm_outcome.restore arm_fields closed variables_closed
            residual_variables_open
            (environment_agrees.mono extension)
        }
      cases form_typing with
      | matchWithoutDefault default_eq scrutinee_type cases_type =>
          exact preserve_arm scrutinee_type cases_type
      | matchWithDefault default_eq scrutinee_type cases_type default_type =>
          exact preserve_arm scrutinee_type cases_type
  | matchDefault contains form_eq scrutinee_contains scrutinee_evaluates
      allocate_hidden select execute =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
        scrutineeNode location defaultBody runtimeDefaultFinal outcome
      cases form_typing with
      | matchWithoutDefault default_eq scrutinee_type cases_type =>
          have selected_default := select.defaultBody_eq
          rw [default_eq] at selected_default
          contradiction
      | matchWithDefault default_eq scrutinee_type cases_type default_type =>
          have selected_default := select.defaultBody_eq
          rw [selected_default] at default_eq
          cases default_eq
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed scrutinee_type
              scrutinee_evaluates with
            ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
          rcases scrutinee_type.stored_type with
            ⟨staticScrutineeNode, static_contains, static_type_eq⟩
          have scrutinee_node_eq := containsExpression_unique
            graph.nodeOccurrencesUnique static_contains scrutinee_contains
          subst staticScrutineeNode
          have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
              scrutineeNode.type := static_type_eq ▸ scrutinee_typed
          have hidden_heap_typed := scrutinee_heap_typed.allocate
            (.some hidden_value_typed) allocate_hidden
          have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
          rcases statements_preserves _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers
              (environment_agrees.mono
                (scrutinee_extension.trans hidden_extension))
              hidden_heap_typed default_type execute with
            body_preserved
          rcases body_preserved with
            ⟨body_heap_typed, body_extension, body_outcome⟩
          have extension := (scrutinee_extension.trans hidden_extension).trans
            body_extension
          exact {
            heap_typed := body_heap_typed
            heap_extends := extension
            outcome_typed := body_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates
      allocate_hidden select =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      rename_i scrutineeHeap dynamicNode resolution scrutinee scrutineeNode
        location
      cases form_typing with
      | matchWithoutDefault default_eq scrutinee_type cases_type =>
          rcases expression_preserves _ _ _ _ _ evidence_covers
              environment_agrees before_typed scrutinee_type
              scrutinee_evaluates with
            ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
          rcases scrutinee_type.stored_type with
            ⟨staticScrutineeNode, static_contains, static_type_eq⟩
          have scrutinee_node_eq := containsExpression_unique
            graph.nodeOccurrencesUnique static_contains scrutinee_contains
          subst staticScrutineeNode
          have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
              scrutineeNode.type := static_type_eq ▸ scrutinee_typed
          have hidden_heap_typed := scrutinee_heap_typed.allocate
            (.some hidden_value_typed) allocate_hidden
          have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
          have extension := scrutinee_extension.trans hidden_extension
          exact {
            heap_typed := hidden_heap_typed
            heap_extends := extension
            outcome_typed := .fallthrough (environment_agrees.mono extension)
          }
      | matchWithDefault default_eq scrutinee_type cases_type default_type =>
          have selected_default := select.noBranch_defaultBody_eq
          rw [default_eq] at selected_default
          contradiction
  | forLoop contains form_eq initializer_executes iterate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      rename_i initialized dynamicNode initializer condition post body
        runtimeLoopContext loopFinalContext loopEnvironment outcome
      cases form_typing with
      | forLoop initializer_type condition_type body_type post_type =>
          rcases for_items_preserves _ _ _ _ _ _ _ _ _ runtime
              evidence_covers environment_agrees before_typed initializer_type
              initializer_executes with
            ⟨loop_context_eq, initialized_typed, initializer_extension,
              loop_environment_agrees⟩
          subst runtimeLoopContext
          have loop_fields :=
            Solcore.SourceSemantics.Dynamic.ForItemsHaveType.runtimeContextFields
              initializer_type
          have loop_closed := loop_fields.targetClosed closed
          have loop_owner := loop_fields.currentDeclaration.trans owner
          have loop_evidence := loop_fields.covers evidence_covers
          have initialized_at_loop := initialized_typed.transportClosed
            loop_fields.signatures closed loop_closed variables_closed
            (loop_fields.targetResidualVariablesOpen residual_variables_open)
          rcases for_loop_preserves _ _ _ _ _ _ _ _ _ _ _ _ _
              (runtime.transport loop_fields) loop_evidence loop_environment_agrees
              initialized_at_loop condition_type post_type body_type iterate with
            ⟨loop_heap_typed, loop_extension, loop_outcome⟩
          have loop_heap_at_outer := loop_heap_typed.transportClosed
            loop_fields.signatures.symm loop_closed closed
            (loop_fields.targetVariablesClosed variables_closed)
            residual_variables_open
          have extension := initializer_extension.trans loop_extension
          exact {
            heap_typed := loop_heap_at_outer
            heap_extends := extension
            outcome_typed := loop_outcome.restore loop_fields closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | whileLoop contains form_eq iterate =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | whileLoop condition_type body_type =>
          rcases while_preserves _ _ _ _ _ _ _ _ _ _ _ runtime
              evidence_covers environment_agrees before_typed condition_type
              body_type iterate with
            ⟨loop_heap_typed, extension, loop_outcome⟩
          exact {
            heap_typed := loop_heap_typed
            heap_extends := extension
            outcome_typed := loop_outcome.restore (.refl context) closed
              variables_closed residual_variables_open
              (environment_agrees.mono extension)
          }
  | breakStmt contains form_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | breakStmt allowed =>
          exact {
            heap_typed := before_typed
            heap_extends := .refl before
            outcome_typed := .breaking
          }
  | continueStmt contains form_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | continueStmt allowed =>
          exact {
            heap_typed := before_typed
            heap_extends := .refl before
            outcome_typed := .continuing
          }

end StatementExecutes

/-- Preservation certificate for one successfully invoked body. -/
structure BodyInvocationPreserved
    (bodyInstance : BodyInstance) (before after : Heap)
    (result : Value) : Prop where
  result_typed :
    ValueHasType bodyInstance.context after result bodyInstance.resultType
  heap_typed : HeapWellTyped bodyInstance.context after
  heap_extends : HeapTypesExtend before after

/-- Whole-language preservation is stated as one proof object.  Its fields
quantify over the actual mutually recursive big-step judgments, so every
expression, statement, loop, call, match, assignment, and staging-neutral
source rule is inside the contract.  The local lemmas above discharge the
primitive, coercion, pattern, place, allocation, and builtin cases. -/
structure WholeLanguagePreservation (program : Program) : Prop where
  program_well_formed : ProgramWellFormed program
  expression : forall context evidence source environment before after id value
      type,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    ExpressionHasType source context id type ->
    ExpressionEvaluates program context evidence source environment before id
      value after ->
    ExpressionEvaluationPreserved context before after value type
  statements : forall context evidence source environment before after statements
      outcome control staticFinalContext runtimeFinalContext facts,
    SourceRuntimeValid program context source ->
    evidence.Covers context ->
    EnvironmentAgrees before context.locals environment ->
    HeapWellTyped context before ->
    StatementsHaveType source control context statements staticFinalContext facts ->
    StatementsExecute program context evidence source environment before
      statements runtimeFinalContext outcome after ->
    StatementEvaluationPreserved context staticFinalContext control.returnType
      before after outcome
  invoke : forall bodyInstance evidence before after arguments result
      inputTypes lexicalContext facts,
    BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext
      facts ->
    evidence.Covers bodyInstance.context ->
    HeapWellTyped bodyInstance.context before ->
    ValuesHaveTypes bodyInstance.context before arguments inputTypes ->
    BodyInvokes program bodyInstance evidence before arguments result after ->
    BodyInvocationPreserved bodyInstance before after result

namespace BodyInstanceTypingCertificate

/-- The whole static certificate supplies exactly the invariants needed to
start the mutually recursive source-preservation proof at an instantiated
body. -/
theorem sourceRuntimeValid
    {program : Program} {bodyInstance : BodyInstance}
    {inputTypes : List Ty} {lexicalContext : Context} {facts : BodyFacts}
    (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes
      lexicalContext facts) :
    SourceRuntimeValid program bodyInstance.context bodyInstance.source := {
  signatures := certificate.signatures_eq
  graph := certificate.graph_closed.wellFormed
  owner := certificate.owner
  closed := certificate.type_parameters_empty
  variables_closed := certificate.type_variables_empty
  residual_variables_open := certificate.residual_type_variables_open
  ledger := certificate.requirement_ledger.idsUnique
}

end BodyInstanceTypingCertificate

namespace StatementRoots

theorem filterMap_eq
    {roots : List NodeId} {statements : List StatementId}
    (extracted : StatementRoots roots statements) :
    (roots.filterMap fun root =>
      match root with
      | .statement statement => some statement
      | .expression _ => none) = statements := by
  induction extracted with
  | nil => rfl
  | cons tail induction => simp [induction]

end StatementRoots

end Solcore.SourceSemantics.Dynamic
