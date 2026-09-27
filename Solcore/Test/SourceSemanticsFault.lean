import Solcore.SourceSemantics

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic

/-- A structurally absent occurrence produces the public fault outcome. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ExpressionEvaluatesOutcome program context evidence source environment heap id
      (.fault (.missingExpression id)) heap :=
  .fault (.missing missing)

/-- An empty lexical frame gives a positive unbound-local derivation even
when the occurrence owns a nonempty generalized requirement segment. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (heap : Heap) (binder : Resolved.LocalId) (name : String)
    (owned : RequirementId) :
    ExpressionFormFaults program context evidence source [] heap
      (.reference name (.local binder)) [owned] [] (.unboundLocal binder) heap := by
  exact .localUnbound (owned := [owned]) rfl (.nil binder)

/-- A location past the empty heap is dangling without negating heap reads. -/
example (location : Location) : Heap.Dangling ⟨[]⟩ location := by
  exact .nil location.index

/-- A nonempty generalized requirement segment does not hide a dangling
local location. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (binder : Resolved.LocalId) (name : String) (owned : RequirementId) :
    ExpressionFormFaults program context evidence source
      [(binder, ⟨0⟩)] ⟨[]⟩
      (.reference name (.local binder)) [owned] []
      (.danglingLocation ⟨0⟩) ⟨[]⟩ := by
  exact .localDangling (owned := [owned]) rfl .head (.nil 0)

/-- A generalized local reports the first failed owned requirement after its
runtime substitution has been selected. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (binder : Resolved.LocalId)
    (owned : List RequirementId) (location : Location) (cell : Cell)
    (function : GeneralizedClosure) (substitution : TypeSystem.Substitution)
    (failed : RequirementId)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .reference name (.local binder))
    (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
    (lookup : Environment.LooksUp environment binder location)
    (read : Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function)
    (context_fields : RuntimeContextFields function.definitionContext context)
    (selection : LocalSchemeRuntimeSelection context function.binder
      node.rawType owned substitution)
    (fault : RequirementsFault context evidence owned
      (instantiateLocalSchemePredicates substitution function.binder) failed) :
    ExpressionFaults program context evidence source environment heap id
      (.unsatisfiedRequirement failed) heap := by
  exact .generalizedLocalRequirement contains form_eq layout lookup read
    descriptor context_fields selection fault

/-- Once generalized-local instantiation succeeds, its result coercion path
can still expose a concrete semantic fault. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (before after : Heap) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (binder : Resolved.LocalId)
    (owned : List RequirementId) (location : Location) (cell : Cell)
    (function : GeneralizedClosure) (substitution : TypeSystem.Substitution)
    (produced : EvidenceEnvironment) (reason : SemanticFault)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .reference name (.local binder))
    (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
    (lookup : Environment.LooksUp environment binder location)
    (read : Heap.Reads before location cell)
    (descriptor : cell.generalized = some function)
    (context_fields : RuntimeContextFields function.definitionContext context)
    (instantiation : LocalSchemeRuntimeInstantiation context evidence
      function.binder node.rawType owned substitution produced)
    (fault : CoercionPathFaults program context evidence before node.coercions
      (.closure (function.instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) reason after) :
    ExpressionFaults program context evidence source environment before id
      reason after := by
  exact .generalizedLocalCoercion contains form_eq layout lookup read descriptor
    context_fields instantiation fault

/-- Primitive operand faults name the exact source operator. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (heap : Heap) :
    UnaryOperationFaults program context evidence heap .logicalNot [] .unit
      (.invalidUnaryOperand .logicalNot) heap := by
  apply UnaryOperationFaults.primitive
  exact .logicalNot (by simp [BooleanValue])

/-- Non-callable values fault before any body can be postulated. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap (.bool true) []
      .notCallable heap := by
  exact .notCallable (by simp [CallableValue])

/-- Builtins expose their retained parameter count in arity faults. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) []
      (.argumentArityMismatch 2 0) heap := by
  apply CallableFaults.builtinArity
  decide

/-- Correct-arity builtin calls diagnose the first wrong argument type. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) [.bool true, .integer 0]
      (.typeMismatch .integer .bool) heap := by
  apply CallableFaults.builtinArgumentType
  · decide
  · apply ValuesFirstTypeMismatch.head (.bool true)
    decide

/-- Missing retained evidence names the exact unsatisfied requirement. -/
example (context : SourceSemantics.Context) (evidence : EvidenceEnvironment)
    (id : RequirementId) (missing : RequirementMissing context id) :
    RequirementUnavailable context evidence id :=
  .missing missing

/-- Closing retained evidence successfully rules out a closure fault for the
same open evidence tree. -/
example (environment : EvidenceEnvironment)
    (openEvidence closedEvidence : TraitEvidence)
    (closes : EvidenceCloses environment openEvidence closedEvidence)
    (fault : EvidenceClosureFaults environment openEvidence) : False :=
  closes.excludes_fault fault

/-- Every finite retained evidence tree has a constructive runtime outcome:
either all assumptions close or a missing assumption is identified. -/
example (environment : EvidenceEnvironment) (openEvidence : TraitEvidence) :
    (∃ closedEvidence,
      EvidenceCloses environment openEvidence closedEvidence) ∨
      EvidenceClosureFaults environment openEvidence :=
  EvidenceCloses.exists_or_fault environment openEvidence

/-- A dictionary covering the static context materializes a closed, valid
evidence tree from every valid open tree. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (goal : ProgramPredicate)
    (openEvidence : TraitEvidence)
    (covers : EvidenceEnvironment.Covers context environment)
    (valid : EvidenceValid context.assumptions
      context.signatures.resolutionRules goal openEvidence) :
    ∃ closedEvidence,
      EvidenceCloses environment openEvidence closedEvidence ∧
        EvidenceValid [] context.signatures.resolutionRules goal
          closedEvidence :=
  SourceSemantics.Dynamic.EvidenceValid.close_of_covers covers valid

/-- Under the static requirement-identity invariant, successful materialization
and runtime unavailability are mutually exclusive. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (id : RequirementId)
    (predicate : ProgramPredicate) (closedEvidence : TraitEvidence)
    (unique : RequirementIdsUnique context)
    (produces : RequirementProducesEvidence context environment id predicate
      closedEvidence)
    (unavailable : RequirementUnavailable context environment id) : False :=
  produces.excludes_unavailable unique unavailable

/-- A successfully materialized requirement spine cannot also report a first
fault for the same ordered identity/predicate inputs. -/
example (context : SourceSemantics.Context)
    (caller produced : EvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate) (failed : RequirementId)
    (unique : RequirementIdsUnique context)
    (produces : RequirementsProduceEnvironment context caller requirements
      predicates produced)
    (fault : RequirementsFault context caller requirements predicates failed) :
    False :=
  produces.excludes_fault unique fault

/-- A well-formed requirement ledger and valid caller dictionary classify each
stable identity as either materializable or concretely unavailable. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment) (id : RequirementId)
    (ledger : RequirementLedgerWellFormed context)
    (valid : environment.Valid context.signatures.resolutionRules) :
    (∃ predicate evidence,
      RequirementProducesEvidence context environment id predicate evidence) ∨
      RequirementUnavailable context environment id :=
  requirement_produces_or_unavailable ledger valid id

/-- Static requirement sequence validity plus a covering dictionary is enough
to materialize the exact ordered runtime evidence environment. -/
example (context : SourceSemantics.Context)
    (environment : EvidenceEnvironment)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate)
    (covers : environment.Covers context)
    (proves : RequirementSequenceProves context requirements predicates) :
    ∃ produced,
      RequirementsProduceEnvironment context environment requirements
        predicates produced :=
  SourceSemantics.Dynamic.RequirementSequenceProves.produces_of_covers
    covers proves

/-- A malformed pattern is an explicit metadata fault, not a failed match. -/
example (context : SourceSemantics.Context) (value : Value)
    (arm : TypedMatchCase) (rest : List TypedMatchCase)
    (malformed : PatternMalformed context arm.pattern) :
    MatchCasesPatternFault context value (arm :: rest) :=
  .head malformed

/-- The closed Core-representable residualization boundary is the sole
staging-fault introduction rule. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (before after : Heap) (id : ExpressionId)
    (value : Int)
    (evaluates : ExpressionEvaluates program context evidence source environment
      before id (.integer value) after) :
    RuntimeExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault .stagingViolation) after :=
  .stagingViolation evaluates (.integer value)

/-- Grouping preserves the exact child fault and its heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (inner : ExpressionId)
    (missing : ExpressionMissing source inner) :
    ExpressionFormFaults program context evidence source environment heap
      (.group inner) [] [] (.missingExpression inner) heap := by
  exact ExpressionFormFaults.group (coercions := []) rfl (.missing missing)

/-- Statement faults are reified as `ControlOutcome.fault`. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : StatementId)
    (missing : StatementMissing source id) :
    StatementExecutesOutcome program context evidence source environment heap id
      context (.fault (.missingStatement id)) heap :=
  .fault (.missing missing)

/-- A generalized statement binder reaches the explicit runtime boundary
before its initializer is evaluated. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : StatementId)
    (node : StatementNode) (binder : TypedBinder)
    (initializer : Option ExpressionId)
    (contains : ContainsStatement source id node)
    (form_eq : node.form = .letDecl binder initializer)
    (polymorphic : binder.scheme.quantified ≠ [])
    (unsupported : GeneralizedInitializerUnsupported source binder initializer) :
    StatementFaults program context evidence source environment heap id
      (.unsupportedPolymorphicBinder binder.id) heap := by
  exact .polymorphicLet contains form_eq polymorphic unsupported

/-- The same explicit boundary applies to generalized binders in a `for`
header. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (binder : TypedBinder)
    (initializer : Option ExpressionId)
    (polymorphic : binder.scheme.quantified ≠ [])
    (unsupported : GeneralizedInitializerUnsupported source binder initializer) :
    ForItemFaults program context evidence source environment heap
      (.letDecl binder initializer)
      (.unsupportedPolymorphicBinder binder.id) heap := by
  exact .polymorphicLet polymorphic unsupported

/-- A `for`-header vector stops at its first faulting item and preserves that
item's exact fault and heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ForItemsFault program context evidence source environment heap
      [.expression id] context (.missingExpression id) heap := by
  exact .head (.expression (.missing missing))

/-- Loop-condition failure is observable before any body iteration. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    WhileFaults program context evidence source environment heap id []
      (.missingExpression id) heap := by
  exact .condition (.missing missing)

end Solcore.Test.SourceSemanticsFault
