import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-! Independent literal correspondence under arbitrary ambient definitions.
Numeric requirement validity and a covering evidence environment remain
explicit source entry conditions. Literal code neither reads nor changes any
Core environment or heap, including administrative closures in other cells. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

structure ContextValid (solved : List SolvedRequirement) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Prop where
  ledger : context.solvedRequirements = solved
  valid : RequirementLedgerWellFormed context
  covers : evidence.Covers context

private theorem ContextValid.proves {solved : List SolvedRequirement} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} (valid : ContextValid solved context evidence)
    {id : RequirementId} {predicate : ProgramPredicate}
    (member : ∃ entry ∈ solved, entry.id = id ∧ entry.predicate = predicate) :
    RequirementProves context id predicate := by
  obtain ⟨entry, member, identifier, predicate⟩ := member
  have present : entry ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
  exact ⟨entry, ⟨present, identifier⟩, predicate, valid.valid.entriesValid entry present⟩

private theorem word_constructs {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteralValue} {value : Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) : Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Word.ofNatModulo value.val = value := by apply Fin.ext; exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem Atomic.not_local {form : ExpressionForm} (atomic : Atomic form) :
    ∀ name binder, form ≠ .reference name (.local binder) := by
  cases atomic <;> intros <;> intro impossible <;> cases impossible

private theorem Literal.atomic {solved node type code} (literal : Literal solved node type code) : Atomic node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .bool _ _
  | word value form _ _ _ _ => rw [form]; exact .word _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integer _ _

private theorem Literal.coercions {solved node type code} (literal : Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic.not_local _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic.not_local _ _ form)

private theorem Literal.form_unique {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {left right : Dynamic.Value}
    (first : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions left firstHeap)
    (second : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions right secondHeap) :
    left = right ∧ firstHeap = secondHeap := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at first second
    cases first with | tuple _ elements pack =>
      cases elements
      cases pack
      cases second with | tuple _ elements pack => cases elements; cases pack; exact ⟨rfl, rfl⟩
  | bool value form _ _ _ => rw [form] at first second; cases first; cases second; exact ⟨rfl, rfl⟩
  | word value form _ _ _ _ =>
    rw [form] at first second
    cases first with | literal _ first =>
      cases second with | literal _ second => exact ⟨first.functional second, rfl⟩
  | resolvedWord form _ | resolvedInteger form _ =>
    rw [form] at first second
    cases first with | integerLiteral _ first =>
      cases second with | integerLiteral _ second => exact ⟨first.functional second, rfl⟩

private theorem Literal.excludes_fault {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid solved context evidence)
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after) : False := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at fault
    cases fault with | tuple _ failed => cases failed
  | bool value form _ _ _ | word value form _ _ _ _ => rw [form] at fault; cases fault
  | resolvedWord form metadata | resolvedInteger form metadata =>
    rw [form] at fault
    cases fault with | integerRequirement _ unavailable =>
      obtain ⟨_, produced⟩ := Dynamic.RequirementProves.produces_of_covers valid.covers (valid.proves metadata.solved)
      exact produced.excludes_unavailable valid.valid.idsUnique unavailable

/-- Atomic code is well typed in every ambient definition environment. -/
theorem Literal.hasType {solved node type code} (literal : Literal solved node type code)
    (context : Core.Context) (definitions : DataEnvironment) :
    HasType context code (LanguageResult.resultType type) definitions := by
  cases literal with
  | unit => exact .inRight .word .unit
  | bool => exact .inRight .word .bool
  | word | resolvedWord => exact .inRight .word .word
  | resolvedInteger => exact .inRight .word .integer

/-- Each static literal constructs a source value and a native value directly.
The environment renaming and both heaps are arbitrary. -/
theorem Literal.evaluates {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid solved context evidence)
    (source : TypedSource) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (mapping : LocationMap) (world : StoreTyping) (native : Environment) (store : Store) (ξ : Renaming) :
    ∃ sourceValue coreValue,
      Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions sourceValue heap ∧
      ValueRep checked registry functions mapping world node.type sourceValue coreValue type ∧
      Evaluates native store (code.rename ξ) (.inRight .word coreValue) store := by
  cases literal with
  | unit form type requirements coercions =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .tuple rfl .nil .nil, .unit, .inRight .unit⟩
  | bool value form type requirements coercions =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .builtinBoolean rfl, .bool _, .inRight .bool⟩
  | word value form type requirements coercions meaning =>
    rw [form, type, requirements, coercions]
    exact ⟨_, _, .literal rfl (word_constructs meaning), .word _, .inRight .word⟩
  | @resolvedWord value resolution validated form metadata =>
    have constructs : Dynamic.ResolvedIntegerLiteralConstructs context value resolution (.word (Word.ofNatModulo resolution.rawValue)) := by
      cases resolution with | mk raw target requirement =>
        have targetEq := metadata.targetType
        dsimp only at targetEq
        subst target
        exact .word metadata.meaning (valid.proves metadata.solved)
    rw [form, metadata.nodeType, metadata.requirements, metadata.coercions, metadata.value]
    exact ⟨_, _, .integerLiteral rfl constructs, .word _, .inRight .word⟩
  | @resolvedInteger value resolution validated form metadata =>
    have constructs : Dynamic.ResolvedIntegerLiteralConstructs context value resolution (.integer (Int.ofNat resolution.rawValue)) := by
      cases resolution with | mk raw target requirement =>
        have targetEq := metadata.targetType
        dsimp only at targetEq
        subst target
        exact .integer metadata.meaning (valid.proves metadata.solved)
    rw [form, metadata.nodeType, metadata.requirements, metadata.coercions, metadata.value]
    exact ⟨_, _, .integerLiteral rfl constructs, .integer _, .inRight .integer⟩

/-- Universal literal preservation has no child execution hypothesis. -/
theorem preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (valid : ContextValid solved context evidence)
    {source : TypedSource} (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨other, otherFound, literal⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates functions program context evidence valid source environment before mapping world actual store ξ
  have contains := lookupExpression?_sound found
  have result : outcome = .value sourceValue ∧ after = before := by
    cases trace with
    | value trace =>
      have actualRaw := evaluation_raw unique contains literal.atomic literal.coercions trace
      obtain ⟨rfl, rfl⟩ := literal.form_unique actualRaw raw
      exact ⟨rfl, rfl⟩
    | fault fault =>
      exact False.elim (literal.excludes_fault valid (fault_raw unique contains literal.atomic literal.coercions fault))
  obtain ⟨rfl, rfl⟩ := result
  exact ⟨coreValue |> Value.inRight .word, store, mapping, world, evaluated, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _⟩

/-- A completed native literal always reconstructs its independent source
execution, without assuming any source trace beforehand. -/
theorem reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (valid : ContextValid solved context evidence)
    (source : TypedSource) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  intro scope id lowered receipt node found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluation
  obtain ⟨other, otherFound, literal⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates functions program context evidence valid source environment before mapping world actual store ξ
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated evaluation
  have trace : Dynamic.ExpressionEvaluates program context evidence source environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [literal.coercions]
    exact .nil
  exact ⟨.value sourceValue, before, mapping, world, .value trace, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiterals
