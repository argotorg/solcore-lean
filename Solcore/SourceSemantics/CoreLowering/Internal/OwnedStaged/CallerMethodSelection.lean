import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
import Solcore.SourceSemantics.Staging.RecursiveScope
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls

/-!
# Staged bounds: caller method selection

Closed and generic method selection, policy and method profiles of general callers, and caller head handlers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyCallerMethodExclusion
/-! Legacy policy hooks decline operator methods at the actual reached Source
occurrences. These facts are derived from compiler receipts, not execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

private theorem method_calls_legacy_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body callFuel compilation
      values source callScope callId reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : MethodCalls compiler root) (tree : Syntax source rootId) : Syntax source callId := by
  induction path with
  | here sequence children => exact tree
  | @method_child scope id otherFuel code types outer sequence children child childCode member inside ih =>
    exact ih (syntax_child tree outer.metadata.found (outer.argument_references (List.of_mem_zip member).1))
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    exact ih (syntax_child tree actual.found (by simp [form, ExpressionForm.references]))
  | @tuple_child scope id node tupleIds types codes header sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @builtin_child scope id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree outer.metadata.found (by
      simp [outer.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @direct_child scope id otherCallee otherIds instantiation otherFuel code types outer calleeTyped application sequence children child childCode member inside ih =>
    exact False.elim (no_direct_of_syntax _ tree outer (.here calleeTyped application sequence children))
  | @call_child scope id otherCallee otherIds metadata otherFuel code types outer sequence children child childCode member inside ih =>
    apply ih
    apply syntax_child tree outer.found
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      simp [outer.originalForm, ExpressionForm.references]
    · simp [outer.originalForm, ExpressionForm.references, (List.of_mem_zip remaining).1]
  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))

  | @index_base scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih
  | @index_key scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    exact False.elim (no_indexes_of_syntax _ tree header keyFound form sourceType (.here firstTree secondTree))


theorem no_methods_of_policy_on {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    (tree : Syntax source id) {roots : List NodeId}
    (reached : CallableLambdaBodyReachability.Reaches source roots (.expression id))
    (profile : PolicyOn policy compilation readFuel values source scope reasonAt
      (fun child => CallableLambdaBodyReachability.Reaches source roots (.expression child))) : NoMethods root := by
  intro fuel callScope callId callCode compiler path
  have syntaxTree := method_calls_legacy_syntax path tree
  have scopeEq := method_calls_scope path
  have bypass := profile.special callId (method_calls_reached path reached) syntaxTree
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel + 1)
  rw [← scopeEq] at bypass
  have impossible := compiler.special.symm.trans bypass
  cases impossible

theorem no_methods_of_policy {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    (tree : Syntax source id)
    (profile : PolicyFor policy compilation readFuel values source scope reasonAt) : NoMethods root :=
  no_methods_of_policy_on root tree (.root (by simp))
    (profile.on (fun child => CallableLambdaBodyReachability.Reaches source [.expression id] (.expression child)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
/-! A finite closed method catalog discharges method formation and dictionary
selection from actual checker provenance. Caller dictionaries may be nonempty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  parameters : ∀ implementation, implementation ∈ program.signatures.implementations →
    implementation.parameters = []
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ program.signatures.traits →
      implementation.methodAssumptions trait method = []

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Every field follows from the selected implementation and full materializer,
including empty method dictionaries and original source occurrence uniqueness. -/
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have domain := chosen.domain
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember
  have substitution : receipt.method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have assumptions : receipt.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have empty : (bodyInstance receipt.program receipt.method).context.assumptions = [] := assumptions
  have covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ :=
      CallableCoercionEvidenceOrigins.materialized_operator receipt.operator.materialized
    have dictionary : receipt.operator.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : receipt.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique, empty⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
/-! Method selection with arbitrary actual implementation substitutions.
The retained catalog restricts method assumptions, independently of parameters. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ program.signatures.traits →
      implementation.methodAssumptions trait method = []

/-- Existing closed catalogs retain their original API and embed directly. -/
theorem Catalog.of_closed {program : CheckedProgram}
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog program) :
    Catalog program := ⟨catalog.formed, catalog.assumptions⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Shared static suffix after the selected raw range is derived. -/
theorem support_of_range     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have assumptions : receipt.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have empty : (bodyInstance receipt.program receipt.method).context.assumptions = [] := assumptions
  have covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ :=
      CallableCoercionEvidenceOrigins.materialized_operator receipt.operator.materialized
    have dictionary : receipt.operator.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : receipt.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique, empty⟩

/-- Actual original parent typing, current requirement identities and compiler
selection derive the complete raw range before instantiating the Source body. -/
theorem selection_support     (checked : CallableMethodBodyCoherence.Checked receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionSupport receipt selected := by
  have goalAdmitted := CallableIndexedOwnedPreparedStagedMethodSelectionGoal.admissible
    receipt selected signatures ledger assumptions unique idsUnique typed
  have formed := catalog.formed _ selected.certificate.selected.implementationMember
    _ selected.certificate.selected.methodMember
  have range := CallableIndexedOwnedPreparedStagedMethodSelectionRanges.of_selected
    selected.certificate.selected wellFormed formed signatures goalAdmitted
  exact support_of_range receipt checked wellFormed catalog selected range

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
/-! The retained production policy supplies the recursive caller profile.
Every supported Source occurrence has genuine metadata exclusions; the actual
contextual and evidence hooks then delegate before entering their special paths.
Original Source and Code.view need separate global metadata proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {source : TypedSource}
  {directSites : DeclarationInstantiation → Prop}

inductive SupportedForm : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : SupportedForm form
  | proxy (inner : TypeSystem.Ty) : SupportedForm (.proxy inner)
  | read (name : String) (binder : Resolved.LocalId) : SupportedForm (.reference name (.local binder))
  | unary (operator : Solcore.Syntax.UnaryOp) (operand : ExpressionId) : SupportedForm (.unary operator operand)
  | binary (left : ExpressionId) (operator : Solcore.Syntax.BinaryOp) (right : ExpressionId) : SupportedForm (.binary left operator right)
  | index (base key : ExpressionId) : SupportedForm (.index base key)
  | conditional (condition yes no : ExpressionId) : SupportedForm (.conditional condition yes no)
  | group (inner : ExpressionId) : SupportedForm (.group inner)
  | tuple (ids : List ExpressionId) : SupportedForm (.tuple ids)
  | constructor (instantiation : DataConstructorInstantiation) (ids : List ExpressionId) :
      SupportedForm (.constructor instantiation ids)
  | builtin (callee : ExpressionId) (ids : List ExpressionId) (function : BuiltinFunctionId) :
      SupportedForm (.call callee ids (.builtinFunction function))
  | direct (callee : ExpressionId) (ids : List ExpressionId) (instantiation : DeclarationInstantiation) :
      SupportedForm (.call callee ids (.declaration instantiation))
  | call (callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
      SupportedForm (.call callee ids (.indirect metadata))

theorem syntax_node {id : ExpressionId}
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites) :
    ∃ node, source.lookupExpression? id = some node ∧ SupportedForm node.form := by
  cases tree with
  | leaf product =>
    cases product with
    | literal found atomic => exact ⟨_, found, .literal atomic⟩
    | read found form =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .read _ _
    | group found form _child =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .group _
    | pair found form _first _second =>
      refine ⟨_, found, ?_⟩
      rw [form]
      exact .tuple _
  | proxy found form =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .proxy _
  | group found form _child =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .group _
  | tuple found form _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .tuple _
  | constructor found form _ranges _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .constructor _ _
  | builtin found form _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .builtin _ _ _
  | direct found form _monomorphic _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .direct _ _ _
  | call found form _callee _children =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .call _ _ _

  | unary found form _child =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .unary _ _
  | binary found form _first _second =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .binary _ _ _
  | index found form _keyFound _first _second =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .index _ _
  | conditional found form _condition _then _else =>
    refine ⟨_, found, ?_⟩
    rw [form]
    exact .conditional _ _ _

/-- These exclusions cover every occurrence in the supported global grammar.
They contain no compiler action, runtime state or child execution law. -/
structure MetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource)
    (directSites : DeclarationInstantiation → Prop := CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic) : Prop where
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

structure MetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop)
    (directSites : DeclarationInstantiation → Prop := CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.requirements = []
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

/-- Native literals keep their genuine selected evidence rows. Their compiler
validator authenticates those rows; other admitted expressions retain empty
requirements. This is a metadata condition, not an execution premise. -/
structure NativeMetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource)
    (directSites : DeclarationInstantiation → Prop := CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic) : Prop where
  requirements : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  coercions : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

structure NativeMetadataOn (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named) (source : TypedSource) (allowed : ExpressionId → Prop)
    (directSites : DeclarationInstantiation → Prop := CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic) : Prop where
  requirements : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  coercions : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  directCaller : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → named.specialized.assumptions = []
  localRead : ∀ id, allowed id → CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites →
    ∀ node, source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem NativeMetadataFor.of_ordinary (metadata : MetadataFor prepared named source directSites) :
    NativeMetadataFor prepared named source directSites :=
  ⟨fun id tree node found => .inl (metadata.requirements id tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.directCaller, metadata.localRead⟩

theorem NativeMetadataOn.of_ordinary {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed directSites) : NativeMetadataOn prepared named source allowed directSites :=
  ⟨fun id reached tree node found => .inl (metadata.requirements id reached tree node found),
    metadata.coercions, metadata.initializer, metadata.arguments, metadata.directCaller, metadata.localRead⟩

theorem NativeMetadataFor.on (metadata : NativeMetadataFor prepared named source directSites)
    (allowed : ExpressionId → Prop) : NativeMetadataOn prepared named source allowed directSites :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.directCaller id tree,
   fun id _ tree => metadata.localRead id tree⟩

theorem MetadataFor.on (metadata : MetadataFor prepared named source directSites)
    (allowed : ExpressionId → Prop) : MetadataOn prepared named source allowed directSites :=
  ⟨fun id _ tree => metadata.requirements id tree,
   fun id _ tree => metadata.coercions id tree,
   fun id _ tree => metadata.initializer id tree,
   fun id _ tree => metadata.arguments id tree,
   fun id _ tree => metadata.directCaller id tree,
   fun id _ tree => metadata.localRead id tree⟩

theorem contextual_same {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (supported : SupportedForm node.form)
    (ordinary : ∀ name binder, node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram (context prepared named).plan
      prepared.base.locals (context prepared named).owner none source id = .ok source := by
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic =>
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | read name binder =>
    unfold SourceCoreGeneralFunctions.contextualSource
    rw [found]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [form]
    dsimp only
    rw [ordinary name binder form]
    rfl
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | tuple => simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  | call => simp [SourceCoreGeneralFunctions.contextualSource, found, form]

theorem evidence_none
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) {id : ExpressionId} {node : ExpressionNode}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node) (supported : SupportedForm node.form)
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution) (coercions : node.coercions = [])
    (arguments : ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = [])
    (directClosed : ∀ callee ids instantiation,
      node.form = .call callee ids (.declaration instantiation) → caller.assumptions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller current child budget
      source scope id reasonAt callables = .ok none := by
  rcases requirements with requirements | ⟨literal, resolution, form⟩
  ·
    have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [requirements, coercions]
      rfl
    generalize form : node.form = shape at supported
    cases supported with
    | literal atomic =>
      cases atomic <;>
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | read =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | proxy | index | unary | binary | conditional | group | constructor | builtin =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | tuple =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]
    | direct callee ids instantiation =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, requirements, coercions,
        directClosed callee ids instantiation form]
    | call callee ids metadata =>
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        arguments callee ids metadata form]
  · have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some node.requirements := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [coercions]
      change (if node.requirements.length < 0 then none else
        if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
          some (node.requirements.take (node.requirements.length - 0)) else none) = some node.requirements
      simp
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, coercions]

private theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : NativeMetadataFor prepared named source directSites)
    {id : ExpressionId}
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.requirements id tree node found) (metadata.coercions id tree node found)
    (metadata.arguments id tree node found) (metadata.directCaller id tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_for_native
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : NativeMetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt directSites := by
  constructor
  · intro id tree child budget
    rw [recipe.lowerSpecial]
    exact special_none compilation rootFuel metadata tree child budget scope reasonAt
  · intro id tree
    obtain ⟨node, found, supported⟩ := syntax_node tree
    have sameSource := contextual_same found supported (metadata.localRead id tree node found)
    rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · exact recipe.lowerRead
  · exact recipe.leafLowerer


theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt directSites := by
  exact recipe_policy_for_native recipe (NativeMetadataFor.of_ordinary metadata) scope reasonAt

/-- The full profile is proved from one actual retained production recipe.
The independent raw typing, scope declarations and CallsReady remain separate. -/
theorem retained_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : MetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt directSites := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_for recipe metadata scope reasonAt

theorem retained_policy_for_native
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : NativeMetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt directSites := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_for_native recipe metadata scope reasonAt


private theorem special_none_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed directSites)
    {id : ExpressionId}
    (admitted : allowed id)
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax source id directSites)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id admitted tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.requirements id admitted tree node found) (metadata.coercions id admitted tree node found)
    (metadata.arguments id admitted tree node found) (metadata.directCaller id admitted tree node found)
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id admitted tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id admitted tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem recipe_policy_on_native
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed directSites := by
  constructor
  · intro id admitted tree child budget
    rw [recipe.lowerSpecial]
    exact special_none_on compilation rootFuel metadata admitted tree child budget scope reasonAt
  · intro id admitted tree
    obtain ⟨node, found, supported⟩ := syntax_node tree
    have sameSource := contextual_same found supported (metadata.localRead id admitted tree node found)
    rw [recipe.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  · exact recipe.lowerRead
  · exact recipe.leafLowerer


theorem recipe_policy_on
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn policy (context prepared named)
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed directSites := by
  exact recipe_policy_on_native recipe (NativeMetadataOn.of_ordinary metadata) scope reasonAt

/-- The full profile is proved from one actual retained production recipe.
The independent raw typing, scope declarations and CallsReady remain separate. -/
theorem retained_policy_on
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    {allowed : ExpressionId → Prop}
    (metadata : MetadataOn prepared named source allowed directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed directSites := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_on recipe metadata scope reasonAt


theorem retained_policy_on_native
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    {allowed : ExpressionId → Prop}
    (metadata : NativeMetadataOn prepared named source allowed directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) source scope reasonAt allowed directSites := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, recipe, sameCompilation⟩ := retained
  rw [sameCompilation]
  exact recipe_policy_on_native recipe metadata scope reasonAt



/-- Original and viewed Sources each retain the global Syntax quantifier.
Reached-node metadata transport alone does not discharge either global input. -/
theorem retained_paired_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (original : MetadataFor prepared named function.source directSites)
    (viewed : MetadataFor prepared named code.view directSites)
    (originalScope viewScope : SourceCoreLocalCell.Scope)
    (originalReasonAt viewReasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) function.source originalScope originalReasonAt directSites ∧
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) code.view viewScope viewReasonAt directSites :=
  ⟨retained_policy_for retained original originalScope originalReasonAt,
    retained_policy_for retained viewed viewScope viewReasonAt⟩

/-- Registry provenance transports the full original Source profile to every
actual selected invocation scope, without changing its global Syntax quantifier. -/
theorem retained_selected_policy_for
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code prepared function parameterScope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : MetadataFor prepared named function.source directSites)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor code.policy code.compilation
      prepared.fuel (SourceCoreCompatibleValues.Context.initial checked) child.source scope reasonAt directSites := by
  rw [stages.source selected]
  exact retained_policy_for retained metadata scope reasonAt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
/-! Actual named policy recipes retain declaration and operator-method evidence
hooks. Other recursive forms keep their original native metadata restrictions. The compiler
step returns the same static receipt and original ordered child callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm syntax_node contextual_same evidence_none)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Supported Child)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named} {source : TypedSource}
  {directSites : DeclarationInstantiation → Prop}

/-- Declaration and operator calls may carry additional ordinary requirement IDs.
Their actual compiler branch authenticates every retained dictionary entry. -/
structure MetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : Named) (source : TypedSource) (directSites : DeclarationInstantiation → Prop) : Prop where
  requirements : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      (∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)) ∨ OperatorForm node.form
  coercions : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem MetadataFor.of_native
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor prepared named source directSites) :
    MetadataFor prepared named source directSites := by
  refine ⟨?_, metadata.coercions, metadata.initializer, metadata.arguments, metadata.localRead⟩
  intro id tree node found
  rcases metadata.requirements id tree node found with empty | literal
  · exact .inl empty
  · exact .inr (.inl literal)

theorem MetadataFor.non_direct_requirements (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect) (primitive : tree.NonOperator)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution := by
  rcases metadata.requirements id tree node found with empty | literal | ⟨callee, ids, instantiation, form⟩ | operator
  · exact .inl empty
  · exact .inr literal
  · exact False.elim (ordinary node found callee ids instantiation form)
  · exact False.elim (primitive node found operator)

/-- The original contextual step agrees with the actual evidence lowerer at a
named declaration call. No second compiler policy is selected. -/
theorem direct_hook
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  have same := contextual_same found (form ▸ SupportedForm.direct callee ids instantiation)
    (metadata.localRead id tree node found)
  rw [recipe.lowerSpecial]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [same, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none]
  cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
  | error error => rfl
  | ok output => cases output <;> simp [form]

theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect) (primitive : tree.NonOperator)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.non_direct_requirements tree ordinary primitive found) (metadata.coercions id tree node found)
    (metadata.arguments id tree node found)
    (fun callee ids instantiation form => False.elim (ordinary node found callee ids instantiation form))
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | proxy | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem read_policy
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  rw [recipe.readExpression]
  simp only [sameSource, bind, Except.bind]
  rfl

/-- The authentic accepted expression either took the ordinary branch or
returned the exact code supplied by its evidence hook. -/
theorem accepted_direct_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  have hook := direct_hook recipe metadata tree found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt
  cases selectedHook : policy.lowerSpecial? with
  | none =>
    simp only [selectedHook] at hook
    exact .inl hook.symm
  | some lower =>
    simp only [selectedHook] at hook accepted
    rw [hook] at accepted
    cases action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) (Child policy body fuel (context prepared named))
        (fuel + 1) source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => rw [action] at accepted; cases accepted
    | ok output =>
      cases output with
      | none => exact .inl rfl
      | some actual =>
        rw [action] at accepted
        cases Except.ok.inj accepted
        exact .inr rfl

theorem operator_hook
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  all_goals
   have supported : SupportedForm node.form := by rw [form]; first | exact .unary _ _ | exact .binary _ _ _
   have same := contextual_same found supported (metadata.localRead id tree node found)
   rw [recipe.lowerSpecial]
   unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
   simp only [same, bind, Except.bind, found, pure, Except.pure,
     metadata.initializer id tree, Option.filter_none]
   cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
       ((representation prepared).atContext named.signature.key []).expressions.projectType
       named.specialized (context prepared named) child budget source scope id reasonAt
       (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
   | error error => rfl
   | ok output => cases output <;> simp [form]


theorem accepted_operator_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  have hook := operator_hook recipe metadata tree found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt
  cases selectedHook : policy.lowerSpecial? with
  | none =>
    simp only [selectedHook] at hook
    exact .inl hook.symm
  | some lower =>
    simp only [selectedHook] at hook accepted
    rw [hook] at accepted
    cases action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) (Child policy body fuel (context prepared named))
        (fuel + 1) source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => rw [action] at accepted; cases accepted
    | ok output =>
      cases output with
      | none => exact .inl rfl
      | some actual =>
        rw [action] at accepted
        cases Except.ok.inj accepted
        exact .inr rfl


theorem ordinary_requirements {node : ExpressionNode} (coercions : node.coercions = []) :
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some node.requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [coercions]
  change (if node.requirements.length < 0 then none else
    if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
      some (node.requirements.take (node.requirements.length - 0)) else none) = some node.requirements
  simp

theorem operator_none_requirements
    {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {budget : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {callables : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (coercions : node.coercions = [])
    (accepted : SourceCoreEvidence.lowerWithProjector program project caller compilation child budget
      source scope id reasonAt callables = .ok none) : node.requirements = [] := by
  have ordinary := ordinary_requirements coercions
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  all_goals
    unfold SourceCoreEvidence.lowerWithProjector at accepted
    simp only [found, form, ordinary, bind, Except.bind, pure, Except.pure,
      Bool.and_true, Bool.not_false, Bool.or_false] at accepted
    split at accepted
    · rename_i bypass
      simp only [coercions, List.isEmpty_nil, Bool.true_and, Bool.and_false, Bool.not_false, Bool.and_true] at bypass
      exact List.isEmpty_iff.mp bypass
    · repeat first | cases accepted | split at accepted | contradiction

theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    (supported : ∀ instantiation, directSites instantiation → Supported (context prepared named).plan instantiation)
    (metadata : MetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    MethodStepPolicyFor policy (context prepared named) prepared.fuel
      (.initial checked) source scope reasonAt directSites := by
  constructor
  · intro id _ tree ordinary primitive child budget
    rw [recipe.lowerSpecial]
    exact special_none compilation rootFuel metadata tree ordinary primitive child budget scope reasonAt
  · intro id _ tree _
    exact read_policy recipe metadata tree
  · exact recipe.lowerRead
  · exact recipe.leafLowerer
  · intro body fuel id callee ids instantiation node lowered _ found form site children accepted
    have tree := GeneralSyntax.direct found form site children
    rcases accepted_direct_action recipe metadata tree found form accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported found form
        (supported instantiation site) (fun child budget => by
          exact (direct_hook recipe metadata tree found form child budget scope reasonAt).trans
            (CallableCallEvidenceCertificates.direct_bypass found form requirements
              (metadata.coercions id tree node found) assumptions))
        (read_policy recipe metadata tree) accepted
    · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form authentic
      have projected := actual.suffix.outputProjection
      change SourceCoreCompatibleDataExpressions.projectType checked
        (.occurrence node.id.occurrence) node.type = .ok lowered.type at projected
      have actualPolicy : CallableCoercionExpressionCertificates.Direct prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []).expressions.projectType
          named.specialized (context prepared named) (Child policy body fuel (context prepared named))
          (fuel + 1) source scope id callee ids instantiation reasonAt policy.callables node lowered := by
        rw [callables]
        exact actual
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_evidence
        (supported instantiation site) (metadata.coercions id tree node found)
        (CompatibleExpressionReads.projectType_of_accepted projected) actualPolicy accepted
  · intro body fuel id node lowered _ found operator tree accepted
    have form : (∃ op operand, node.form = .unary op operand) ∨
        (∃ op left right, node.form = .binary left op right) := by
      cases formEq : node.form <;> simp [formEq, OperatorForm] at operator
      · exact .inl ⟨_, _, rfl⟩
      · exact .inr ⟨_, _, _, rfl⟩
    rcases accepted_operator_action recipe metadata tree found form accepted with bypass | authentic
    · have empty := operator_none_requirements found form (metadata.coercions id tree node found) bypass
      refine .inl ?_
      intro child budget
      apply (operator_hook recipe metadata tree found form child budget scope reasonAt).trans
      apply evidence_none prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) child budget scope reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found
      · rcases form with ⟨op, operand, form⟩ | ⟨op, left, right, form⟩
        all_goals rw [form]; first | exact .unary _ _ | exact .binary _ _ _
      · exact .inl empty
      · exact metadata.coercions id tree node found
      · exact metadata.arguments id tree node found
      · intro callee ids instantiation actualForm
        rcases form with ⟨op, operand, form⟩ | ⟨op, left, right, form⟩
        all_goals simp [form] at actualForm
    · have nonempty : node.requirements ≠ [] := by
        intro empty
        have none := evidence_none prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []).expressions.projectType
          named.specialized (context prepared named) (Child policy body fuel (context prepared named)) (fuel + 1)
          scope reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found
          (by rcases form with ⟨op, operand, form⟩ | ⟨op, left, right, form⟩; all_goals rw [form]; first | exact .unary _ _ | exact .binary _ _ _)
          (.inl empty) (metadata.coercions id tree node found) (metadata.arguments id tree node found)
          (by intro callee ids instantiation actualForm; rcases form with ⟨op, operand, form⟩ | ⟨op, left, right, form⟩; all_goals simp [form] at actualForm)
        cases none.symm.trans authentic
      obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted found form
        (ordinary_requirements (metadata.coercions id tree node found)) nonempty authentic
      have projected := actual.suffix.outputProjection
      change SourceCoreCompatibleDataExpressions.projectType checked
        (.occurrence node.id.occurrence) node.type = .ok lowered.type at projected
      have actualPolicy : CallablePreparedMethodSelection.Operator prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []).expressions.projectType
          named.specialized (context prepared named) (Child policy body fuel (context prepared named))
          (fuel + 1) source scope id reasonAt policy.callables node lowered := by
        rw [callables]
        exact actual
      exact .inr (CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.of_evidence
        (metadata.coercions id tree node found) (CompatibleExpressionReads.projectType_of_accepted projected)
        actualPolicy ((operator_hook recipe metadata tree found form _ _ scope reasonAt).trans authentic) accepted)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
/-! Internal call-head continuations for the shared structural expression proof.
Each continuation is indexed by an actual compiler receipt and its path in the
root certificate. Concrete invocation theorems construct these continuations
from strictly smaller body proofs and the reached protected state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions) (stages : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
  (budget : Nat)
  (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
    invocation.source context reasonAt scope id code)

def PreservesDirect : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def PreservesMethod : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def PreservesIndirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      PreservesBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      PreservesAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsDirect : Prop :=
  ∀ {fuel scope id callee ids instantiation code types} (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id callee ids instantiation reasonAt code),
    DirectCalls compiler root →
    DirectDeclarationCalleeValid context invocation.source callee instantiation →
    DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsMethod : Prop :=
  ∀ {fuel scope id code types} (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body fuel compilation
      (.initial compiled.compatible.checked) invocation.source scope id reasonAt code),
    MethodCalls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) scope compiler.arguments types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope (compiler.arguments.zip compiler.codes)) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

def ReflectsIndirect : Prop :=
  ∀ {fuel scope id callee ids metadata code types} (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
      invocation.source scope id callee ids metadata reasonAt code),
    Calls compiler root →
    DataExpressionSequence.Tree invocation.source
      (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes →
    ∀ size, size ≤ budget →
      ReflectsBelow bridge context model stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) faults size →
      ReflectsAt bridge context model stages invocation (Point scope id code) faults size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments
/-! The original coerced declaration call retains its raw input/result typing
and full evidence partition. Argument execution uses the original Source scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Port EvidenceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)

include receipt in
theorem source_types (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ∃ types, DirectDeclarationCalleeValid context invocation.source callee instantiation ∧
      DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates ∧
      ExpressionsHaveTypes invocation.source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst actualNode
    rw [← rawEq, receipt.form] at raw
    cases raw with
    | directCall calleeValid application argumentsTyped =>
      cases application with
      | intro signatureMember admissible declaration parameters result functionType predicates =>
        exact ⟨_, calleeValid, .intro signatureMember admissible declaration parameters result functionType rfl,
          argumentsTyped⟩

include receipt in
theorem children {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before node.form node.requirements node.coercions outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values name evidence,
      size = Staging.Recursive.Size.stepSize [sequenceSize, invocationSize] ∧
      Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages sequenceSize
        invocation context environment before ids (.values values) argumentsHeap ∧
      Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements node.coercions
        instantiation.predicates evidence ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages invocationSize
        invocation context argumentsHeap (.global ⟨instantiation,evidence⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Staging.Recursive.Size.stepSize [sequenceSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages sequenceSize
        invocation context environment before ids (.fault failure) after) := by
  rw [receipt.form] at trace
  cases trace with
  | rawAtomicValue atomic _ | rawAtomicFault atomic _ => cases atomic
  | rawDirectApplied occurrence valid children produced invoked =>
      exact .inl ⟨_,_,_,_,_,_,rfl,occurrence,valid,children,produced,invoked⟩
  | rawDirectArgumentsFault _ children => exact .inr ⟨_,_,rfl,rfl,children⟩

include port in
theorem callee_receipt
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation) :
    ∃ name, Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  cases calleeValid with
  | intro contains form admissible _ requirements coercions =>
    refine ⟨_, ⟨_, contains, form, requirements, coercions⟩,
      CompatibleSourceInstantiationClosure.declaration_valid admissible runtime.variables_closed
        port.supported.ranges⟩

include receipt port evidenceAt in
theorem global_eq {evidence : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements node.coercions
      instantiation.predicates evidence) :
    Dynamic.Value.global ⟨instantiation, evidence⟩ = .global port.function := by
  have same := evidenceAt.agrees evidence produced
  have metadata := port.sourceInstantiation
  cases h : port.function with
  | mk actual actualEvidence =>
    simp only [h] at metadata same ⊢
    cases metadata
    cases same
    rfl

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port evidenceAt in
theorem at_successful_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation)
    (application : DeclarationApplicationValid context instantiation sourceTypes
      node.rawType instantiation.predicates)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before ids (.values arguments) after)
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.loweredArguments.map (·.type)) arguments payloads)
    (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  obtain ⟨_, _, valid⟩ := callee_receipt receipt port runtime calleeValid
  have functionType : instantiation.type = .function (TypeSystem.Ty.productMany sourceTypes) node.rawType := by
    cases application with
    | intro _ _ _ _ _ functionType _ => exact functionType
  have calleeTyped : Dynamic.ValueHasType context before (.global port.function)
      (.function (TypeSystem.Ty.productMany sourceTypes) node.rawType) := by
    have portValid : SourceSemantics.DeclarationInstantiation.Valid context port.function.instantiation := by
      simpa only [port.sourceInstantiation] using valid
    have portCovers : port.function.evidence.Covers
        ((SourceSemantics.Context.ofSignatures context.signatures).withAssumptions
          port.function.instantiation.predicates) := by
      have produced := evidenceAt.produces
      cases produced with
      | intro _ _ produces =>
        constructor
        · exact produces.valid
        · simpa only [port.sourceInstantiation, SourceSemantics.Context.withAssumptions,
            Dynamic.EvidenceEnvironment.Supplies] using produces.supplies
    have base := Dynamic.ValueHasType.global (heap := before) portValid portCovers
    simpa only [port.sourceInstantiation, functionType] using base
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have arity : port.header.function.parameters.length = arguments.length := by
    rw [port.header.parameters, List.length_map, binderCount]
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.loweredArguments.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.loweredArguments).symm.trans
      (receipt.native.inputType.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments port.sourceAt
      wellFormed runtime covers locals heapTyped typing calleeTyped rfl arity trace
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments
end
