import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinCalls
import Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityPayload
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-!
# Indexed callables: lambda and named values

Named generation, builtin, named and lambda values, and the contextual lambda recipes they use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
/-! Named generation sites retain the real second-pass body callback, marked
parameter prefix and entry hook. Exact plan selection identifies the complete
source of the installed seed; neither a native type nor a descriptor key alone
identifies a source graph. Runtime prefix preservation remains explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
open Core Frontend SourceInference
open CallableIndexedHistory
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Named := SourceCoreGeneralFunctions.Function

def context {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named) :
    SourceCoreFunctions.Context :=
  CompatibleNamedBody.bodyContext prepared.base.plan prepared.base.globals named

def representation {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :=
  SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts

def source (named : Named) : TypedSource := named.specialized.function.typedBody

def state (named : Named) : MetadataState := ⟨⟨named.signature.key, [], source named⟩, []⟩

def allocator {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named) :=
  SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))

def bodyAction {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (parents : List SourceCoreLocalEvidence.Prepared)
    (own : SourceCoreProgramFaultSites.Function) (statements : List StatementId) : Except SourceCoreBasic.Error Expr :=
  let actual := (representation prepared).atContext named.signature.key []
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation actual named.specialized.function.solvedRequirements
    own.assignments diagnostics named.signature.key
    (SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [])
    (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (context prepared named) prepared.base.callableContext none none)
    prepared.fuel (source named) (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) statements
    named.signature.resultType (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason

/-- This records compiler actions, not body execution. The body source and
empty parent substitution are fixed by the actual named compiler call. -/
structure Compilation {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : Named) (diagnostics : SourceCoreDataPlaceFaultSites.Program) (code : Expr) where private mk ::
  parents : List SourceCoreLocalEvidence.Prepared
  parentsPrepared : SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
    (prepared.base.locals.bindings.flatMap (·.instances)) = .ok parents
  own : SourceCoreProgramFaultSites.Function
  diagnostic : diagnostics.base.find? named.signature.key = some own
  statements : List StatementId
  roots : (source named).roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
    | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) = .ok statements
  body : Expr
  bodyCompiled : bodyAction prepared named diagnostics parents own statements = .ok body
  parameterCode : Expr
  parametersCompiled : SourceCoreSourceCells.bindParameters (allocator prepared named) (source named) [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection body = .ok parameterCode
  output : Expr
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameterCode = .ok output
  emitted : code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

theorem of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation prepared.base.sourceProgram
      (representation prepared) prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
      diagnostics prepared.base.locals prepared.base.callableContext prepared.fuel named = .ok code) :
    Nonempty (Compilation prepared named diagnostics code) := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  obtain ⟨parents, parentsPrepared, accepted⟩ := bind_ok accepted
  have parentsPrepared := mapError_ok parentsPrepared
  cases selected : diagnostics.base.find? named.signature.key with
  | none => simp [selected, bind, Except.bind, throw] at accepted
  | some own =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨statements, roots, accepted⟩ := bind_ok accepted
    obtain ⟨body, bodyCompiled, accepted⟩ := bind_ok accepted
    have bodyCompiled : bodyAction prepared named diagnostics parents own statements = .ok body := mapError_ok bodyCompiled
    change (do
      let parameterCode ← (SourceCoreSourceCells.bindParameters (allocator prepared named) (source named) [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body).mapError SourceCoreGeneralFunctions.Error.lowering
      let output ← (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameterCode).mapError SourceCoreGeneralFunctions.Error.lowering
      pure (Expr.lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)) = .ok code at accepted
    obtain ⟨parameterCode, parametersCompiled, accepted⟩ := bind_ok accepted
    obtain ⟨output, hook, emitted⟩ := bind_ok accepted
    exact ⟨⟨parents, parentsPrepared, own, selected, statements, roots, body, bodyCompiled, parameterCode,
      mapError_ok parametersCompiled, output, mapError_ok hook, (Except.ok.inj emitted).symm⟩⟩

/-- The sealed second pass supplies this receipt at the real global slot. -/
theorem compiled_at {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {index : Nat} {named : Named} (selected : prepared.base.functions[index]? = some named) :
    ∃ diagnostics code, prepared.secondPass.closures[index]? = some code ∧
      Nonempty (Compilation prepared named diagnostics code) := by
  obtain ⟨diagnostics, code, _, cached, compiled⟩ := NamedCalls.compiled_at prepared selected
  exact ⟨_, code, cached, of_accepted prepared compiled⟩

private theorem entry_of_id (table : SourceCoreStageCodebook.Table) {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    ∃ entry, table.entryAt? id = some entry ∧ entry.origin = origin := by
  unfold SourceCoreStageCodebook.Table.idAt? at selected
  cases found : table.entries.find? (fun entry => decide (entry.origin = origin)) with
  | none => simp [found] at selected
  | some entry =>
    have origin : entry.origin = origin := by simpa using List.find?_some found
    have identifier : entry.id = id := by simpa [found] using selected
    subst id
    exact ⟨entry, CallableAncestryPairedValidation.stage_entry_self table (List.mem_of_find?_eq_some found), origin⟩

/-- Full exact specialization, together with the actual descriptor selection,
fixes every seed field. No erasure of source metadata is used. -/
theorem seed {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {named : Named} {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    SourceCoreCallableAncestryPairedPreparation.named? prepared.ancestry.graph.inputs origin = some (state named) := by
  obtain ⟨entry, found, originEq⟩ := entry_of_id _ selected
  simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?, found,
    originEq, record, state, source, Except.toOption]

/-- The real named hook installs the exact source seed certified above. -/
theorem Compilation.history {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    ∃ origin, prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) (some (state named)) ∧
      compiled.output = SourceCoreCallableIndexedFrames.withFrame (.var (prepared.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) compiled.parameterCode := by
  obtain ⟨origin, index, selected, frame, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt prepared.ancestry compiled.hook
  exact ⟨origin, selected, named_complete prepared.ancestry.graph (seed prepared selected record), by rw [frame]; exact emitted⟩

/-- Runtime installation uses the real writable administrative location. The
source metadata is obtained from the hook and graph, independently of its read. -/
theorem installed {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {origin : Word} {before : Store} {location : Location} {saved : Value}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (read : before.read? location = some saved) :
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin)
      (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) := by
  have written : before.write? location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) = some
    (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, .stable (named_complete prepared.ancestry.graph (seed prepared selected record))⟩

/-- A completed actual entry hook exposes the exact marked parameter child,
its real saved-frame slots and its installed named seed. This is native trace
inversion, with no premise asserting a source body execution. -/
theorem Compilation.entered {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {environment : Environment} {before finalStore : Store} {location : Location} {saved result : Value}
    (reference : environment[prepared.base.globals.length + 1]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : before.read? location = some saved)
    (completed : Evaluates environment before compiled.output result finalStore) :
    ∃ origin bodyStore,
      prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) (some (state named)) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin)
        (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) ∧
      Evaluates (.unit :: saved :: environment)
        (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)))
        ((compiled.parameterCode.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  obtain ⟨origin, selected, carried, emitted⟩ := compiled.history record
  rw [emitted] at completed
  obtain ⟨installedValue, nextStore, bodyStore, next, bodyRun, final⟩ :=
    CallableContextFrames.withFrame_reflects (.var reference) read completed
  have expected : Evaluates (saved :: environment) before
      ((SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)).weakenAt 0)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) before := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic next expected
  exact ⟨origin, bodyStore, selected, carried, installed selected record read, bodyRun, final⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
/-! Static receipts from the actual lambda branch, including the copies of the
captures at each call and at creation, marked parameter allocation and both
production lambda hooks. Body compilation is retained as an equation, with no
premise about executing that body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
open Core Frontend SourceInference
open FunctionCode (children)

def parameterBody (policy : SourceCoreFunctions.Policy) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (parameters : List (TypedBinder × Core.Ty))
    (result : Core.Ty) (body : Core.Expr) : Except SourceCoreBasic.Error Core.Expr :=
  match policy.sourceCells with
  | none => pure (SourceCoreFunctions.bindParameters parameters result (body.weakenAt parameters.length))
  | some allocate => SourceCoreSourceCells.bindParameters allocate source scope parameters result
      SourceCoreFunctions.argumentProjection (body.weakenAt parameters.length)

structure Certificate (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (reported : Core.Ty) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  parameter : TypeSystem.Ty
  parameterCore : Core.Ty
  resultCore : Core.Ty
  sourceType : node.type = .function parameter result
  parameterTypes : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
  parameterProjected : policy.projectType (.occurrence id.occurrence) parameter = .ok parameterCore
  resultProjected : policy.projectType (.occurrence id.occurrence) result = .ok resultCore
  loweredParameters : List (TypedBinder × Core.Ty)
  bodyScope : SourceCoreLocalCell.Scope
  parametersCompiled : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (loweredParameters, bodyScope)
  body : Core.Expr
  bodyCompiled : lowerBody (children policy lowerBody fuel compilation) fuel source bodyScope statements resultCore
    reasonAt compilation.internalReason compilation.internalReason = .ok body
  allocatedBody : Core.Expr
  allocated : parameterBody policy source scope loweredParameters resultCore body = .ok allocatedBody
  copiedBody : Core.Expr
  copied : SourceCoreSourceCells.copyScope policy.sourceCells source scope (· + 1) allocatedBody = .ok copiedBody
  rawBody : Core.Expr
  bodyHook : policy.rawLambdaBody compilation source scope node parameterCore resultCore copiedBody = .ok rawBody
  checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reported
    (policy.callables.functionType parameterCore resultCore) = .ok ()
  rawLambda : Core.Expr
  expressionHook : policy.rawLambdaExpression compilation source scope node parameterCore resultCore
    (.lambda parameterCore (LanguageResult.resultType resultCore) rawBody) = .ok rawLambda
  expression : Core.Expr
  decoration : policy.callables.decorateCallable compilation source node (.lambda id) parameterCore resultCore
    (LanguageResult.success (TaggedFunction.anonymous rawLambda)) = .ok expression
  snapshotted : Core.Expr
  snapshot : (if policy.snapshotLambda id then
      SourceCoreSourceCells.copyScope policy.sourceCells source scope (fun index => index) expression
    else .ok expression) = .ok snapshotted
  emitted : lowered = ⟨reported, snapshotted⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Core.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : DecoratedFunctionCode.SpecialPasses policy lowerBody fuel compilation source scope id reasonAt)
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reported))
    (form : node.form = .lambda parameters result statements)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Certificate policy lowerBody fuel compilation source scope id node parameters result statements reported reasonAt lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  change (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower compilation (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) compilation
          childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
  simp only [pure, Except.pure] at ordinary
  cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
  all_goals
    try rw [ordinary] at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, read, form,
      bind, Except.bind, pure, Except.pure] at accepted
    cases sourceType : node.type with
    | function parameter sourceResult =>
      simp only [sourceType] at accepted
      by_cases bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
      · by_cases resultSame : result = sourceResult
        · subst sourceResult
          simp only [bundle, not_true_eq_false, ↓reduceIte] at accepted
          obtain ⟨parameterCore, parameterProjected, accepted⟩ := bind_ok accepted
          obtain ⟨resultCore, resultProjected, accepted⟩ := bind_ok accepted
          obtain ⟨⟨loweredParameters, bodyScope⟩, parametersCompiled, accepted⟩ := bind_ok accepted
          obtain ⟨body, bodyCompiled, accepted⟩ := bind_ok accepted
          have combined : (do
              let allocatedBody ← parameterBody policy source scope loweredParameters resultCore body
              let copiedBody ← SourceCoreSourceCells.copyScope policy.sourceCells source scope (· + 1) allocatedBody
              let rawBody ← policy.rawLambdaBody compilation source scope node parameterCore resultCore copiedBody
              SourceCoreBasic.ensureType (.occurrence id.occurrence) reported (policy.callables.functionType parameterCore resultCore)
              let rawLambda ← policy.rawLambdaExpression compilation source scope node parameterCore resultCore
                (.lambda parameterCore (LanguageResult.resultType resultCore) rawBody)
              let expression ← policy.callables.decorateCallable compilation source node (.lambda id) parameterCore resultCore
                (LanguageResult.success (TaggedFunction.anonymous rawLambda))
              let snapshotted ← (if policy.snapshotLambda id then
                SourceCoreSourceCells.copyScope policy.sourceCells source scope (fun index => index) expression
              else .ok expression)
              pure (⟨reported, snapshotted⟩ : SourceCoreBasic.LoweredExpr)) = .ok lowered := by
            cases cells : policy.sourceCells <;> cases snapshot : policy.snapshotLambda id <;>
              simpa only [parameterBody, cells, snapshot, bind, Except.bind, pure, Except.pure, ↓reduceIte,
                Bool.false_eq_true] using accepted
          obtain ⟨allocatedBody, allocated, accepted⟩ := bind_ok combined
          obtain ⟨copiedBody, copied, accepted⟩ := bind_ok accepted
          obtain ⟨rawBody, bodyHook, accepted⟩ := bind_ok accepted
          obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
          cases checked
          obtain ⟨rawLambda, expressionHook, accepted⟩ := bind_ok accepted
          obtain ⟨expression, decoration, accepted⟩ := bind_ok accepted
          obtain ⟨snapshotted, snapshot, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨⟨parameter, parameterCore, resultCore, sourceType, bundle, parameterProjected, resultProjected,
            loweredParameters, bodyScope, parametersCompiled, body, bodyCompiled, allocatedBody, allocated,
            copiedBody, copied, rawBody, bodyHook, checkedType, rawLambda, expressionHook, expression, decoration,
            snapshotted, snapshot, rfl⟩⟩
        · simp [bundle, resultSame, throw] at accepted
      · simp [bundle, throw] at accepted
    | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
      simp [sourceType] at accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
/-! Builtin leaves for the real indexed artifact. Nonwrapping identities come
from its actual global prefix and the compiler builtin inventory. Descriptors
belong to that artifact's sealed codebook, while closures retain the actual
ambient-typed capture environment. The three payload laws follow from those
receipts without a function-body execution premise. Named and anonymous source
functions are outside this leaf model; no closure history is inferred here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    Dynamic.Value → Word → Prop where
  | builtin {function : BuiltinFunctionId} {index : Nat} {identity : Word}
      (selected : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity) :
      Identity prepared (.builtin ⟨function⟩) identity

private theorem word_value {number : Nat} {word : Word} (accepted : Word.ofNat? number = some word) :
    word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

/-- Equal IDs mean the complete source builtin identity is equal, in both
 directions. The global prefix is never reduced modulo the word size. -/
theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related; cases related; exact .builtin _
  · intro left right a b first second
    cases first with
    | @builtin f i a foundA numberA =>
      cases second with
      | @builtin g j b foundB numberB =>
        constructor
        · intro same
          have indices : i = j := by
            have values := (word_value numberA).symm.trans ((congrArg Fin.val same).trans (word_value numberB))
            omega
          have itemA := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some foundA)
          have itemB := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some foundB)
          have functions : f = g := Option.some.inj (itemA.symm.trans (indices ▸ itemB))
          cases functions
          rfl
        · intro same
          have functions : f = g := by cases same; rfl
          subst g
          have indices : i = j := (Prod.mk.inj (Option.some.inj (foundA.symm.trans foundB))).2
          exact Option.some.inj (numberA.symm.trans (indices ▸ numberB))

/-- Builtin IDs remain outside every named global slot of the same artifact. -/
theorem Identity.outside_globals {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : Dynamic.Value} {identity named : Word} {position : Nat}
    (related : Identity prepared source identity) (bound : position < prepared.base.globals.length)
    (selected : Word.ofNat? (position + 1) = some named) : identity ≠ named := by
  intro same
  cases related with
  | builtin _ number =>
    have index := (word_value number).symm.trans ((congrArg Fin.val same).trans (word_value selected))
    omega

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {function : BuiltinFunctionId} {index : Nat} {identity : Word}
      {captured : Environment} {context : Core.Context}
      (selected : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity)
      (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function))
      (typed : RuntimeEnvironmentHasTypes world captured context prepared.layouts.definitions) :
      Represents prepared world function.type (.builtin ⟨function⟩)
        (BuiltinCalls.Protocol.contractedValue function identity descriptor.id captured)
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))

private theorem projected {catalog : SourceCoreCompatibleCatalog.Catalog}
    (profile : catalog.callableContracts = true) (function : BuiltinFunctionId) :
    catalog.project function.type = .ok
      (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) := by
  cases function <;> simp [BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes, BuiltinFunctionId.returnType,
    TypeSystem.Ty.productMany, TypeSystem.Ty.integer, TypeSystem.Ty.word, TypeSystem.Ty.bool, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreCompatibleCatalog.Catalog.functionType,
    profile, SourceCoreInteger.builtinParameter, SourceCoreInteger.builtinResult]

theorem Represents.runtime_hasType {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) :
    RuntimeValueHasType world value type prepared.layouts.definitions := by
  cases related with
  | @builtin function index identity captured context selected number descriptor typed =>
    have body := SourceCoreInteger.builtinClosure_hasType (scope := context) (definitions := prepared.layouts.definitions) function
    cases body with
    | lambda _ _ body => exact .pair (.pair (.inRight .word) (.closure typed body)) .word

/-- The ambient environment is the actual frame/marker suffix, not a catalog
with administrative entries assigned fabricated source types. -/
def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by intro _ _ _ _ _ _ _ related; cases related; exact projected profile _
  runtime_hasType := Represents.runtime_hasType
  source_function := by intro _ _ _ _ _ _ _ related; cases related; exact .builtin _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related _ _ worlds
    cases related with
    | builtin selected number descriptor typed => exact .builtin selected number descriptor (typed.weaken worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | builtin selected number descriptor _ =>
    exact .contractedIdentified _ _ _ descriptor.id (.builtin selected number) profile

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ parameter result source value type related
  cases related
  exact (Dynamic.ValueRuntimeType.builtin _).matches

/-- Successful actual builtin-reference lowering authenticates inventory,
source header and the artifact descriptor before forming the real closure.
No evidence resolver or source evaluator is executed by this proof. -/
theorem formation_of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
      compilation source node name function = .ok lowered)
    {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (store : Store) (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type := by
  have reference := BuiltinCalls.reference_of_accepted accepted
  cases reference with
  | @intro index identity expression spelling sourceType inventory identitySelected decorated =>
    cases descriptorFound : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function) with
    | error error =>
      simp [SourceCoreGeneralFunctions.callablePolicy, descriptorFound, bind, Except.bind, Except.mapError] at decorated
    | ok descriptor =>
      have emitted := ActualCallablePolicy.builtin_decoration prepared.ancestry.graph.inputs.callable active compilation source node
        function (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)) descriptor
      have same := Except.ok.inj (emitted.symm.trans decorated)
      subst expression
      refine ⟨BuiltinCalls.Protocol.contractedValue function identity descriptor.id actual, ?_, ?_⟩
      · exact BuiltinCalls.Protocol.contracted_evaluates function identity descriptor.id actual store
      · rw [sourceType]
        exact .builtin inventory (by simpa only [globals] using identitySelected) descriptor typed


/-- Every completed evaluation of the actual reference has the authenticated
value and leaves the entire store unchanged, including administrative cells. -/
theorem reference_reflects {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
      compilation source node name function = .ok lowered)
    {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    {store finalStore : Store} {result : Value}
    (completed : Evaluates actual store lowered.expression result finalStore)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, result = .inRight .word value ∧ finalStore = store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type := by
  obtain ⟨value, evaluated, related⟩ := formation_of_accepted prepared profile globals accepted typed store registry mapping
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨value, same, stores, related⟩

/-- At a real ordinary source occurrence, the same value is produced by the
independent source rule. Source requirement/coercion admission remains explicit. -/
theorem source_reference (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (function : BuiltinFunctionId)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.builtin ⟨function⟩) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form, requirements, coercions]
    exact .builtinFunction rfl
  · rw [coercions]; exact .nil

end Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
/-! Named and builtin function leaves for the actual indexed artifact. Named
identity observes complete canonical declaration metadata and resolved evidence.
Static second-pass/installation equations and actual ambient-typed captures
certify the native carrier; no function-body execution follows from these laws.
Anonymous closures and source occurrence canonical-order provenance remain
separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Evidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

/-- Complete canonical plan and dictionary receipts. `target` ties source
metadata to the key through the real matcher, rather than replacing metadata
with that key. `slot` retains the actual singleton global selection. -/
structure Row {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (index : Nat) (signature : SourceCoreCalls.Signature) (specialized : Specialized) (evidence : Evidence) : Prop where
  slot : CallableNamedMetadata.Slot prepared.base.globals index signature
  record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized
  target : SourceCompilationPlan.exactInstantiationKey prepared.base.plan (CallableNamedMetadata.instantiation specialized) = .ok signature.key
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence

/-- The ordinary compiler selection supplies the unique slot and complete
canonical record. The extra ordered-domain receipt records exactly what the
order-insensitive matcher did not check. -/
theorem Row.of_selected {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    Row prepared index signature specialized evidence ∧ metadata = CallableNamedMetadata.instantiation specialized := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan] at target
  have same := (CallableNamedMetadata.matches_of_exact target record).canonical domain
  refine ⟨⟨?_, record, same ▸ target, resolved⟩, same⟩
  simpa only [globals] using CallableNamedMetadata.slot_of_selected_signature accepted

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) : Dynamic.Value → Word → Prop where
  | builtin {source identity} (related : CallableIndexedBuiltinValues.Identity prepared source identity) : Identity prepared source identity
  | named {index signature specialized evidence identity}
      (row : Row prepared index signature specialized evidence)
      (number : Word.ofNat? (index + 1) = some identity) :
      Identity prepared (.global (CallableNamedMetadata.global specialized evidence)) identity

private theorem word_value {number : Nat} {word : Word} (accepted : Word.ofNat? number = some word) : word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private theorem Row.source_eq_iff {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {i j : Nat} {a b : SourceCoreCalls.Signature} {f g : Specialized} {x y : Evidence}
    (left : Row prepared i a f x) (right : Row prepared j b g y) :
    i = j ↔ CallableNamedMetadata.global f x = CallableNamedMetadata.global g y := by
  constructor
  · intro same
    have signatures := Option.some.inj (left.slot.selected.symm.trans (same ▸ right.slot.selected))
    subst b
    have records := Except.ok.inj (left.record.symm.trans right.record)
    subst g
    have evidence := Except.ok.inj (left.resolved.symm.trans right.resolved)
    subst y
    rfl
  · intro same
    have headers := congrArg Dynamic.GlobalFunction.instantiation same
    change CallableNamedMetadata.instantiation f = CallableNamedMetadata.instantiation g at headers
    have selected := left.target
    rw [headers] at selected
    have keys := Except.ok.inj (selected.symm.trans right.target)
    exact (left.slot.unique right.slot keys).2

theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related
    cases related with
    | builtin related => exact (CallableIndexedBuiltinValues.identity_faithful prepared).comparable related
    | named => exact .global _
  · intro first second a b left right
    cases left with
    | builtin left =>
      cases right with
      | builtin right => exact (CallableIndexedBuiltinValues.identity_faithful prepared).equal left right
      | named row number =>
        constructor
        · intro same
          exact False.elim (left.outside_globals (List.getElem?_eq_some_iff.mp row.slot.selected).choose number same)
        · intro same; cases left; cases same
    | named left numberA =>
      cases right with
      | builtin right =>
        constructor
        · intro same
          exact False.elim (right.outside_globals (List.getElem?_eq_some_iff.mp left.slot.selected).choose numberA same.symm)
        · intro same; cases right; cases same
      | named right numberB =>
        constructor
        · intro same
          have indices : _ := (word_value numberA).symm.trans ((congrArg Fin.val same).trans (word_value numberB))
          have equalIndices : _ := Nat.add_right_cancel indices
          exact congrArg Dynamic.Value.global (left.source_eq_iff right |>.mp equalIndices)
        · intro same
          have sources := Dynamic.Value.global.inj same
          have indices := (left.source_eq_iff right).mpr sources
          exact Option.some.inj (numberA.symm.trans (indices ▸ numberB))

/-- The code is the exact installed second-pass template at this global slot.
The capture environment and its typing are actual native data. This receipt
establishes static formation, not invocation meaning or arbitrary store history. -/
structure Native {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) (index : Nat) (signature : SourceCoreCalls.Signature)
    (body : Expr) (captured : Environment) : Prop where
  code : ∃ template, prepared.secondPass.closures[index]? = some template ∧
    SourceCoreCompatibleOutputs.installedTemplate index template =
      .lambda signature.parameterType (LanguageResult.resultType signature.resultType) body
  typed : RuntimeValueHasType world
    (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)
    signature.functionType prepared.layouts.definitions

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {sourceType source value type}
      (related : CallableIndexedBuiltinValues.Represents prepared world sourceType source value type) :
      Represents prepared world sourceType source value type
  | named {index signature specialized evidence identity body captured}
      (row : Row prepared index signature specialized evidence)
      (number : Word.ofNat? (index + 1) = some identity)
      (projection : checked.catalog.project specialized.function.type = .ok
        (CallableContract.functionType signature.parameterType signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
      (native : Native prepared world index signature body captured) :
      Represents prepared world specialized.function.type (.global (CallableNamedMetadata.global specialized evidence))
        (.pair (.pair (.inRight .unit (.word identity))
          (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)) (.word descriptor.id))
        (CallableContract.functionType signature.parameterType signature.resultType)

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | builtin related => exact (CallableIndexedBuiltinValues.model prepared profile).projection (registry := registry) (mapping := mapping) related
    | named _ _ projection _ _ => exact projection
  runtime_hasType := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | builtin related => exact related.runtime_hasType
    | named _ _ _ _ native => exact .pair (.pair (.inRight .word) native.typed) .word
  source_function := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | builtin related => cases related; exact .builtin _
    | named => exact .global _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related registries mappings worlds
    cases related with
    | builtin related => exact .builtin ((CallableIndexedBuiltinValues.model prepared profile).extend related registries mappings worlds)
    | named row number projection descriptor native =>
      exact .named row number projection descriptor ⟨native.code, native.typed.weaken worlds⟩

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | builtin related =>
    cases related with
    | builtin selected number descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.builtin (.builtin selected number)) profile
  | named row number _ descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.named row number) profile

theorem Represents.runtime_view {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) : Dynamic.ValueRuntimeTypeMatches source sourceType := by
  cases related with
  | builtin related => cases related; exact (Dynamic.ValueRuntimeType.builtin _).matches
  | named => exact (Dynamic.ValueRuntimeType.global _).matches

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ _ _ _ _ _ related
  exact related.runtime_view

/-- Actual native reference formation loads the exact installed closure and
wraps it without changing its captures or store. Source metadata and evidence
remain the complete canonical row. -/
theorem reference {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {index signature specialized evidence identity body captured world}
    (row : Row prepared index signature specialized evidence)
    (number : Word.ofNat? (index + 1) = some identity)
    (projection : checked.catalog.project specialized.function.type = .ok (CallableContract.functionType signature.parameterType signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
    (native : Native prepared world index signature body captured)
    {actual : Environment} {store : Store} {location : Location} {internalReason : Word}
    (selected : actual[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world specialized.function.type
        (.global (CallableNamedMetadata.global specialized evidence)) value
        (CallableContract.functionType signature.parameterType signature.resultType) :=
  ⟨_, NamedCalls.native_reference descriptor selected read, .named row number projection descriptor native⟩

/-- An ordinary accepted source reference supplies a fully represented global
value. Requirement-bearing references use `authenticated_evidence_eq` at their
separate evidence-policy branch; this theorem does not bypass that policy. -/
theorem formation_of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {metadata : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {index : Nat} {signature : SourceCoreCalls.Signature} {identity : Word} {specialized : Specialized}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (readNode : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration metadata))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node metadata true = .ok (index, signature))
    (number : Word.ofNat? (index + 1) = some identity)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
    (projection : checked.catalog.project specialized.function.type = .ok (CallableContract.functionType signature.parameterType signature.resultType))
    (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key) = .ok descriptor)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (coercions : node.coercions = []) (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context metadata)
    {world : StoreTyping} {actual captured : Environment} {store : Store} {location : Location} {body : Expr}
    (native : Native prepared world index signature body captured)
    (globalReference : actual[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (globalPayload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨metadata, []⟩) heap ∧
      Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world metadata.type (.global ⟨metadata, []⟩) value
        (CallableContract.functionType signature.parameterType signature.resultType) ∧
      (∀ result finalStore, Evaluates actual store lowered.expression result finalStore → result = .inRight .word value ∧ finalStore = store) := by
  obtain ⟨chosen, selectedRecord, matched, assumptions, _⟩ := CallableNamedMetadata.metadata_of_selected_signature selection
  rw [plan] at selectedRecord
  have same := Except.ok.inj (selectedRecord.symm.trans record)
  subst chosen
  have noPredicates : metadata.predicates = [] := matched.predicates.symm.trans assumptions
  have canonical := matched.canonical domain
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok [] := by rw [assumptions]; rfl
  have row := (Row.of_selected prepared plan globals selection record domain resolved).1
  have sourceTrace := NamedCalls.accepted_named_reference (program := program) (evidence := evidence)
    (sourceEnvironment := sourceEnvironment) (heap := heap) prepared.ancestry.graph.inputs.callable active
    owner found readNode form special accepted selection number callables descriptor descriptorAccepted
    coercions requirements valid (by rw [noPredicates]; exact .nil) globalReference globalPayload
  refine ⟨_, sourceTrace.2.2.1, sourceTrace.2.2.2.1, ?_, sourceTrace.2.2.2.2⟩
  rw [canonical]
  exact .named row number projection descriptor native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
/-! The actual checker's retained named metadata uses the opposite parameter
ledger order from the specialization record. This separate leaf model
transports complete source values by an explicit involution. Canonical and
retained source values are never identified inside one identity relation.
Evidence, raw type, native code and actual captures are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Evidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) : Dynamic.Value → Word → Prop where
  | retained {source identity} (canonical : CallableIndexedNamedValues.Identity prepared source identity) :
      Identity prepared (CallableNamedReversal.value source) identity

theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related
    cases related with
    | retained canonical =>
      cases canonical with
      | builtin related => cases related; exact .builtin _
      | named => exact .global _
  · intro first second a b left right
    cases left with
    | retained left =>
      cases right with
      | retained right =>
        constructor
        · intro same
          exact congrArg CallableNamedReversal.value ((CallableIndexedNamedValues.identity_faithful prepared).equal left right |>.mp same)
        · intro same
          exact (CallableIndexedNamedValues.identity_faithful prepared).equal left right |>.mpr (CallableNamedReversal.value_injective same)

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | retained {sourceType source value type}
      (canonical : CallableIndexedNamedValues.Represents prepared world sourceType source value type) :
      Represents prepared world sourceType (CallableNamedReversal.value source) value type

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | retained canonical => exact (CallableIndexedNamedValues.model prepared profile).projection (registry := registry) (mapping := mapping) canonical
  runtime_hasType := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | retained canonical => exact (CallableIndexedNamedValues.model prepared profile).runtime_hasType (registry := registry) (mapping := mapping) canonical
  source_function := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | retained canonical =>
      cases canonical with
      | builtin related => cases related; exact .builtin _
      | named => exact .global _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related registries maps worlds
    cases related with
    | retained canonical => exact .retained ((CallableIndexedNamedValues.model prepared profile).extend canonical registries maps worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin related =>
      cases related with
      | builtin selected number descriptor _ =>
        exact .contractedIdentified _ _ _ descriptor.id (.retained (.builtin (.builtin selected number))) profile
    | named row number _ descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.retained (.named row number)) profile

theorem Represents.runtime_view {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) : Dynamic.ValueRuntimeTypeMatches source sourceType := by
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin related => cases related; exact (Dynamic.ValueRuntimeType.builtin _).matches
    | named => exact (Dynamic.ValueRuntimeType.global _).matches

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ _ _ _ _ _ related
  exact related.runtime_view

/-- The actual matcher accepts either ledger order. Thus a selected retained
occurrence supplies the old canonical target receipt without an extra lookup
assumption. All remaining fields are retained in `same`. -/
theorem row_of_selected {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (same : metadata = CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation specialized))
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    CallableIndexedNamedValues.Row prepared index signature specialized evidence := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan, same, CallableNamedReversal.target_reverse] at target
  exact ⟨by simpa only [globals] using CallableNamedMetadata.slot_of_selected_signature accepted, record, target, resolved⟩

/-- Actual declaration construction and successful specialization supply the
reverse-order source header. No equality of whole source records is assumed. -/
theorem row_of_inferred {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    CallableIndexedNamedValues.Row prepared index signature specialized evidence ∧
      metadata = CallableNamedCanonicalOrder.retainedInstantiation specialized := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan] at target
  have matched := CallableNamedMetadata.matches_of_exact target record
  rw [formed] at matched
  have same := formed.trans (matched.retained_of_specialization specialization unique next final caller)
  exact ⟨row_of_selected prepared plan globals accepted record same resolved, same⟩

/-- Actual target selection and evidence authentication identify every field
of a retained source global. This also covers nonempty dictionaries at the
metadata boundary; extracting their materialization from the qualified
lowering branch remains a separate obligation. -/
theorem global_of_inferred {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {key : SourceCompilationPlan.Key} {metadata : DeclarationInstantiation} {specialized : Specialized}
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (selected : SourceCompilationPlan.exactInstantiationKey plan metadata = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    {actual canonical : Evidence} {semantic : Dynamic.EvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical)
    (represented : Forall₂ (fun item entry => entry.1 = SourceTypedRuntime.runtimeEvidenceGoal item ∧
      ImplementationEvidenceRepresents item entry.2) actual semantic) :
    (⟨metadata, semantic⟩ : Dynamic.GlobalFunction) =
      CallableNamedReversal.global (CallableNamedMetadata.global specialized canonical) := by
  have matched := CallableNamedMetadata.matches_of_exact selected record
  rw [formed] at matched
  have same := formed.trans (matched.retained_of_specialization specialization unique next final caller)
  rw [same, CallableNamedMetadata.environment_eq_of_represents represented,
    CallableNamedMetadata.authenticated_evidence_eq authenticated resolved]
  rfl

/-- The complete accepted ordinary reference forms the retained source value,
including its parameter order. The real instantiation/specialization receipts
discharge full metadata equality through the order bridge. Qualified evidence
policy extraction is a separate branch. -/
theorem formation_of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {metadata : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {index : Nat} {signature : SourceCoreCalls.Signature} {identity : Word} {specialized : Specialized}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (readNode : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration metadata))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node metadata true = .ok (index, signature))
    (number : Word.ofNat? (index + 1) = some identity)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (projection : checked.catalog.project specialized.function.type = .ok (CallableContract.functionType signature.parameterType signature.resultType))
    (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key) = .ok descriptor)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (coercions : node.coercions = []) (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context metadata)
    {world : StoreTyping} {actual captured : Environment} {store : Store} {location : Location} {body : Expr}
    (native : CallableIndexedNamedValues.Native prepared world index signature body captured)
    (globalReference : actual[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (globalPayload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨metadata, []⟩) heap ∧
      Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world metadata.type (.global ⟨metadata, []⟩) value
        (CallableContract.functionType signature.parameterType signature.resultType) ∧
      (∀ result finalStore, Evaluates actual store lowered.expression result finalStore → result = .inRight .word value ∧ finalStore = store) := by
  obtain ⟨chosen, selectedRecord, matched, assumptions, _⟩ := CallableNamedMetadata.metadata_of_selected_signature selection
  rw [plan] at selectedRecord
  have same := Except.ok.inj (selectedRecord.symm.trans record)
  subst chosen
  have noPredicates : metadata.predicates = [] := matched.predicates.symm.trans assumptions
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok [] := by rw [assumptions]; rfl
  obtain ⟨row, sameMetadata⟩ := row_of_inferred prepared plan globals selection record specialization unique next final caller formed resolved
  have sourceTrace := NamedCalls.accepted_named_reference (program := program) (evidence := evidence)
    (sourceEnvironment := sourceEnvironment) (heap := heap) prepared.ancestry.graph.inputs.callable active
    owner found readNode form special accepted selection number callables descriptor descriptorAccepted
    coercions requirements valid (by rw [noPredicates]; exact .nil) globalReference globalPayload
  refine ⟨_, sourceTrace.2.2.1, sourceTrace.2.2.2.1, ?_, sourceTrace.2.2.2.2⟩
  rw [sameMetadata]
  exact .retained (.named row number projection descriptor native)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
/-! Indexed anonymous leaves retain the source formation inputs, static
compiler receipts, real mapped captures and the independently carried lexical
history. A source context or dictionary is never recovered from a native type.
The relation has no field requiring execution of the lambda body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedHistory
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Identity := @CallableIndexedRetainedNamedValues.Identity
abbrev identity_faithful := @CallableIndexedRetainedNamedValues.identity_faithful

structure Code {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (function : Dynamic.Closure) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (viewRelation : TypedSource → TypedSource → Prop := LambdaMetadataViews.MetadataView) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  active : TypeSystem.Substitution
  view : TypedSource
  viewOfSource : viewRelation function.source view
  id : ExpressionId
  sourceNode : ExpressionNode
  sourceFound : function.source.lookupExpression? id = some sourceNode
  sourceForm : sourceNode.form = .lambda function.parameters function.resultType function.body
  node : ExpressionNode
  found : view.lookupExpression? id = some node
  form : node.form = sourceNode.form
  reported : Core.Ty
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  receipt : CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel compilation view scope id node
    function.parameters function.resultType function.body reported reasonAt lowered
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    compilation view scope id reasonAt = .ok lowered
  allocationError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  allocationProfile : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
    prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt compilation.owner active allocationError))
  manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner active
  expressionProfile : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner active
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active
  descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id active)
  projection : checked.catalog.project (FunctionValues.sourceType function) = .ok
    (CallableContract.functionType receipt.parameterCore receipt.resultCore)
  typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
    (LanguageResult.resultType (CallableContract.functionType receipt.parameterCore receipt.resultCore)) prepared.layouts.definitions

def Code.referenceIndex {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) : Nat :=
  SourceCoreCallableIndexedAncestry.creationReferenceIndex code.compilation scope

def Code.body {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) : Expr :=
  SourceCoreCallableIndexedFrames.withFrame (.var (code.referenceIndex + 2))
    (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
      code.descriptor.id (.var 1) (.loadCell (.var (code.referenceIndex + 2)))) (code.receipt.rawBody.weakenAt 1)

/-- The decorated lambda, before any creation-time copies of its captures. -/
def Code.expression {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) : Expr :=
  LanguageResult.success (code.descriptor.wrap (TaggedFunction.anonymous
    (.letE (.loadCell (.var code.referenceIndex))
      (.lambda code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore) code.body))))

theorem Code.decorated {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    code.receipt.expression = code.expression := by
  have hook := code.receipt.expressionHook
  rw [code.expressionProfile] at hook
  obtain ⟨origin, body, selected, raw, _, _, _, emitted⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  have sameBody := Expr.lambda.inj raw
  have nodeId := (lookupExpression?_sound code.found).2
  rw [nodeId] at selected
  have sameOrigin : origin = code.descriptor.id := Option.some.inj (selected.symm.trans code.descriptor.found)
  have bodyEq : code.receipt.rawBody = body := sameBody.2.2
  have decorated := code.receipt.decoration
  rw [code.callables] at decorated
  have expected := ActualCallablePolicy.lambda_decoration prepared.ancestry.graph.inputs.callable code.active
    code.compilation code.view code.node code.id code.receipt.parameterCore code.receipt.resultCore
    (TaggedFunction.anonymous code.receipt.rawLambda) code.descriptor
  have decoration := Except.ok.inj (decorated.symm.trans expected)
  rw [decoration, emitted, sameOrigin, ← bodyEq]
  rfl

/-- The emitted expression is the decorated lambda after the creation-time
copies that the policy selects. -/
theorem Code.emitted {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    code.lowered.expression = code.receipt.snapshotted :=
  congrArg SourceCoreBasic.LoweredExpr.expression code.receipt.emitted

/-- A lambda whose policy does not snapshot it, a generalized local's
initializer, emits the decorated lambda unchanged. -/
theorem Code.emitted_shared {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation)
    (shared : code.policy.snapshotLambda code.id = false) :
    code.lowered.expression = code.expression := by
  have snapshot := code.receipt.snapshot
  simp only [shared, Bool.false_eq_true, ↓reduceIte] at snapshot
  rw [code.emitted, ← Except.ok.inj snapshot, code.decorated]

/-- An ordinary lambda emits its creation-time copies around the decorated
lambda, through the indexed marked allocator. -/
theorem Code.emitted_copied {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation)
    (copied : code.policy.snapshotLambda code.id = true) :
    SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        prepared.base.globals.length (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError)))
      code.view scope (fun index => index) code.expression = .ok code.lowered.expression := by
  have snapshot := code.receipt.snapshot
  simp only [copied, ↓reduceIte] at snapshot
  rw [code.emitted, ← code.allocationProfile, ← code.decorated]
  exact snapshot

/-- Change only the evidence required for the source view. The emitted code,
capture layout, actual compiler receipt and native callable stay identical. -/
def Code.weaken_view {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {before after : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative before)
    (weaken : ∀ source view, before source view → after source view) :
    Code prepared function scope administrative after :=
  { code with viewOfSource := weaken _ _ code.viewOfSource }

theorem Code.weaken_view_body {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {before after : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative before)
    (weaken : ∀ source view, before source view → after source view) :
    (code.weaken_view weaken).body = code.body := rfl

/-- The full actual environment is retained. Only lexical cell references are
compared with canonical slots; extra native captures are not discarded. -/
structure Captures {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (scope : SourceCoreLocalCell.Scope)
    (source : Dynamic.Environment) (actual : Core.Environment) where
  administrative : Core.Context
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Renaming
  represented : DataHeap.EnvRepresents (storageCatalog checked.catalog) mapping world administrative scope source canonical prepared.layouts.definitions
  agrees : ReadOnly.EnvironmentsAgree embedding canonical actual
  respects : Renaming.Respects embedding (SourceCoreLocalCell.coreContext scope ++ administrative) actualContext
  typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions

def Captures.extend {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping} {scope : SourceCoreLocalCell.Scope}
    {source : Dynamic.Environment} {actual : Core.Environment}
    (captured : Captures prepared mapping world scope source actual)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Captures prepared futureMapping futureWorld scope source actual :=
  {captured with represented := captured.represented.extend maps worlds, typed := captured.typed.weaken worlds}

/-- Generation-site alignment belongs to the carried source execution state.
An index that merely decodes successfully does not supply this receipt. Source
context and evidence remain the exact inputs stored in `function`. -/
structure History {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) where
  native : NativeFrame
  ghost : GhostFrame
  metadata : MetadataState
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table native ghost (some metadata)
  source : metadata.metadata.source = function.source
  owner : metadata.metadata.owner = code.compilation.owner
  active : metadata.nativeActive = code.active

/-- The same code serves a closure over another captured environment: no
field of the code mentions the captured locations. -/
def Code.recapture {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) (captured : Dynamic.Environment) :
    Code prepared { function with captured := captured } scope administrative viewRelation :=
  { code with }

def History.recapture {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    {code : Code prepared function scope administrative viewRelation} (history : History code)
    (captured : Dynamic.Environment) : History (code.recapture captured) :=
  { history with }

def value {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) (embedding : Renaming)
    (native : NativeFrame) (actual : Core.Environment) : Core.Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
      (code.body.rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native :: actual))) (.word code.descriptor.id)

theorem weaken_view_value {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {before after : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative before)
    (weaken : ∀ source view, before source view → after source view)
    (embedding : Renaming) (native : NativeFrame) (actual : Core.Environment) :
    value (code.weaken_view weaken) embedding native actual = value code embedding native actual := rfl

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | retained {sourceType source native type}
      (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
      Represents prepared mapping world sourceType source native type
  | lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) prepared.layouts.definitions) :
      Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ mapping world => Represents prepared mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).projection (registry := registry) (mapping := mapping) prior
    | lambda _ code _ _ => exact code.projection
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).runtime_hasType (registry := registry) (mapping := mapping) prior
    | lambda _ _ _ typed => exact typed
  source_function := by
    intro registry mapping world sourceType source native type related
    cases related with
    | retained prior => exact (CallableIndexedRetainedNamedValues.model prepared profile).source_function (registry := registry) (mapping := mapping) prior
    | lambda => exact .closure _
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | retained prior => exact .retained ((CallableIndexedRetainedNamedValues.model prepared profile).extend prior registries maps worlds)
    | lambda captured code history typed => exact .lambda (captured.extend maps worlds) code history (typed.weaken worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | retained prior => exact CallableIndexedRetainedNamedValues.observations prepared profile (mapping := mapping) prior
  | lambda captured code history _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro registry mapping world parameter result source native type related
  cases related with
  | retained prior => exact prior.runtime_view
  | lambda => exact (Dynamic.ValueRuntimeType.closure _).matches

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
/-! An exact production lowerer recipe is retained as a static proposition.
Its existential compilation is the one used at the same original Site.
Recapture preserves the lowerer; no compiler result or execution law is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
open Core Frontend SourceInference
open CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The literal equation returned by the original contextual producer. -/
def BodyRecipe
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode)
    (code : Code prepared function scope administrative) : Prop :=
  code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    (CallableIndexedNamedGeneration.context prepared named).solvedRequirements compilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context prepared named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.locals named.signature.key [])

/-- The selected compiler data stays inside Prop, at the exact named seed and Code. -/
def Retained (named : CallableIndexedNamedGeneration.Named)
    (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode),
    BodyRecipe compilation code

/-- Existing exact recipes enter the retained proposition without selecting another Site. -/
theorem Retained.of_recipe
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode)
    {code : Code prepared function scope administrative}
    (recipe : BodyRecipe compilation code) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, recipe⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
/-! The original outer contextual bind fixes the full policy and body recipe.
The same named Compilation witness remains inside Prop at the actual Code.
Compatible reads use prepared.fuel; the special callback keeps its original
root fuel when a nested child is compiled at a smaller budget.
No execution law or second accepted-policy selection is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- This is the actual original special callback, including its child budget cap. -/
def special
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat) :
    SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
      TypedSource → SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
      Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr) :=
  fun current child budget source scope id reasonAt => do
    let source ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let onLocalError := fun (error : SourceCoreLocalPolymorphism.Error) => match error with
      | .metadata error => error
      | _ => SourceCoreBasic.Error.unsupportedExpression id node.form
    let initialized := prepared.base.locals.bindings.find? fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)
    if let some initialized := initialized.filter (fun _ => (none : Option ExpressionId) ≠ some id) then
      let binding ← (prepared.base.locals.binding current.owner initialized.binder.id).mapError onLocalError
      let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding [] fun candidate => do
        let emission ← (SourceCoreLocalEvidence.prepareForEmission prepared.base.sourceProgram current.plan
          candidate none compilation.parents).mapError fun _ =>
            SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch id
        let localPrepared := emission.prepared
        let childContext := { current with solvedRequirements := localPrepared.caller.function.solvedRequirements }
        let lowered ← (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
          prepared.base.locals compilation.parents compilation.own.assignments diagnostics childContext
          prepared.base.callableContext (some localPrepared) (some id) (min budget rootFuel)
          localPrepared.source scope id reasonAt) |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
          |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        match lowered.expression with
        | .inRight .word closure => pure closure
        | _ => throw (.initializerMetadataMismatch id)).mapError onLocalError
      return some lowered
    let evidence ← SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    if let some lowered := evidence then return some lowered
    match node.form with
    | .reference _ (.local binder) =>
      if prepared.base.locals.bindings.any (fun binding =>
          decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
        let lowered ← (SourceCoreLocalPolymorphism.lowerRead prepared.base.locals current.owner []
          source scope id (reasonAt id)) |>.mapError onLocalError
        let viewed ← ((representation prepared).atContext named.signature.key []).localReadView
          current.owner [] source scope id lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
        return some viewed
      else return none
    | _ => return none

/-- Literal policy fields of the one outer-bind choice, at its original compilation. -/
structure PolicyRecipe
    (compilation : Compilation prepared named diagnostics namedCode)
    (rootFuel : Nat) (policy : SourceCoreFunctions.Policy) : Prop where
  readExpression : policy.readExpression = fun source id => do
    let viewed ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner none source id
    ((representation prepared).atContext named.signature.key []).expressions.readExpression viewed id
  lowerSpecial : policy.lowerSpecial? = some (special compilation rootFuel)
  lowerRead : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead prepared.fuel
    (SourceCoreCompatibleValues.Context.initial checked)
  leafLowerer : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer
    (SourceCoreCompatibleValues.Context.initial checked)
  projectType : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked
  sourceCells : policy.sourceCells = some (allocator prepared named)
  /-- The outer choice compiles no generalized initializer, so every lambda it
  forms copies its captures at creation. -/
  snapshotLambda : policy.snapshotLambda = fun _ => true

/-- The body and complete policy use one original compilation. The policy keeps
its own root fuel when the same callback compiles a child at a smaller budget. -/
def Retained (named : Named) (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat),
    CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code ∧
      PolicyRecipe compilation rootFuel code.policy ∧ code.compilation = context prepared named

/-- Retain only the actual witness passed by the producer. -/
theorem Retained.of_recipes
    (compilation : Compilation prepared named diagnostics namedCode)
    {code : Code prepared function scope administrative} {rootFuel : Nat}
    (body : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code)
    (policy : PolicyRecipe compilation rootFuel code.policy)
    (sameCompilation : code.compilation = context prepared named) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

/-- Existing body-recipe consumers can forget the additional policy equations. -/
theorem Retained.body_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, body, _policy, _sameCompilation⟩ := retained
  exact CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation body

/-- The compatible read profile is global and keeps the original prepared fuel. -/
theorem Retained.lowerRead {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    code.policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead prepared.fuel
      (SourceCoreCompatibleValues.Context.initial checked) := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, policy, _sameCompilation⟩ := retained
  exact policy.lowerRead

/-- The literal compatible leaf callback is retained without choosing another policy. -/
theorem Retained.leafLowerer {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    code.policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer
      (SourceCoreCompatibleValues.Context.initial checked) := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, policy, _sameCompilation⟩ := retained
  exact policy.leafLowerer

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
/-! The same contextual compilation retains its actual public diagnostic issuer.
Body and expression policy receipts share that exact compilation witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- Only the real compatible issuer's complete base table is retained; the
existing optional callable root-table replacement preserves this identity. -/
def IssuedAt (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧ diagnostics.base = issued.program.base ∧
      diagnostics.places = issued.program.places

/-- One actual compilation supplies the body, the full root policy, and the
issued assignment inventory. Nested lambdas keep that same witness. -/
def Retained (named : Named) (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat),
    IssuedAt prepared diagnostics ∧
      CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code ∧
      CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel code.policy ∧
      code.compilation = context prepared named

theorem Retained.of_recipes
    (compilation : Compilation prepared named diagnostics namedCode)
    (issued : IssuedAt prepared diagnostics)
    {code : Code prepared function scope administrative} {rootFuel : Nat}
    (body : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code)
    (policy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel code.policy)
    (sameCompilation : code.compilation = context prepared named) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, rootFuel, issued, body, policy, sameCompilation⟩

theorem Retained.body_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, _, _, body, _, _⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, body⟩

theorem Retained.policy_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _, body, policy, same⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning
/-! Independent source-body correspondence through the actual indexed named
entry callback. The universal body theorem supplies child execution under the
real inserted binders. Installation and restoration are derived native steps,
including their effects on the represented heap and protected snapshots.

This composes a certified source body with an accepted instrumentation hook.
It does not extract that body certificate from the whole function compiler:
the production parameter prefix, named-source attribution and staged recursive
body correspondence remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

private theorem agree_body {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_body (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
  {program : Program} {sourceFunction : Dynamic.Closure} {certificate : FunctionCode.BodyCertificate}
  {faults : FunctionCalls.FaultRep}

/-- The accepted callback supplies the named origin and installed history.
Source finiteness and the universal body theorem supply all child execution;
the caller's current token and original administrative values are restored. -/
theorem preserves (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {scope : SourceCoreLocalCell.Scope}
    {type : Ty} {body code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (bodyCertificate : certificate sourceFunction.source scope sourceFunction.body type body)
    (bodyMeaning : FunctionCalls.BodyPreserves model program sourceFunction certificate faults)
    {context staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (bodyTyped : StatementsHaveType sourceFunction.source
      {returnType := sourceFunction.resultType, loopDepth := 0} context sourceFunction.body staticFinal facts)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {outcome : Dynamic.ExpressionOutcome}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered nativeDefinitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (trace : FunctionCallBody.Trace program sourceFunction context environment before outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    bodyMeaning bodyCertificate bodyTyped environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) trace
  rw [rename_body] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

/-- A completed actual wrapper supplies the child native trace for the
universal reflection theorem. No finite source body trace is required. -/
theorem reflects (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {scope : SourceCoreLocalCell.Scope}
    {type : Ty} {body code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (bodyCertificate : certificate sourceFunction.source scope sourceFunction.body type body)
    (bodyMeaning : FunctionCalls.BodyReflects model program sourceFunction certificate faults)
    {context staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (bodyTyped : StatementsHaveType sourceFunction.source
      {returnType := sourceFunction.resultType, loopDepth := 0} context sourceFunction.body staticFinal facts)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {value : Value}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered nativeDefinitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      FunctionCallBody.Trace program sourceFunction context environment before outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var reference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_body] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    bodyMeaning bodyCertificate bodyTyped environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning
end
