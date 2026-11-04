import Solcore.SourceSemantics.SourceCompiledLocalCanonicalReadOrder
import Solcore.SourceSemantics.SourceCompiledLocalLexicalAllocation
import Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder
import Solcore.SourceSemantics.SourceCompiledBodyReadCutoff
import Solcore.SourceSemantics.SourceCompiledActualLocalReadCalls
import Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
import Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins
import Solcore.SourceSemantics.SourceCompiledActualTemplateBacking
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins
import Solcore.SourceSemantics.SourceCachedTemplateScope
import Solcore.SourceSemantics.CoreLowering.CallStageBoundary
import Solcore.SourceSemantics.CoreLowering.CallStageGuard
import Solcore.SourceSemantics.CoreLowering.AuthenticatedCallableLedger
import Solcore.SourceSemantics.SourceCompiledCatalogedCallOrigins
import Solcore.SourceSemantics.SourceCompiledDirectCallOrigins
import Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
import Solcore.SourceSemantics.SourceCompiledNestedInitializerPublicPrivacy
import Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
import Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
import Solcore.SourceSemantics.Dynamic.Initialization
import Solcore.Frontend.SourceCoreExecution
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStagedCalls
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.Test.SourceCoreRecursiveNamedTupleExpressions
import Solcore.SourceSemantics.SourceSelectedTemplateInventory
import Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection

/-!
# Compiled origin tests

Origins and owners of compiled calls and templates, recursive stage operations, and prepared local reads.
-/

section
-- leanmerge: from Solcore.Test.SourceBodyTemplateScope
/-! Raw public compilation prepares a method containing nested generalized
lambdas and a nonempty qualified template. Both genuine catalog origins
supply their original checker body at the completed cache position. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceBodyTemplateScope
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceSemantics.CoreLowering

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, (Word, Bool)> { function coerce(flag: Bool) returns ((Word, Bool)) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; } }",

    "function entry(flag: Bool) returns (Word, Bool) { return flag; }"]}] }

def main : IO Unit := do
  let checked ← match checkProgram workspace 4096 with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"checker: {reprStr error}")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "entry")
    | throw (IO.userError "missing entry")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    match artifact : compiled.artifact? with
    | none => throw (IO.userError "missing completed artifact")
    | some cached =>
      have _actualBodies := SourceCompiledActualInitializerBarriers.compile_cached_bodies compiledEq artifact
      let mut ordinary := 0
      let mut methods := 0
      let mut methodTemplates := 0
      let mut templates := 0
      let mut variables := 0
      let mut separatedPairs := 0
      let mut localReadCalls := 0
      let mut generalizedReadCalls := 0
      let mut nestedOwners := 0
      let mut orderedLexicalReads := 0
      let mut orderedGeneralizedReads := 0
      for index in List.range cached.indexed.base.functions.length do
        match position : cached.indexed.base.functions[index]? with
        | none => throw (IO.userError "missing cache position")
        | some named =>
          have _actualScope := SourceBodyTemplateScope.cached_selection_scope artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have _actualGeneralizations := SourceCompiledLocalFinalization.BodySelection.cached_initialized_origins artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have _actualTemplateWitnesses := SourceCompiledLocalFinalization.BodySelection.cached_liveTemplatesBacked artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          have exactCalls := SourceCompiledLocalFinalization.BodySelection.compile_local_read_calls
            compiledEq artifact position
          have _actualReadCutoff : ∃ selected : SourceCompiledLocalFinalization.BodySelection
              compiled named.specialized options.checkingFuel,
              SourceInferenceExecution.LocalReadCutoff selected.body.body.state := by
            obtain ⟨selected, _⟩ := exactCalls
            exact ⟨selected, selected.body_read_cutoff
              (SourceCoreCompiler.compile_checked_source compiledEq)⟩
          for retained in named.specialized.function.typedBody.nodes.attach do
            match nodeEq : retained.val with
            | .statement _ => pure ()
            | .expression node =>
              match form : node.form with
              | .reference name (.local binder) =>
                have nodeMember : .expression node ∈ named.specialized.function.typedBody.nodes := by
                  simpa only [nodeEq] using retained.property
                have _actualLookup : ∃ selected : SourceCompiledLocalFinalization.BodySelection compiled named.specialized options.checkingFuel,
                    SourceInferenceExecution.ActualLocalRead.Origin selected.inferenceCall node := by
                  obtain ⟨selected, calls⟩ := exactCalls
                  exact ⟨selected, calls node nodeMember name binder form⟩
                localReadCalls := localReadCalls + 1
                if (SourceSpecializationWorklist.localLambdaBindings named.specialized.function.typedBody).any
                    (fun binding => binding.binder.id == binder) then
                  generalizedReadCalls := generalizedReadCalls + 1
              | _ => pure ()
          match instancesAccepted : SourceSpecializationWorklist.localLambdaInstances named.specialized.function.typedBody with
          | .error error => throw (IO.userError s!"local instances: {reprStr error}")
          | .ok instances =>
            for localInstance in instances.attach do
              match bodyAccepted : SourceSpecializationWorklist.localLambdaBodyNodes
                  named.specialized.function.typedBody localInstance.val with
              | .error error => throw (IO.userError s!"local lexical body: {reprStr error}")
              | .ok bodyNodes =>
                let bodySource := {named.specialized.function.typedBody with nodes := bodyNodes}
                for nested in (initializedLetBindings bodySource).attach do
                  if different : nested.val.binder.id ≠ localInstance.val.binding.binder.id then
                    have _actualNestedOrder : nested.val.binder.id.binderIndex <
                        localInstance.val.binding.binder.id.binderIndex := by
                      obtain ⟨selected, _⟩ := exactCalls
                      exact selected.local_lambda_direct_initialized_binder_lt
                        (SourceCoreCompiler.compile_checked_source compiledEq)
                        (SourceSpecializationWorklist.localLambdaInstances_lexical_read_origin
                          instancesAccepted localInstance.val localInstance.property)
                        bodyAccepted nested.property different
                    unless nested.val.binder.id.binderIndex < localInstance.val.binding.binder.id.binderIndex do
                      throw (IO.userError "nested initialized owner is not before its containing declaration")
                    nestedOwners := nestedOwners + 1
                for retained in bodyNodes.attach do
                  match nodeEq : retained.val with
                  | .statement _ => pure ()
                  | .expression expression =>
                    match form : expression.form with
                    | .reference name (.local target) =>
                      have member : Node.expression expression ∈ bodyNodes := by
                        simpa only [nodeEq] using retained.property
                      have _actualOrder : target.binderIndex <
                          localInstance.val.binding.binder.id.binderIndex := by
                        obtain ⟨selected, _⟩ := exactCalls
                        have graph : OccurrenceGraphClosed named.specialized.function.typedBody := by
                          rw [selected.source]
                          exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
                            named.specialized.parameterSubstitution selected.body.resources.graph_closed
                        have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
                          graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist
                          bodyAccepted member
                        exact selected.local_lambda_descendant_read_binder_lt
                          (SourceCoreCompiler.compile_checked_source compiledEq)
                          (SourceSpecializationWorklist.localLambdaInstances_lexical_read_origin
                            instancesAccepted localInstance.val localInstance.property)
                          (SourceSpecializationWorklist.localLambdaBodyNodes_members bodyAccepted member)
                          path form
                      unless target.binderIndex < localInstance.val.binding.binder.id.binderIndex do
                        throw (IO.userError "actual local lexical read is not before its owner")
                      orderedLexicalReads := orderedLexicalReads + 1
                      if (SourceSpecializationWorklist.localLambdaBindings named.specialized.function.typedBody).any
                          (fun binding => binding.binder.id == target) then
                        orderedGeneralizedReads := orderedGeneralizedReads + 1
                    | _ => pure ()
          let original ← match compiled.program.functions.find?
              (fun function => function.declaration == named.specialized.function.declaration) with
            | some original =>
                ordinary := ordinary + 1
                pure original
            | none =>
                let some method := compiled.program.methods.find?
                    (fun method => method.checked.declaration == named.specialized.function.declaration)
                  | throw (IO.userError "cache body has no actual ordinary or method origin")
                methods := methods + 1
                methodTemplates := methodTemplates + (localSchemeTemplateOwners method.checked.typedBody).length
                pure method.checked
          for current in initializedLetBindings original.typedBody do
            for other in initializedLetBindings original.typedBody do
              if current.binder.id != other.binder.id &&
                  !current.binder.scheme.quantified.isEmpty && !other.binder.scheme.quantified.isEmpty then
                unless current.binder.scheme.quantified.all (fun q => !other.binder.scheme.quantified.contains q) do
                  throw (IO.userError "distinct initialized owners share a quantified variable")
                separatedPairs := separatedPairs + 1
          for owner in localSchemeTemplateOwners original.typedBody do
            let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
            unless free.all owner.binder.scheme.quantified.contains do
              throw (IO.userError "original body template escapes its complete owner")
            let some solved := original.solvedRequirements.find?
                (fun solved => solved.id == owner.requirement.templateRequirement)
              | throw (IO.userError "original body template has no solved row")
            unless solved.predicate == owner.requirement.predicate do
              throw (IO.userError "original body predicate changed in solved ledger")
            templates := templates + 1
            variables := variables + free.length
      unless compiled.plan.specializations.length == 1 && ordinary > 1 && methods > 0 && methodTemplates > 0 && templates > 0 && variables > 0 && separatedPairs > 0 && localReadCalls > 0 && generalizedReadCalls > 0 && orderedLexicalReads > 0 && orderedGeneralizedReads > 0 && nestedOwners > 0 do
        throw (IO.userError s!"method coverage changed: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, variables={variables}")
      IO.println s!"PASS cached ordinary and method template scope: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, flexible variables={variables}, separated owner pairs={separatedPairs}, exact local calls={localReadCalls}, generalized reads={generalizedReadCalls}, ordered lexical reads={orderedLexicalReads}, ordered generalized reads={orderedGeneralizedReads}, nested initialized owners={nestedOwners}"

end Tests.SourceBodyTemplateScope
end

section
-- leanmerge: from Solcore.Test.SourceCachedTemplateScope
/-! Raw public compilation prepares an implementation method and its ordinary
helper after the initial worklist. The unchanged nested helper retains its
nonempty original template predicate at the actual completed cache position. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCachedTemplateScope
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceSemantics.CoreLowering

private theorem catalog_scope {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    (∃ original ∈ compiled.program.functions,
      named.specialized.function = SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      (∀ owner, ContainsLocalSchemeTemplate original.typedBody owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified)) ∨
    (∃ method : ExecutableImplMethods.CheckedMethod,
      Nonempty (CallableCoercionBodyProvenance.Selection cached.sourceProgram method) ∧
      named.specialized = method.specialized) := by
  have finalMember := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ finalMember
  generalize rowEq : named.specialized = row at origin
  cases origin with
  | ordinary ordinary =>
      rw [← rowEq] at ordinary
      apply Or.inl
      simpa only [← rowEq] using SourceCachedTemplateScope.cached_origin_scope artifact checked position ordinary
  | method selected => exact .inr ⟨_, ⟨selected⟩, rfl⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, (Word, Bool)> { function coerce(value: Bool) returns ((Word, Bool)) { return run(value); } }",
    "function entry(flag: Bool) returns (Word, Bool) { return flag; }"]}] }

def main : IO Unit := do
  let checked ← match checkProgram workspace 4096 with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"checker: {reprStr error}")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "entry")
    | throw (IO.userError "missing entry")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    match artifact : compiled.artifact? with
    | none => throw (IO.userError "missing completed artifact")
    | some cached =>
      let mut ordinary := 0
      let mut methods := 0
      let mut late := 0
      let mut templates := 0
      let mut variables := 0
      for index in List.range cached.indexed.base.functions.length do
        match position : cached.indexed.base.functions[index]? with
        | none => throw (IO.userError "missing cache position")
        | some named =>
          have _actualScope := catalog_scope artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          match compiled.program.functions.find?
              (fun function => function.declaration == named.specialized.function.declaration) with
          | none => methods := methods + 1
          | some original =>
            ordinary := ordinary + 1
            if !(compiled.plan.specializations.map (·.key)).contains named.specialized.key then
              late := late + 1
              for owner in localSchemeTemplateOwners original.typedBody do
                let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
                unless free.all owner.binder.scheme.quantified.contains do
                  throw (IO.userError "late original template escapes its complete owner")
                let some solved := original.solvedRequirements.find?
                    (fun solved => solved.id == owner.requirement.templateRequirement)
                  | throw (IO.userError "late original template has no solved row")
                unless solved.predicate == owner.requirement.predicate do
                  throw (IO.userError "late original predicate changed in solved ledger")
                templates := templates + 1
                variables := variables + free.length
      unless compiled.plan.specializations.length == 1 && ordinary > 1 && methods > 0 && late > 0 && templates > 0 && variables > 0 do
        throw (IO.userError s!"late coverage changed: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, late={late}, templates={templates}, variables={variables}")
      IO.println s!"PASS cached ordinary template scope: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, late={late}, templates={templates}, flexible variables={variables}"

end Tests.SourceCachedTemplateScope
end

section
-- leanmerge: from Solcore.Test.SourceCallStageBoundary
/-! A stage failure precedes even an absent argument occurrence. A Core callee
write remains visible, while the argument's different write is skipped. The
latter test is universal over authenticated dispatch receipts, without assuming
an argument or callable-body evaluation. -/

set_option autoImplicit false
namespace Tests.SourceCallStageBoundary
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"call_stage_boundary", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "call_stage_boundary.solc"⟩, 0, 1⟩
private def parameter : TypedBinder := { id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := true }
private def node : ExpressionNode := { id := id 1, span, type := .function .word .unit, form := .lambda [parameter] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression (id 1)], nodes := [.expression node] }
private def program : Program := ⟨⟨[], [], [], [], [], []⟩, [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures program.signatures
private def function : Dynamic.Closure := {
  parameters := [parameter], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def contract : Staging.CallGuard.Contract := ⟨[parameter], false⟩
private def frame : Staging.CallBoundary.Frame where
  stages := ⟨false, .unit, fun _ => some .runtime⟩
  Binds value selected := value = .closure function ∧ selected = contract
  userCallable := by rintro value selected ⟨rfl, _⟩; exact .closure _
  unique := by rintro value left right ⟨_, rfl⟩ ⟨_, rfl⟩; rfl
private def reason : Staging.CallGuard.Fault := .argumentStage 0 (id 2) .runtime
private def metadata : IndirectCallResolution := { argumentCount := 1, argumentTypeBeforeCoercion := .word, argumentTypeAfterCoercion := .word }

private theorem rejected : Staging.CallBoundary.GuardRejects frame (id 0) [id 2] (.closure function) reason := by
  apply Staging.CallBoundary.GuardRejects.contract (show frame.Binds (.closure function) contract from ⟨rfl, rfl⟩)
  apply Staging.CallGuard.Rejects.arguments
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .head (.wrongStage (.inr (.inl rfl)) rfl (by decide))

private theorem callee (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context [] source [] heap (id 1) (.closure function) heap :=
  .intro ⟨List.mem_singleton_self _, rfl⟩ (.lambda rfl (.nil heap)) .nil

/-- The absent argument would fail if evaluated. -/
example (heap : Dynamic.Heap) : Dynamic.ExpressionFaults program context [] source [] heap (id 2)
    (.missingExpression (id 2)) heap := by
  apply Dynamic.ExpressionFaults.missing
  exact .expression (by decide) (.nil _)

/-- The call boundary nevertheless reports the earlier stage failure, with no
argument execution in its derivation. -/
example (heap : Dynamic.Heap) :
    Staging.CallBoundary.Executes program frame context [] source [] heap (id 0) (id 1) [id 2] metadata (.stageFault reason) heap :=
  .stageRejected (callee heap) rejected

example : ¬ Staging.CallBoundary.GuardAccepts frame (id 0) [id 2] (.closure function) := by
  intro accepted
  exact accepted.not_rejects rejected

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def calleeCode : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 11))) (Core.LanguageResult.success (.var 2))
private def argumentCode : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 22))) (Core.LanguageResult.success .unit)

/-- Any authenticated row with these original source-stage facts retains only
the callee's write. The argument would write 22, and is not evaluated. -/
example (site : SourceCoreCallableContracts.Callsite) (carrier : Core.Value)
    (dispatch : CallStageBoundary.Dispatch frame site (id 0) [id 2] (.closure function) carrier) :
    Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      (site.lower (word 99) .unit calleeCode argumentCode)
      (.inLeft .unit (.word (dispatch.reason reason))) [.word (word 11)] := by
  have calleeEvaluation : Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      calleeCode (.inRight .word carrier) [.word (word 11)] :=
    .letE (.storeCell (.var rfl) rfl .word rfl) (.inRight (.var rfl))
  have wrapped : Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      calleeCode (.inRight .word (.pair dispatch.function (.word dispatch.contract))) [.word (word 11)] := by
    rw [← dispatch.shape]
    exact calleeEvaluation
  exact site.lower_stage_failure (word 99) dispatch.row _ dispatch.found (dispatch.rejected rejected) wrapped

/-- Static receipt reflection reconstructs independent acceptance. It does not
use an evaluated argument or function body as a premise. -/
example (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceValue : Dynamic.Value) (carrier : Core.Value)
    (dispatch : CallStageBoundary.Dispatch frame site call arguments sourceValue carrier)
    (passed : dispatch.row.beforeArguments = .ok ()) :
    Staging.CallBoundary.GuardAccepts frame call arguments sourceValue :=
  dispatch.accepted_iff.mp passed

end Tests.SourceCallStageBoundary
end

section
-- leanmerge: from Solcore.Test.SourceCallStageGuards
/-! Stage-guard ordering and bypass regressions in independent source rules.
The compiler equivalence is universal over all retained caller/contract metadata;
these examples exercise the ordering cases most easily lost in a refactor. -/

set_option autoImplicit false
namespace Tests.SourceCallStageGuards
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Staging.CallGuard

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"call_stage_guards", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def parameter (index : Nat) (comptime : Bool) (type : TypeSystem.Ty := .word) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "parameter", scheme := .mono type, comptime }
private def ordinary : Frame := ⟨false, .unit, fun _ => some .runtime⟩
private def firstKnown : Frame := ⟨false, .unit, fun expression => if expression = id 1 then some .comptime else none⟩
private def argumentsKnown : Frame := ⟨false, .unit, fun expression => if expression = id 0 then some .runtime else some .comptime⟩

private theorem not_effectful : ¬ Effectful ordinary := by
  rintro (flag | only)
  · cases flag
  · cases only

private theorem runtime_word : ¬ RequiresComptime false (parameter 0 false) := by
  rintro (force | explicit | only)
  · cases force
  · cases explicit
  · cases only

/-- A parameter without a comptime requirement does not inspect its stage. -/
example : Accepts ordinary ⟨[parameter 0 false], false⟩ (id 0) [id 1] :=
  .ordinary not_effectful (.cons (.ordinary runtime_word) (.nil _)) (.ordinary rfl)

/-- Earlier stage mismatch wins over the missing trailing argument. -/
private theorem first_failure : Rejects ordinary ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1]
    (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inr (.inl rfl)) rfl (by decide)))

example : ¬ Rejects ordinary ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1] (.arity 1 0) := by
  intro later
  have impossible := first_failure.functional later
  cases impossible

/-- After a successful first parameter, the arity diagnostic counts the
remaining suffix. It does not report the original full list lengths. -/
example : Rejects firstKnown ⟨[parameter 0 true, parameter 1 true], false⟩ (id 0) [id 1] (.arity 1 0) := by
  apply Rejects.arguments
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .tail (.comptime (by simp [firstKnown])) (.parametersRemain 1 (parameter 1 true) [])

/-- A staged result forces ordinary-looking parameters to be comptime too. -/
example : Rejects ordinary ⟨[parameter 0 false], true⟩ (id 0) [id 1] (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inl rfl) rfl (by decide)))

/-- Result availability is checked only after every argument passes. -/
example : Rejects argumentsKnown ⟨[parameter 0 false], true⟩ (id 0) [id 1] (.resultStage .runtime) := by
  apply Rejects.result
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .cons (.comptime (by decide)) (.nil _)
  · exact .wrongStage rfl (by simp [argumentsKnown]) (by decide)

/-- Native Integer retains its source staging requirement independently of
whether its runtime carrier can be represented by Core. -/
example : Rejects ordinary ⟨[parameter 0 false .integer], false⟩ (id 0) [id 1] (.argumentStage 0 (id 1) .runtime) :=
  .arguments not_effectful (.head (.wrongStage (.inr (.inr .integer)) rfl (by decide)))

/-- An effectful-staging caller bypasses this pre-argument check, including its
arity check. Ordinary callable application checks arity after argument effects. -/
example : Accepts ⟨false, .integer, fun _ => none⟩ ⟨[parameter 0 true], true⟩ (id 0) [] :=
  .effectful (.inr .integer)

example : Accepts ⟨true, .unit, fun _ => none⟩ ⟨[parameter 0 true], true⟩ (id 0) [] :=
  .effectful (.inl rfl)

/-- The sealed metadata receipt is interpreted by the independent relation,
including all exact diagnostic coordinates and source stages. -/
example (guard : SourceCoreStageContracts.Guard) (diagnostic : SourceCompilationPlan.Error)
    (failed : guard.decision = .error diagnostic) :
    ∃ reason, Rejects (CoreLowering.CallStageGuard.frame guard.sidecar.caller)
      ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments reason ∧
      diagnostic = CoreLowering.CallStageGuard.error guard.sidecar.caller guard.node guard.contract.owner reason :=
  (CoreLowering.CallStageGuard.guard_rejects_iff guard diagnostic).mp failed

end Tests.SourceCallStageGuards
end

section
-- leanmerge: from Solcore.Test.SourceCallableLedger
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Same erased function type, different original staging contracts. Additional
checks cover descriptor membership beyond Core typing and public-factory
coverage without a supplied row/guard certificate. -/

set_option autoImplicit false
namespace Tests.SourceCallableLedger
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"callable_ledger", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def parameter (marked : Bool) : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := marked }
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def function (marked : Bool) : Dynamic.Closure := {
  parameters := [parameter marked], resultType := .unit, body := [], source, captured := []
  context := Context.ofSignatures ⟨[], [], [], [], [], []⟩, evidence := [] }
private def contract (marked : Bool) : Staging.CallGuard.Contract := ⟨[parameter marked], false⟩
private def plan : SourceSpecializationWorklist.Plan := ⟨[], [], [], []⟩
private def stages : Staging.CallGuard.Frame := ⟨false, .unit, fun _ => some .runtime⟩
private def ledger : Staging.CallBoundary.Frame := {
  stages, Binds := CallableLedger.Binds plan
  userCallable := CallableLedger.Binds.userCallable, unique := CallableLedger.Binds.unique }

private theorem bound (marked : Bool) : ledger.Binds (.closure (function marked)) (contract marked) := by
  apply CallableLedger.Binds.closure rfl
  constructor
  · intro impossible; cases impossible
  · intro impossible; cases impossible

private theorem ordinaryCaller : ¬ Staging.CallGuard.Effectful stages := by
  rintro (marked | only)
  · cases marked
  · cases only

/-- Even the full source function type omits the explicit parameter flag. -/
example : FunctionValues.sourceType (function true) = FunctionValues.sourceType (function false) := rfl

/-- The ledger preserves that flag before the argument is evaluated. -/
example : Staging.CallBoundary.GuardRejects ledger (id 0) [id 1] (.closure (function true))
    (.argumentStage 0 (id 1) .runtime) := by
  apply Staging.CallBoundary.GuardRejects.contract (bound true)
  apply Staging.CallGuard.Rejects.arguments ordinaryCaller
  exact .head (.wrongStage (.inr (.inl rfl)) rfl (by decide))

example : Staging.CallBoundary.GuardAccepts ledger (id 0) [id 1] (.closure (function false)) := by
  apply Staging.CallBoundary.GuardAccepts.contract (bound false)
  apply Staging.CallGuard.Accepts.ordinary ordinaryCaller
  · apply Staging.CallGuard.ArgumentsAccept.cons
    · apply Staging.CallGuard.ArgumentAccepts.ordinary
      rintro (forced | marked | only)
      · cases forced
      · cases marked
      · cases only
    · exact .nil _
  · exact .ordinary rfl

/-- Core typing alone cannot admit an unregistered contract word, even when
an underlying payload relation accepts the function code and captures. -/
example {catalog : SourceCoreDataCatalog.Catalog} (underlying : CoreLowering.GenericHeap.PayloadModel catalog)
    (table : SourceCoreStageCodebook.Table) (mapping : CoreLowering.GeneralHeap.LocationMap)
    (world : Core.StoreTyping) (sourceType : TypeSystem.Ty) (value : Dynamic.Value) (raw : Core.Value)
    (word : Core.Word) (type : Core.Ty)
    (_typed : Core.RuntimeValueHasType world (.pair raw (.word word)) type catalog.definitions)
    (absent : ∀ entry, entry ∈ table.entries → entry.id ≠ word) :
    ¬ (CallableLedger.model underlying plan table).Represents mapping world sourceType value (.pair raw (.word word)) type := by
  intro represented
  obtain ⟨entry, member, same⟩ := AuthenticatedCallableLedger.descriptor_member represented.2
  exact absent entry member same

/-- The real public preparation result supplies dispatch coverage. There is
no external premise asserting a selected guard or a successful child call. -/
example {catalog : SourceCoreDataCatalog.Catalog} (underlying : CoreLowering.GenericHeap.PayloadModel catalog)
    {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan} {checked : SourceCoreDataCatalog.Checked}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (prepared : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying plan site.table) (CallableLedger.frame sidecar)
      site site.call arguments sourceType type := by
  intro mapping world value carrier contract represented bound
  exact AuthenticatedCallableLedger.covers_of_prepare underlying prepared caller contains form sourceType type represented bound

/-- Contextual source alignment preserves the complete active substitution,
not merely a final erased parameter/result type. -/
example (plan : SourceCoreStageCodebook.Plan) (sidecar : SourceCoreStageContracts.Sidecar)
    (prepared : SourceCoreLocalEvidence.Prepared) (id : ExpressionId) (contract : SourceCoreStageContracts.Contract)
    (selected : SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar)
    (accepted : SourceCoreStageContracts.Contract.contextualLambda sidecar prepared id = .ok contract) :
    (AuthenticatedCallableLedger.LambdaSource.contextual sidecar prepared id contract selected accepted).source =
      sidecar.source.applySubstitution prepared.substitution := rfl

end Tests.SourceCallableLedger
end

section
-- leanmerge: from Solcore.Test.SourceCompiledCatalogedCallOrigins
/-! The full original nested qualified program exercises finalized template
emitters and same-prefix initializer receipts through public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledCatalogedCallOrigins
open Solcore Frontend SourceInference SourceSemantics TypeSystem CatalogedDirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration instantiation) => expression.requirements.contains requirement && catalog.contains instantiation.declaration
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledCatalogedCallOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes template.val do
          throw (IO.userError "finalized template lost its cataloged selected cataloged emitter")
        templates := templates + 1
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original cataloged emitter")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected cataloged emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS cataloged public compilation: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}"

end Tests.SourceCompiledCatalogedCallOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCompiledDirectCallOrigins
/-! A complete nested qualified source program exercises actual direct
requirement issuance, final solving and selected public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledDirectCallOrigins
open Solcore Frontend SourceInference SourceSemantics TypeSystem DirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration _) => expression.requirements.contains requirement
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut rows := 0
    for caller in compiled.plan.specializations.attach do
      have _public := SourceCompiledDirectCallOrigins.compile_direct_emitters compiledEq caller.property
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original emitter")
          unless hasEmitter caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 do
      throw (IO.userError "empty direct emitter coverage")
    IO.println s!"PASS public compilation: rows={rows}, issued requirements={emitted}"

end Tests.SourceCompiledDirectCallOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCompiledDirectCallPredicateOrigins
/-! The full original nested qualified program exercises finalized template
emitters and same-prefix initializer receipts through public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledDirectCallPredicateOrigins
open Solcore Frontend SourceInference SourceSemantics TypeSystem DirectCallPredicateEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : Requirement) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration instantiation) => expression.requirements.contains requirement.id && catalog.contains instantiation.declaration && instantiation.predicates.contains requirement.predicate
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledDirectCallPredicateOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        let some solved := caller.val.function.solvedRequirements.find? (fun row => row.id == template.val)
          | throw (IO.userError "template has no solved requirement")
        unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes
            { id := template.val, predicate := solved.predicate } do
          throw (IO.userError "finalized template lost its matching finalized call predicate")
        templates := templates + 1
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          let some rawRow := body.state.requirements.find? (fun row => row.id == requirement.val)
            | throw (IO.userError "direct ID has no raw ledger row")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) body.state.nodes rawRow do
            throw (IO.userError "issued requirement lost its original call predicate")
          let some solved := caller.val.function.solvedRequirements.find? (fun row => row.id == requirement.val)
            | throw (IO.userError "direct ID has no solved ledger row")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes
              { id := requirement.val, predicate := solved.predicate } do
            throw (IO.userError "issued requirement lost its specialized call predicate")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS predicate-paired public compilation: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}"

end Tests.SourceCompiledDirectCallPredicateOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCompiledNestedInitializerPrivacy
/-! Public compilation exercises a nonempty inner generalized template,
nonzero outer and inner positions, and later uses of both closures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledNestedInitializerPrivacy
open Solcore Frontend SourceInference SourceSemantics TypeSystem

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let before = flag;",
    "let outer = lam(value, tag) { let prior = true; let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, before);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some signature := program.signatures.functions.find? (fun signature => signature.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match accepted : SourceCoreCompiler.compile workspace [.declaration signature.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut connected := 0
    for row in compiled.plan.specializations.attach do
      have _continuation := SourceCompiledLocalFinalization.compile_nested_lambda_privacy
        accepted row.property
      connected := connected + 1
    let some original := compiled.program.functions.find? (fun function => function.declaration == signature.id)
      | throw (IO.userError "missing original selected checker body")
    let bindings := initializedLetBindings original.typedBody
    let some outer := bindings.find? (fun binding => binding.binder.name == "outer")
      | throw (IO.userError "missing outer initialized binder")
    let some inner := bindings.find? (fun binding => binding.binder.name == "inner")
      | throw (IO.userError "missing inner initialized binder")
    unless !inner.binder.scheme.quantified.isEmpty && !inner.binder.schemeRequirements.isEmpty do
      throw (IO.userError "inner quantified template coverage is empty")
    unless !outer.binder.scheme.quantified.isEmpty do
      throw (IO.userError "outer quantified coverage is empty")
    for q in inner.binder.scheme.quantified do
      if outer.binder.scheme.quantified.contains q then
        throw (IO.userError "inner quantifier entered the outer scheme")
    let some outerValue := original.typedBody.nodes.findSome? (fun node => match node with
        | .expression expression =>
            if NodeId.expression expression.id == outer.initializer then some expression else none
        | _ => none)
      | throw (IO.userError "missing actual outer initializer expression")
    for q in inner.binder.scheme.quantified do
      if outerValue.type.freeVariables.contains q then
        throw (IO.userError "inner quantifier escaped into the finalized outer lambda result")
    unless connected > 0 do throw (IO.userError "public selected row coverage is empty")
    IO.println s!"PASS nested initializer final privacy: selected rows={connected}, inner quantifiers={inner.binder.scheme.quantified.length}, outer quantifiers={outer.binder.scheme.quantified.length}, inner templates={inner.binder.schemeRequirements.length}"

end Tests.SourceCompiledNestedInitializerPrivacy
end

section
-- leanmerge: from Solcore.Test.SourceCompiledTemplateCallOrigins
/-! The full original nested qualified program exercises finalized template
emitters and same-prefix initializer receipts through public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledTemplateCallOrigins
open Solcore Frontend SourceInference SourceSemantics TypeSystem DirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration _) => expression.requirements.contains requirement
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledTemplateCallOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        unless hasEmitter caller.val.function.typedBody.nodes template.val do
          throw (IO.userError "finalized template lost its selected emitter")
        templates := templates + 1
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original emitter")
          unless hasEmitter caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS public compilation: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}"

end Tests.SourceCompiledTemplateCallOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCompiledTemplateCallOwner
/-! The unchanged full nested qualified program makes the actual prepared
open-call owner connection nonempty through raw public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledTemplateCallOwner
open Solcore Frontend SourceInference SourceSemantics TypeSystem CatalogedDirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration instantiation) => expression.requirements.contains requirement && catalog.contains instantiation.declaration
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    let mut openTemplates := 0
    let mut instances := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledCatalogedCallOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        have _owner := SourceCompiledTemplateCallOwner.template_owner compiledEq caller.property template.property
        let openEmitter := caller.val.function.typedBody.nodes.any fun node => match node with
          | .expression expression => match expression.form with
            | .call _ _ (.declaration instantiation) =>
                expression.requirements.contains template.val &&
                  !SourcePreparedOpenCallEdges.InstantiationClosed instantiation
            | _ => false
          | _ => false
        if openEmitter then openTemplates := openTemplates + 1
        unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes template.val do
          throw (IO.userError "finalized template lost its selected cataloged emitter")
        templates := templates + 1
      match SourceSpecializationWorklist.localLambdaInstances caller.val.function.typedBody with
      | .error error => throw (IO.userError s!"actual local discovery: {reprStr error}")
      | .ok discovered => instances := instances + discovered.length
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original cataloged emitter")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected cataloged emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 && openTemplates > 0 && instances > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS prepared template owners: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}, open templates={openTemplates}, actual instances={instances}"

end Tests.SourceCompiledTemplateCallOwner
end

section
-- leanmerge: from Solcore.Test.SourceDynamicInitialization
/-! Successful expression execution preserves initialization of existing
locations, without typing assumptions. The stronger property excludes clearing
writes even though the independent heap relation can describe them. -/
set_option autoImplicit false
namespace Tests.SourceDynamicInitialization
open Solcore Solcore.SourceSemantics Solcore.SourceSemantics.Dynamic
open Solcore.Frontend Solcore.Frontend.SourceInference

example {program : Program} {context : SourceSemantics.Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {value : Value} {location : Location} {cell : Cell}
    (trace : ExpressionEvaluates program context evidence source environment before id value after)
    (read : Heap.Reads before location cell) (initialized : cell.value ≠ none) :
    ∃ current, Heap.Reads after location current ∧ current.value ≠ none :=
  trace.initialization_extends location cell read initialized

private def initialized : Cell := ⟨.bool, some (.bool false), none⟩
private def cleared : Cell := ⟨.bool, none, none⟩

example : Heap.Writes ⟨[initialized]⟩ ⟨0⟩ none ⟨[cleared]⟩ :=
  .intro (.intro .head) .head

example : ¬ HeapInitializationExtend ⟨[initialized]⟩ ⟨[cleared]⟩ := by
  intro extension
  obtain ⟨current, read, nonempty⟩ := extension ⟨0⟩ initialized (.intro .head) (by decide)
  have same := read.functional (show Heap.Reads ⟨[cleared]⟩ ⟨0⟩ cleared from .intro .head)
  subst current
  exact nonempty rfl

example {before middle after : Heap} {location : Location} {cell : Cell}
    {type : TypeSystem.Ty} {allocated : Location} {value : Value}
    (read : Heap.Reads before location cell) (initialized : cell.value ≠ none)
    (allocation : Heap.Allocates before type none allocated middle)
    (write : Heap.Writes middle allocated (some value) after) :
    ∃ current, Heap.Reads after location current ∧ current.value ≠ none :=
  ((HeapInitializationExtend.of_allocation allocation).trans
    (HeapInitializationExtend.of_write write)) location cell read initialized

#print axioms ExpressionEvaluates.initialization_extends
#print axioms StatementExecutes.initialization_extends
#print axioms ForLoopExecutes.initialization_extends
end Tests.SourceDynamicInitialization
end

section
-- leanmerge: from Solcore.Test.SourcePreparedQualifiedLocalReadBindings
/-! Nonempty compilation checks for the original selected qualified-reference
receipt, including a nested owner which retains a separate type variable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourcePreparedQualifiedLocalReadBindings
open Solcore Frontend SourceInference SourceSemantics

private def workspace (body : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" ([
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }"
  ] ++ body)}] }

private def references (compiled : SourceCoreCompiler.Compiled) : IO Nat := do
  let mut count := 0
  for caller in compiled.plan.specializations.attach do
    for item in caller.val.function.typedBody.nodes.attach do
      match itemEq : item.val with
      | .statement _ => pure ()
      | .expression node =>
        match form : node.form with
        | .reference name (.local localId) =>
          match found : SourceCompilationPlan.directLambdaLetBinder?
              caller.val.function.typedBody localId with
          | none => pure ()
          | some binder =>
            if qualified : binder.schemeRequirements ≠ [] then
              have present : .expression node ∈ caller.val.function.typedBody.nodes := by
                rw [← itemEq]; exact item.property
              have _certificate := SourcePreparedQualifiedLocalReadBindings.compiled_selected
                compiled caller.property present form found qualified
              let some owned := SourceCompilationPlan.ordinaryOwnedRequirements? node
                | throw (IO.userError "missing ordinary requirement spine")
              let ownNode := {node with type := node.rawType, requirements := owned, coercions := []}
              let .ok (substitution, bindings) :=
                  SourceCompilationPlan.localRequirementBindings caller.val binder ownNode
                | throw (IO.userError "qualified bindings rejected")
              unless bindings.map (fun binding => (binding.template, binding.actualRequirement)) ==
                  binder.schemeRequirements.zip owned do
                throw (IO.userError "template/actual pairing")
              for template in binder.schemeRequirements.attach do
                have _excludes := fun metavariable (outside : metavariable ∉ binder.scheme.quantified) =>
                  SourcePreparedQualifiedLocalReadBindings.compiled_template_excludes
                    compiled caller.property present form found qualified template.property outside
                for metavariable in TypedTraitResolution.predicateVariables template.val.predicate do
                  unless binder.scheme.quantified.contains metavariable do
                    throw (IO.userError "captured template variable")
              for binding in bindings do
                unless (TypedTraitResolution.predicateVariables binding.predicate).isEmpty do
                  throw (IO.userError "ungrounded instantiated predicate")
              IO.println s!"QUALIFIED {name} domain={reprStr substitution.domain} bindings={bindings.length}"
              count := count + 1
            else pure ()
        | _ => pure ()
  pure count

private def checkCase (label : String) (generalizedOuter : Bool) (body : List String) : IO Unit := do
  let .ok program := checkProgram (workspace body) 4096
    | throw (IO.userError s!"{label}: checker rejected")
  let some signature := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError s!"{label}: missing run")
  let .ok compiled := SourceCoreCompiler.compileChecked program [.declaration signature.id]
      {checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128}
    | throw (IO.userError s!"{label}: compiler rejected")
  let outerBinders := compiled.plan.specializations.flatMap fun caller =>
    caller.function.typedBody.nodes.filterMap fun
      | .statement {form := .letDecl binder (some _), ..} =>
          if binder.name == "outer" then some binder else none
      | _ => none
  let [outer] := outerBinders | throw (IO.userError s!"{label}: outer owner")
  unless (!outer.scheme.quantified.isEmpty) == generalizedOuter do
    throw (IO.userError s!"{label}: outer generalization")
  IO.println s!"OUTER quantified={reprStr outer.scheme.quantified}"
  let count ← references compiled
  unless count > 0 do throw (IO.userError s!"{label}: no qualified references")
  IO.println s!"PASS {label}: {count} qualified original references"

def main : IO Unit := do
  checkCase "used-inner" false [
    "function run(flag: Bool) returns (Word) {",
    "let outer = lam(value) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return value; };",
    "return outer(1); }"]
  checkCase "separate-outer-variable" true [
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "return outer(1, flag); }"]

end Tests.SourcePreparedQualifiedLocalReadBindings
end

section
-- leanmerge: from Solcore.Test.SourcePreparedQualifiedLocalReadOwner
/-! Public compilation supplies exact owner and template receipts for a real
nested qualified function while the outer function remains generalized. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourcePreparedQualifiedLocalReadOwner
open Solcore Frontend SourceInference SourceSemantics SourceSpecializationWorklist

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "return outer(1, flag); }"]}] }

private def inspect (compiled : SourceCoreCompiler.Compiled) : IO Unit := do
  let mut qualifiedCount := 0
  let mut outerCount := 0
  for caller in compiled.plan.specializations.attach do
    match discovered : localLambdaInstances caller.val.function.typedBody with
    | .error error => throw (IO.userError s!"discovery: {reprStr error}")
    | .ok instances =>
      for value in instances.attach do
        have _owner := SourcePreparedQualifiedLocalReadOwner.discovered_owner discovered value.property
        unless SourceCompilationPlan.directLambdaLetBinder? caller.val.function.typedBody
            value.val.binding.binder.id == some value.val.binding.binder do
          throw (IO.userError "complete owner mismatch")
        if value.val.binding.binder.name == "outer" then
          unless !value.val.binding.binder.scheme.quantified.isEmpty do
            throw (IO.userError "outer is no longer generalized")
          outerCount := outerCount + 1
        if qualified : value.val.binding.binder.schemeRequirements ≠ [] then
          have _receipt := SourcePreparedQualifiedLocalReadOwner.compiled_instance
            compiled caller.property discovered value.property qualified
          for template in value.val.binding.binder.schemeRequirements.attach do
            for metavariable in (TypedTraitResolution.predicateVariables template.val.predicate).attach do
              have _scoped := SourcePreparedQualifiedLocalReadOwner.compiled_instance_template_scoped
                compiled caller.property discovered value.property template.property metavariable.property
              unless value.val.binding.binder.scheme.quantified.contains metavariable.val do
                throw (IO.userError "template variable outside same inner scheme")
          qualifiedCount := qualifiedCount + 1
  unless qualifiedCount > 0 && outerCount > 0 do
    throw (IO.userError "empty nested owner connection")
  IO.println s!"PASS instances: qualified={qualifiedCount}, generalizedOuter={outerCount}"

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some signature := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let seeds := [SourceCoreCompiler.Seed.declaration signature.id]
  let options : SourceCoreCompiler.Options :=
    {checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128}
  match accepted : SourceCoreCompiler.compileChecked program seeds options with
  | .error error => throw (IO.userError s!"checked compiler: {reprStr error}")
  | .ok compiled =>
    for caller in compiled.plan.specializations.attach do
      have _public := SourcePreparedQualifiedLocalReadOwner.compileChecked_instance_templates
        accepted caller.property
      pure ()
    inspect compiled
    IO.println "PASS compileChecked"
  match accepted : SourceCoreCompiler.compile workspace seeds options with
  | .error error => throw (IO.userError s!"raw compiler: {reprStr error}")
  | .ok compiled =>
    for caller in compiled.plan.specializations.attach do
      have _public := SourcePreparedQualifiedLocalReadOwner.compile_instance_templates
        accepted caller.property
      pure ()
    inspect compiled
    IO.println "PASS compile"

end Tests.SourcePreparedQualifiedLocalReadOwner
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStageArguments
/-! The staged universal reflection interface is instantiated with actual
Boolean compiler receipts. A completed bundle constructs the recursive source
argument trace under an administrative slot. The final machine fixture checks
that an ordinary language failure carrier skips later argument mutations; it
does not stand in for proving a stage guard's metadata. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.SourceRecursiveStageArguments
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap RecursiveStageMeaning RecursiveStageArguments
open DataExpressionSequence (Tree)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"expression_sequence", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "expression_sequence.solc" }
  startByte := 0
  endByte := 1 }
private def node (index : Nat) (value : Bool) : ExpressionNode := {
  id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value) }
private def source : TypedSource := {
  owner
  inputs := []
  roots := [.expression (id 0), .expression (id 1), .expression (id 2)]
  nodes := [.expression (node 0 true), .expression (node 1 false), .expression (node 2 true)] }
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def model := GenericHeap.finitePayload catalog signatures
private def context : SourceSemantics.Context := .ofSignatures signatures
private def code (value : Bool) : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool value)⟩

private inductive Child : Certificate where
  | boolean {scope expression node name value}
      (found : source.lookupExpression? expression = some node)
      (form : node.form = .reference name (.builtinBoolean value))
      (type : node.type = .bool) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Child scope expression (code value)

private def frame : Staging.Recursive.Scope := {
  origin := ⟨owner, [], []⟩, source, owned := rfl, context, evidence := []
  guards := {
    stages := ⟨false, .unit, fun _ => some .runtime⟩
    Binds := fun _ _ => False
    userCallable := by intro _ _ impossible; cases impossible
    unique := by intro _ _ _ impossible; cases impossible } }
private def registry : Staging.Recursive.Registry := {
  Closure := fun _ _ => False
  source := by intro _ _ impossible; cases impossible
  context := by intro _ _ impossible; cases impossible
  evidence := by intro _ _ impossible; cases impossible }

private theorem leaf_reflects (program : SourceSemantics.Program) :
    Reflects model program registry frame context Child (fun _ _ => False) := by
  intro scope expression lowered certified foundNode found mapping world admin sourceEnv canonical actual
    before store ξ value finalStore environments heaps locals layout evaluated
  cases certified with
  | @boolean scope expression selected name boolean known form type requirements coercions =>
    have same : foundNode = selected := Option.some.inj (found.symm.trans known)
    subst foundNode
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((code boolean).expression.rename ξ) (.inRight .word (.bool boolean)) store from .inRight .bool)
    refine ⟨.value (.bool boolean), before, mapping, world, ?_, ?_, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
    · apply Staging.Recursive.Expression.atomicValue (node := selected) (lookupExpression?_sound known)
      · rw [form]; exact .reference _ _
      · exact coercions
      · rw [form, requirements]; exact .builtinBoolean rfl
    · rw [type]
      exact .value ⟨rfl, .bool boolean⟩

private theorem tree : Tree frame.source Child [] [id 0, id 1, id 2] [.bool, .bool, .bool]
    [code true, code false, code true] :=
  .cons (node := node 0 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
    (.cons (node := node 1 false) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)
      (.single (node := node 2 true) (by cbv) (Child.boolean (by cbv) rfl rfl rfl rfl)))

private def packed := SourceCoreCalls.packArguments [code true, code false, code true]
private def output : Value := .inRight .word (.pair (.bool true) (.pair (.bool false) (.bool true)))
example : SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false) := by cbv
example : SourceCoreBasic.lowerExpression 4 source [] (id 2) Word.zero = .ok (code true) := by cbv

example : ∃ types, Tree frame.source Child [] [id 0, id 1] types [code true, code false] := by
  let identify := fun (value : Bool) => id (if value then 0 else 1)
  let compile := fun value => SourceCoreBasic.lowerExpression 4 source [] (identify value) Word.zero
  have trueCompiled : compile true = .ok (code true) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 0) Word.zero = .ok (code true)
    cbv
  have falseCompiled : compile false = .ok (code false) := by
    change SourceCoreBasic.lowerExpression 4 source [] (id 1) Word.zero = .ok (code false)
    cbv
  have compiled : [true, false].mapM compile = .ok [code true, code false] := by
    simp only [List.mapM_cons, List.mapM_nil, trueCompiled, falseCompiled, bind, Except.bind, pure, Except.pure]
  apply Tree.of_mapM identify compile compiled
  intro value lowered accepted
  cases value with
  | false =>
    rw [falseCompiled] at accepted
    cases accepted
    exact ⟨node 1 false, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩
  | true =>
    rw [trueCompiled] at accepted
    cases accepted
    exact ⟨node 0 true, by cbv, Child.boolean (by cbv) rfl rfl rfl rfl⟩

private theorem run : runStateful 100 (.initial packed.expression [.integer 900] []) = .done output [] := by cbv

/-- The Core execution constructs the source vector trace even with an extra
raw administrative environment slot. No source trace is supplied here. -/
example (program : SourceSemantics.Program) : ∃ outcome after finalMap finalWorld,
    Staging.Recursive.Expressions program registry frame context [] ⟨[]⟩ [id 0, id 1, id 2] outcome after ∧
    Result model finalMap finalWorld [.bool, .bool, .bool] [code true, code false, code true]
      (fun _ _ => False) outcome output ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after [] ∧
    LocationMap.Extends [] finalMap ∧ WorldExtends [] finalWorld ∧
    AdministrativePreserved [] [] finalMap [] ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  apply RecursiveStageArguments.reflects tree (leaf_reflects program) (canonical := []) (ξ := Renaming.insertion 0)
    (.nil .nil) .empty .nil (by intro index value impossible; simp at impossible)
  simpa [packed, code, SourceCoreCalls.packArguments, LocalSequence.pair, LanguageResult.bind,
    LanguageResult.success, Expr.rename, Expr.weakenAt, Renaming.insertion, Renaming.lift] using
    runStateful_evaluation_sound run

/-- Updating the same captured cell twice observes source order in both the
returned pair and the final store. -/
private def writeThenRead (value : Int) : SourceCoreBasic.LoweredExpr :=
  ⟨.integer, .letE (.storeCell (.var 0) (.integer value)) (LanguageResult.success (.loadCell (.var 1)))⟩
private def mutations := SourceCoreCalls.packArguments [writeThenRead 11, writeThenRead 22]
example : runStateful 100 (.initial mutations.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inRight .word (.pair (.integer 11) (.integer 22))) [.integer 22] := by cbv

private def failed : SourceCoreBasic.LoweredExpr := ⟨.integer, LanguageResult.failure .integer (.word Word.zero)⟩
private def stops := SourceCoreCalls.packArguments [writeThenRead 11, failed, writeThenRead 22]
example : runStateful 100 (.initial stops.expression [.cellRef .integer 0] [.integer 0]) =
    .done (.inLeft (.product .integer (.product .integer .integer)) (.word Word.zero)) [.integer 11] := by cbv


end Tests.SourceRecursiveStageArguments
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStageErasure
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A successful nested conditional/product and a non-callable failure retain
the same independent ordinary meaning. The rejected call's missing argument
is never evaluated. These are source judgment fixtures, not assertions of
whole checker/compiler coverage. The final theorem exercises the generalized
public-factory provenance API without assuming a child execution. -/
set_option autoImplicit false
namespace Tests.SourceRecursiveStageErasure
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.Staging Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_stage_erasure", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive_stage_erasure.solc"⟩, 0, 1⟩
private def metadata : IndirectCallResolution := {
  argumentCount := 1, argumentTypeBeforeCoercion := .unit,
  argumentTypeAfterCoercion := .unit, argumentCoercions := [] }
private def node (index : Nat) (form : ExpressionForm) : ExpressionNode := { id := id index, span, type := .unit, form }
private def yes : ExpressionNode := node 0 (.reference "true" (.builtinBoolean true))
private def no : ExpressionNode := node 1 (.reference "false" (.builtinBoolean false))
private def grouped : ExpressionNode := node 2 (.group (id 0))
private def pair : ExpressionNode := node 3 (.tuple [id 2, id 1])
private def choice : ExpressionNode := node 4 (.conditional (id 0) (id 3) (id 5))
private def badCall : ExpressionNode := node 5 (.call (id 0) [id 6] (.indirect metadata))
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 4)],
  nodes := [.expression yes, .expression no, .expression grouped, .expression pair, .expression choice, .expression badCall] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def program : Program := ⟨signatures, [], []⟩
private def scope : Recursive.Scope := {
  origin := ⟨owner, [], []⟩, source, owned := rfl, context, evidence := [],
  guards := {
    stages := ⟨false, .unit, fun _ => some .runtime⟩
    Binds := fun _ _ => False
    userCallable := by intro _ _ impossible; cases impossible
    unique := by intro _ _ _ impossible; cases impossible } }
private def registry : Recursive.Registry := {
  Closure := fun _ _ => False
  source := by intro _ _ impossible; cases impossible
  context := by intro _ _ impossible; cases impossible
  evidence := by intro _ _ impossible; cases impossible }

private theorem yesTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 0) (.value (.bool true)) heap :=
  .atomicValue (node := yes) ⟨by simp [scope, source], rfl⟩ (.reference _ _) rfl (.builtinBoolean rfl)

private theorem noTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 1) (.value (.bool false)) heap :=
  .atomicValue (node := no) ⟨by simp [scope, source], rfl⟩ (.reference _ _) rfl (.builtinBoolean rfl)

private theorem pairTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 3) (.value (.product (.bool true) (.bool false))) heap := by
  apply Recursive.Expression.pair (left := id 2) (right := id 1)
  · exact ⟨pair, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩
  · exact .group ⟨grouped, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap)
  · exact noTrace heap

example (heap : Dynamic.Heap) : Dynamic.ExpressionEvaluates program context [] source [] heap (id 4)
    (.product (.bool true) (.bool false)) heap := by
  apply Recursive.Expression.value_plain (registry := registry) (scope := scope)
  exact .conditional ⟨choice, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap) (pairTrace heap)

/-- The absent argument node cannot be silently evaluated ahead of the
non-callable fault; the ordinary projection keeps the post-callee heap. -/
example (heap : Dynamic.Heap) : Dynamic.ExpressionFaults program context [] source [] heap (id 5) .notCallable heap := by
  apply Recursive.Expression.semanticFault_plain (registry := registry) (scope := scope)
  exact .notCallable ⟨badCall, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap) (by intro impossible; cases impossible)

example {checkedProgram : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    {key : SourceCoreStageCodebook.Key} {lambda : ExpressionId} {active : TypeSystem.Substitution}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda key lambda active)) :
    Nonempty (AuthenticatedCallableLedger.LambdaSite plan table key lambda active descriptor.id) :=
  RecursiveStageProjection.lambda_site_of_descriptor accepted descriptor

end Tests.SourceRecursiveStageErasure
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStageGlobalApplication
/-! Independent global applications retain the selected body scope and its
full heap, including nested staging failure. These consumers require actual
source instantiation/evidence/roots and ordered allocation. The ordinary
erasure traverses the global body in the same mutual fold as callee/arguments. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStageGlobalApplication
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open Staging.Recursive Dynamic

theorem global_stage_failure
    {program : Program} {registry : Registry} {caller child : Scope} {context bodyContext finalContext : SourceSemantics.Context}
    {function : GlobalFunction} {bodyInstance : BodyInstance} {roots : List StatementId}
    {arguments : List Dynamic.Value} {before bound after : Dynamic.Heap} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {origin : Scope} {call : ExpressionId} {reason : Staging.CallGuard.Fault}
    (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
    (covers : function.evidence.Covers bodyInstance.context)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs types bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Statements program registry child bodyContext environment bound roots finalContext
      (.fault (.stage origin call reason)) after) :
    Applies program registry caller context before (.global function) arguments
      (.fault (.stage origin call reason)) after ∧ Generated origin call reason := by
  have executed := Applies.global (scope := caller) (context := context) instantiates covers rootsEq selected parameters allocate body BodyResult.fault
  exact ⟨executed, executed.stage_origin rfl⟩

theorem global_raw_arity
    {program : Program} {registry : Registry} {caller : Scope} {context : SourceSemantics.Context}
    {function : GlobalFunction} {bodyInstance : BodyInstance} {arguments : List Dynamic.Value} {heap : Dynamic.Heap}
    (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
    (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
    Applies program registry caller context heap (.global function) arguments
      (.fault (.semantic (.argumentArityMismatch bodyInstance.source.inputs.length arguments.length))) heap :=
  .globalArity instantiates mismatch

section Erasure
variable {program : Program} {registry : Registry} {scope : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before calleeHeap argumentsHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {function : GlobalFunction} {arguments : List Dynamic.Value}
  (occurrence : Occurrence scope call (.call callee ids (.indirect metadata)))
  (uncoerced : metadata.argumentCoercions = [])
  (calleeRun : Expression program registry scope context environment before callee (.value (.global function)) calleeHeap)
  (guard : Staging.CallBoundary.GuardAccepts scope.guards call ids (.global function))
  (argumentRun : Expressions program registry scope context environment calleeHeap ids (.values arguments) argumentsHeap)
  (arity : ids.length = metadata.argumentCount)

include occurrence uncoerced calleeRun guard argumentRun arity in
theorem global_value_projects {value : Dynamic.Value}
    (invoked : Applies program registry scope context argumentsHeap (.global function) arguments (.value value) after) :
    ExpressionEvaluates program context scope.evidence scope.source environment before call value after := by
  have run := Expression.applied occurrence uncoerced calleeRun guard argumentRun arity invoked
  exact run.value_plain

include occurrence uncoerced calleeRun guard argumentRun arity in
theorem global_fault_projects {reason : SemanticFault}
    (invoked : Applies program registry scope context argumentsHeap (.global function) arguments (.fault (.semantic reason)) after) :
    ExpressionFaults program context scope.evidence scope.source environment before call reason after := by
  have run := Expression.applied occurrence uncoerced calleeRun guard argumentRun arity invoked
  exact run.semanticFault_plain
end Erasure

abbrev actual_named_view := @RecursiveNamedPreparedStagedCalls.Prepared.global_view
abbrev actual_named_scope := @RecursiveNamedPreparedStagedCalls.Prepared.selected_global
abbrev actual_named_body := @RecursiveNamedPreparedStagedCalls.Prepared.applies
abbrev actual_named_arity := @RecursiveNamedPreparedStagedCalls.Prepared.arity_failure

/-- Global views keep empty lexical captures and the exact full invocation
dictionary, independently of all native function type erasure. -/
theorem global_view_capture_and_evidence (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) :
    (globalView body evidence roots).captured = [] ∧ (globalView body evidence roots).evidence = evidence :=
  ⟨rfl, rfl⟩
end Tests.SourceRecursiveStageGlobalApplication
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStagePrimitiveOperators
/-! Primitive operators retain ordered recursive staged children. Actual
numeric validators authenticate only their own literal rows; operator methods
and output coercions remain separate rules. Runtime inspection audits checked
and specialized source metadata and the existing native compiler. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStagePrimitiveOperators
open Solcore Frontend SourceInference SourceSemantics Dynamic Staging.Recursive
open SourceSemantics.CoreLowering

section Numeric
variable {program : Program} {registry : Registry} {scope : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {solved : List SolvedRequirement}
  (contains : ContainsExpression scope.source id node) (form : node.form = .integerLiteral literal resolution)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)

include contains form sameLedger runtime

theorem word_leaf {validated : SourceCoreElaboration.WordIntegerLiteral}
    (accepted : SourceCoreElaboration.validateWordIntegerLiteral solved node literal resolution = .ok validated) :
    Expression program registry scope context environment heap id (.value (.word validated.value)) heap := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound accepted
  apply Expression.atomicValue contains (form ▸ AtomicForm.integerLiteral literal resolution) metadata.coercions
  simpa only [metadata.coercions] using
    NumericLiteralEvidenceReceipts.word_raw accepted form sameLedger runtime program scope.evidence scope.source environment heap

theorem integer_leaf {validated : SourceCoreElaboration.NativeIntegerLiteral}
    (accepted : SourceCoreElaboration.validateNativeIntegerLiteral solved node literal resolution = .ok validated) :
    Expression program registry scope context environment heap id (.value (.integer validated.value)) heap := by
  have metadata := SourceCoreElaboration.validateNativeIntegerLiteral_sound accepted
  apply Expression.atomicValue contains (form ▸ AtomicForm.integerLiteral literal resolution) metadata.coercions
  simpa only [metadata.coercions] using
    NumericLiteralEvidenceReceipts.integer_raw accepted form sameLedger runtime program scope.evidence scope.source environment heap
end Numeric

section Ordered
variable {program : Program} {registry : Registry} {scope origin : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {id left right call : ExpressionId}
  {operator : Syntax.BinaryOp} {reason : Staging.CallGuard.Fault}

theorem word_add {a b : Core.Word} (occurrence : Occurrence scope id (.binary left .add right))
    (first : Expression program registry scope context environment before left (.value (.word a)) middle)
    (second : Expression program registry scope context environment middle right (.value (.word b)) after) :
    Expression program registry scope context environment before id (.value (.word (a.add b))) after ∧
      ExpressionEvaluates program context scope.evidence scope.source environment before id (.word (a.add b)) after := by
  have trace := Expression.binary occurrence first (.strict .add) second (.wordAdd a b)
  exact ⟨trace, trace.value_plain⟩

theorem integer_not {operand : ExpressionId} {a : Int} (occurrence : Occurrence scope id (.unary .bitNot operand))
    (child : Expression program registry scope context environment before operand (.value (.integer a)) after) :
    Expression program registry scope context environment before id (.value (.integer (~~~a))) after :=
  .unary occurrence child (.integerBitNot a)

theorem left_stage_fault (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.binaryLeftFault occurrence first
  exact ⟨trace, trace.stage_origin rfl⟩

theorem right_stage_fault {a : Dynamic.Value} (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.value a) middle)
    (continues : EvaluatesRightOperand operator a)
    (second : Expression program registry scope context environment middle right (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.binaryRightFault occurrence first continues second
  exact ⟨trace, trace.stage_origin rfl⟩

theorem short_circuit_skips_failing_right (occurrence : Occurrence scope id (.binary left .logicalAnd right))
    (first : Expression program registry scope context environment before left (.value (.bool false)) middle)
    (hypothetical : Expression program registry scope context environment middle right (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.value (.bool false)) middle ∧
      Generated origin call reason :=
  ⟨.binaryShortCircuit occurrence first .andFalse, hypothetical.stage_origin rfl⟩

theorem unary_stage_fault {operand : ExpressionId} {op : Syntax.UnaryOp}
    (occurrence : Occurrence scope id (.unary op operand))
    (child : Expression program registry scope context environment before operand (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after :=
  .unaryOperandFault occurrence child

theorem semantic_invalid {a b : Dynamic.Value} (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.value a) middle)
    (continues : EvaluatesRightOperand operator a)
    (second : Expression program registry scope context environment middle right (.value b) after)
    (invalid : BinaryPrimitiveOperandsInvalid operator a b) :
    ExpressionFaults program context scope.evidence scope.source environment before id (.invalidBinaryOperands operator) after :=
  (Expression.binaryInvalid occurrence first continues second invalid).semanticFault_plain
end Ordered

section Boundaries
variable {scope : Scope} {id : ExpressionId} {node : ExpressionNode} {form : ExpressionForm}
  (unique : NodeOccurrencesUnique scope.source) (found : ContainsExpression scope.source id node)

include unique found

theorem required_operator_not_ordinary (required : node.requirements ≠ []) : ¬ Occurrence scope id form := by
  rintro ⟨other, contains, _, empty, _⟩
  have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans (lookupExpression?_complete unique contains))
  exact required (by simpa only [same] using empty)

theorem coerced_operator_not_ordinary (coerced : node.coercions ≠ []) : ¬ Occurrence scope id form := by
  rintro ⟨other, contains, _, _, empty⟩
  have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans (lookupExpression?_complete unique contains))
  exact coerced (by simpa only [same] using empty)
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Core.Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function arithmetic() returns (Word) { return 2 + 3 * 4; }",
  "function inverted() returns (Word) { return ~4; }",
  "function logic() returns (Bool) { return !false && true; }",
  "function skipped() returns (Bool) { let absent: Bool; return false && absent; }",
  "function firstFault() returns (Word) { let first: Word; let second: Word; return first + second; }",
  "function secondFault() returns (Word) { let first: Word = 9; let second: Word; return first + second; }"
]

private def audit (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut operators := 0
  let mut numbers := 0
  for named in compiled.indexed.base.functions do
    let exact ← get "full actual specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (exact == named.specialized) "operator source full record changed"
    let source := exact.function.typedBody
    let ledger := exact.function.solvedRequirements
    for entry in source.nodes do
      match entry with
      | .expression node => match node.form with
        | .unary .. | .binary .. =>
          require (node.requirements.isEmpty && node.coercions.isEmpty) "primitive parent carries requirements/coercions"
          operators := operators + 1
        | .integerLiteral literal resolution =>
          require (node.requirements == [resolution.requirement]) "numeric child lost its owned requirement"
          let _ ← get "actual numeric validator" (SourceCoreElaboration.validateWordIntegerLiteral ledger node literal resolution)
          let selected := ledger.filter (·.id == resolution.requirement)
          require (selected.length == 1) "numeric selection is not the retained singleton"
          numbers := numbers + 1
        | _ => pure ()
      | _ => pure ()
  require (operators == 8 && numbers == 5) s!"unexpected primitive inventory {operators}/{numbers}"

/-- These are real checked-source layouts, before any staged evaluator can
materialize the operators. The generic method remains a distinct nonempty row. -/
private def checked_boundaries : IO Unit := do
  let sources := [
    "function numeric() returns (comptime<integer>) { return 5 + 6; }",
    "trait Add<T> { function add(left: T, right: T) returns (T); } " ++
      "function generic<T>(left: T, right: T) returns (T) where T: Add { return left + right; }"
  ]
  let mut integers := 0
  let mut methods := 0
  let mut literals := 0
  for source in sources do
    let checked ← get "checked integer/method operator boundaries" (checkProgram {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := source}] })
    for function in checked.functions do
      for entry in function.typedBody.nodes do
        match entry with
        | .expression node => match node.form with
          | .binary _ .add _ =>
            if node.requirements.isEmpty then
              require (node.rawType == .integer && node.coercions.isEmpty) "primitive integer parent layout changed"
              integers := integers + 1
            else
              require (!node.requirements.isEmpty && node.coercions.isEmpty) "generic method layout changed"
              methods := methods + 1
          | .integerLiteral literal resolution =>
            require (resolution.targetType == .integer && node.requirements == [resolution.requirement]) "integer child ownership changed"
            let _ ← get "actual Integer validator" (SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node literal resolution)
            literals := literals + 1
          | _ => pure ()
        | _ => pure ()
  require (integers == 1 && methods == 1 && literals == 2) s!"checked integer/method inventory {integers}/{methods}/{literals}"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected) "ordered full heap changed"

def run : IO Unit := do
  let names := ["arithmetic", "inverted", "logic", "skipped", "firstFault", "secondFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive stage primitives" content names
  audit compiled
  checked_boundaries
  for fuel in [0, 1, 37, 300000] do
    for name in names do
      let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let resumed ← get "primitive checkpoint resume" (first.resume 300000)
      match name, resumed.observation with
      | "arithmetic", .done value state => require (reprStr value == reprStr (word 14)) "arithmetic"; cells state []
      | "inverted", .done (.word value) state => require (value == (Core.Word.ofNatModulo 4).bitNot) "unary"; cells state []
      | "logic", .done (.bool true) state => cells state []
      | "skipped", .done (.bool false) state => cells state [(.bool, none)]
      | "firstFault", .fault (.uninitializedLocal binder) state
      | "secondFault", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [row] => pure row | _ => throw (IO.userError "actual fault root missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter
          (·.name == if name == "firstFault" then "first" else "second") with
          | [binder] => pure binder.id | _ => throw (IO.userError "actual fault binder missing")
        require (binder == expected) "operand first fault identity changed"
        cells state [(.word, if name == "firstFault" then none else some (word 9)), (.word, none)]
      | _, other => throw (IO.userError s!"unexpected primitive outcome {name}: {reprStr other}")
  IO.println "recursive staged primitive operators: actual checked metadata / owned numeric rows / ordered native fault heaps / short circuit / resume GREEN"
end Tests.SourceRecursiveStagePrimitiveOperators
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStageTrace
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Nested callee/argument rejection and closure-body frame propagation in the
independent recursive profile. Closure-body composition takes an independent
static ClosureFrame certificate; it takes no child or body execution premise.
These tests do not claim full compiler admission of this restricted profile. -/

set_option autoImplicit false
namespace Tests.SourceRecursiveStageTrace
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Solcore.SourceSemantics.Staging

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_stage_trace", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement : StatementId := ⟨⟨owner, 6⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive_stage_trace.solc"⟩, 0, 1⟩
private def parameter (marked : Bool) : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .unit, comptime := marked }
private def metadata (count : Nat) : IndirectCallResolution := {
  argumentCount := count, argumentTypeBeforeCoercion := .unit,
  argumentTypeAfterCoercion := .unit, argumentCoercions := [] }
private def node (index : Nat) (form : ExpressionForm) : ExpressionNode := { id := id index, span, type := .unit, form }
private def targetNode : ExpressionNode := node 0 (.lambda [parameter true] .unit [])
private def argumentNode : ExpressionNode := node 1 (.tuple [])
private def innerNode : ExpressionNode := node 2 (.call (id 0) [id 1] (.indirect (metadata 1)))
private def calleeNode : ExpressionNode := node 3 (.call (id 2) [] (.indirect (metadata 0)))
private def ordinaryNode : ExpressionNode := node 4 (.lambda [parameter false] .unit [])
private def argumentCallNode : ExpressionNode := node 5 (.call (id 4) [id 2] (.indirect (metadata 1)))
private def returnNode : StatementNode := { id := statement, span, type := .unit, form := .returnStmt (some (id 2)) }
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement statement], nodes := [
    .expression targetNode, .expression argumentNode, .expression innerNode,
    .expression calleeNode, .expression ordinaryNode, .expression argumentCallNode, .statement returnNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def program : Program := ⟨signatures, [], []⟩
private def plan : SourceSpecializationWorklist.Plan := ⟨[], [], [], []⟩
private def guardFrame (effectful : Bool) : CallBoundary.Frame := {
  stages := ⟨effectful, .unit, fun _ => some .runtime⟩
  Binds := CallableLedger.Binds plan
  userCallable := CallableLedger.Binds.userCallable, unique := CallableLedger.Binds.unique }
private def child : Recursive.Scope := {
  origin := ⟨owner, [], [(⟨7⟩, .word)]⟩, source, owned := rfl, context, evidence := [], guards := guardFrame false }
private def caller : Recursive.Scope := {
  child with origin := ⟨owner, [], [(⟨8⟩, .bool)]⟩, guards := guardFrame true }
private def callable (marked : Bool) : Dynamic.Closure := {
  parameters := [parameter marked], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def wrapper : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [statement], source, captured := [], context, evidence := [] }
private def registry : Recursive.Registry := {
  Closure := fun function scope => function = wrapper ∧ scope = child
  source := by rintro _ _ ⟨rfl, rfl⟩; rfl
  context := by rintro _ _ ⟨rfl, rfl⟩; rfl
  evidence := by rintro _ _ ⟨rfl, rfl⟩; rfl }
private def failure : Recursive.Failure := .stage child (id 2) (.argumentStage 0 (id 1) .runtime)

private theorem targetValue (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 0) (.value (.closure (callable true))) heap := by
  apply Recursive.Expression.atomicValue (node := targetNode)
  · exact ⟨by simp [child, source], rfl⟩
  · exact .lambda _ _ _
  · rfl
  · exact .lambda rfl (.nil heap)

private theorem ordinaryValue (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 4) (.value (.closure (callable false))) heap := by
  apply Recursive.Expression.atomicValue (node := ordinaryNode)
  · exact ⟨by simp [child, source], rfl⟩
  · exact .lambda _ _ _
  · rfl
  · exact .lambda rfl (.nil heap)

private theorem bound (marked : Bool) : child.guards.Binds (.closure (callable marked)) ⟨[parameter marked], false⟩ := by
  apply CallableLedger.Binds.closure rfl
  constructor
  · intro impossible; cases impossible
  · intro impossible; cases impossible

private theorem ordinary : ¬ CallGuard.Effectful child.guards.stages := by
  rintro (marked | only)
  · cases marked
  · cases only

private theorem rejected : CallBoundary.GuardRejects child.guards (id 2) [id 1] (.closure (callable true))
    (.argumentStage 0 (id 1) .runtime) :=
  .contract (bound true) (.arguments ordinary (.head (.wrongStage (.inr (.inl rfl)) rfl (by decide))))

private theorem innerFault (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 2) (.fault failure) heap := by
  apply Recursive.Expression.rejected (callee := id 0) (arguments := [id 1]) (metadata := metadata 1)
  · exact ⟨innerNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact targetValue heap
  · exact rejected

/-- A failure while computing a callee retains the inner call's coordinates. -/
example (heap : Dynamic.Heap) : Recursive.Expression program registry child context [] heap (id 3) (.fault failure) heap := by
  apply Recursive.Expression.calleeFault (callee := id 2) (arguments := []) (metadata := metadata 0)
  · exact ⟨calleeNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact innerFault heap

private theorem accepted : CallBoundary.GuardAccepts child.guards (id 5) [id 2] (.closure (callable false)) := by
  apply CallBoundary.GuardAccepts.contract (bound false)
  apply CallGuard.Accepts.ordinary ordinary
  · apply CallGuard.ArgumentsAccept.cons
    · apply CallGuard.ArgumentAccepts.ordinary
      rintro (forced | marked | only)
      · cases forced
      · cases marked
      · cases only
    · exact .nil _
  · exact .ordinary rfl

/-- An accepted outer guard does not bypass a nested argument's guard. -/
example (heap : Dynamic.Heap) : Recursive.Expression program registry child context [] heap (id 5) (.fault failure) heap := by
  apply Recursive.Expression.argumentsFault (callee := id 4) (arguments := [id 2]) (metadata := metadata 1)
  · exact ⟨argumentCallNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact ordinaryValue heap
  · exact accepted
  · exact .headFault (innerFault heap)

/-- Even an effectful caller enters the closure's retained ordinary frame.
The inner stage fault is built here from atomic rules, not assumed as a body
execution. The independent closure-validity certificate remains explicit. -/
example (heap : Dynamic.Heap) (valid : Dynamic.ClosureFrame program wrapper) :
    Recursive.Applies program registry caller context heap (.closure wrapper) [] (.fault failure) heap := by
  apply Recursive.Applies.closure (child := child) (outcome := .fault failure)
  · exact ⟨rfl, rfl⟩
  · exact valid
  · exact .nil _
  · exact .nil heap
  · exact .nil [] heap
  · apply Recursive.Statements.returnFault (node := returnNode) (expression := id 2)
    · exact ⟨by simp [child, source], rfl⟩
    · rfl
    · exact innerFault heap
  · exact .fault

example : child.origin.localSubstitution ≠ caller.origin.localSubstitution := by decide
example : child.guards.stages.callerReturnComptime = false ∧ caller.guards.stages.callerReturnComptime = true := ⟨rfl, rfl⟩

/-- Every propagated rejection is backed by its source guard and occurrence. -/
example (heap : Dynamic.Heap) : Recursive.Generated child (id 2) (.argumentStage 0 (id 1) .runtime) :=
  (innerFault heap).stage_origin rfl

/-- Production scope construction retains the actual sidecar's return marker
and full contextual substitution, even when those are erased by Core types. -/
example (sidecar : SourceCoreStageContracts.Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (RecursiveStageRegistry.scope sidecar active function).guards.stages.callerReturnComptime =
      sidecar.caller.function.returnComptime ∧
    (RecursiveStageRegistry.scope sidecar active function).origin.localSubstitution = active := ⟨rfl, rfl⟩

end Tests.SourceRecursiveStageTrace
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveStageTupleExpressions
/-! Independent ordered source tuples preserve the actual prefix heaps and
failure origin. The native audits below exercise existing compiler packing;
they do not supply a staged child or callable-body correspondence theorem. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStageTupleExpressions
open Solcore Frontend SourceInference SourceSemantics Dynamic Staging.Recursive

section Source
variable {program : Program} {registry : Registry} {scope origin : Scope}
  {context : SourceSemantics.Context} {environment : Environment} {before middle after : Heap}
  {id a b c d call : ExpressionId} {reason : Staging.CallGuard.Fault}

theorem empty (occurrence : Occurrence scope id (.tuple [])) :
    Expression program registry scope context environment before id (.value .unit) before :=
  .tupleValue occurrence .nil .nil

theorem singleton {value : Value} (occurrence : Occurrence scope id (.tuple [a]))
    (child : Expression program registry scope context environment before a (.value value) after) :
    Expression program registry scope context environment before id (.value value) after :=
  .tupleValue occurrence (.cons child .nil) (.singleton value)

theorem triple {next : Heap} {x y z : Value}
    (occurrence : Occurrence scope id (.tuple [a, b, c]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle b (.value y) next)
    (third : Expression program registry scope context environment next c (.value z) after) :
    Expression program registry scope context environment before id (.value (.product x (.product y z))) after :=
  .tupleValue occurrence (.cons first (.cons second (.cons third .nil))) (.cons (.cons (.singleton z)))

theorem repeated_occurrences {x y : Value}
    (occurrence : Occurrence scope id (.tuple [a, a]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle a (.value y) after) :
    Expression program registry scope context environment before id (.value (.product x y)) after :=
  .tupleValue occurrence (.cons first (.cons second .nil)) (.cons (.singleton y))

theorem stage_at_head {suffix : List ExpressionId}
    (occurrence : Occurrence scope id (.tuple (a :: suffix)))
    (failed : Expression program registry scope context environment before a (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.tupleFault occurrence (Expressions.headFault (ids := suffix) failed)
  exact ⟨trace, trace.stage_origin rfl⟩

theorem stage_after_prefix {value : Value} {suffix : List ExpressionId}
    (occurrence : Occurrence scope id (.tuple (a :: b :: suffix)))
    (first : Expression program registry scope context environment before a (.value value) middle)
    (failed : Expression program registry scope context environment middle b (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.tupleFault occurrence (.tailFault first (.headFault failed))
  exact ⟨trace, trace.stage_origin rfl⟩

theorem semantic_fault {elements : List ExpressionId} {fault : SemanticFault}
    (occurrence : Occurrence scope id (.tuple elements))
    (failed : Expressions program registry scope context environment before elements (.fault (.semantic fault)) after) :
    Expression program registry scope context environment before id (.fault (.semantic fault)) after ∧
      ExpressionFaults program context scope.evidence scope.source environment before id fault after := by
  have trace := Expression.tupleFault occurrence failed
  exact ⟨trace, trace.semanticFault_plain⟩

theorem values_and_erasure {elements : List ExpressionId} {values : List Value} {packed : Value}
    (occurrence : Occurrence scope id (.tuple elements))
    (children : Expressions program registry scope context environment before elements (.values values) after)
    (pack : ValuesPack values packed) :
    Expression program registry scope context environment before id (.value packed) after ∧
      ExpressionEvaluates program context scope.evidence scope.source environment before id packed after ∧
      elements.length = values.length := by
  have trace := Expression.tupleValue occurrence children pack
  exact ⟨trace, trace.value_plain, children.length⟩

/-- The existing pair constructor remains a valid independent entry. -/
theorem old_pair {x y : Value} (occurrence : Occurrence scope id (.tuple [a, b]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle b (.value y) after) :
    Expression program registry scope context environment before id (.value (.product x y)) after :=
  .pair occurrence first second

theorem empty_sequence_cannot_fault {failure : Failure} :
    ¬ Expressions program registry scope context environment before [] (.fault failure) after := by
  intro impossible
  cases impossible

theorem nonempty_tuple_not_atomic {rest : List ExpressionId} : ¬ AtomicForm (.tuple (a :: rest)) := by
  intro impossible
  cases impossible

theorem required_parent_excluded {node : ExpressionNode} {elements : List ExpressionId}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupExpression? id = some node)
    (required : node.requirements ≠ []) : ¬ Occurrence scope id (.tuple elements) := by
  rintro ⟨other, contains, _, empty, _⟩
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact required empty

theorem coerced_parent_excluded {node : ExpressionNode} {elements : List ExpressionId}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupExpression? id = some node)
    (coerced : node.coercions ≠ []) : ¬ Occurrence scope id (.tuple elements) := by
  rintro ⟨other, contains, _, _, empty⟩
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact coerced empty
end Source

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content := String.intercalate "\n" [
  "function empty() { return (); }",
  "function one() returns (Word) { return (7); }",
  "function pair() returns ((Word, Bool)) { return (11, true); }",
  "function triple() returns ((Word, Bool, Word)) { return (13, false, 17); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((19, true, 23), 29, false); }"
]

/-- The source fixture supplies exact uncoerced tuple occurrences and full
numeric ledgers. Its native audit is about the existing packer only. -/
private def actual_occurrences : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive source tuples" content
    ["empty", "one", "pair", "triple", "nested"]
  let mut counts : List Nat := []
  let mut singletons := 0
  let mut repeated := 0
  for named in compiled.indexed.base.functions do
    let selected ← get "tuple full actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "tuple retained full specialization changed"
    let source := selected.function.typedBody
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let compilation : SourceCoreFunctions.Context := {
      plan := compiled.indexed.base.plan, owner := named.signature.key,
      globals := compiled.indexed.base.globals, administrativePrefix := 0,
      solvedRequirements := selected.function.solvedRequirements, internalReason := Core.Word.zero }
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
      .error (.unsupportedExpression ⟨⟨source.owner, 0⟩⟩ (.tuple []))
    let reasonAt := fun (_ : ExpressionId) => Core.Word.zero
    let lower := fun (input : TypedSource) budget id =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy noBody budget compilation input [] id reasonAt
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .integerLiteral literal resolution =>
          let _ ← get "tuple actual selected numeric row"
            (SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements node literal resolution)
          require (node.requirements == [resolution.requirement]) "tuple numeric child requirement changed"
        | .tuple ids =>
          require (node.requirements.isEmpty && node.coercions.isEmpty) "tuple parent is not an ordinary occurrence"
          let children ← ids.mapM (fun child => get "tuple ordered original child" (lower source 99 child))
          let actual ← get "tuple actual parent" (lower source 100 node.id)
          require (actual == SourceCoreCalls.packArguments children && children.length == ids.length)
            "tuple same ordered child vector changed"
          counts := counts ++ [ids.length]
        | .group child =>
          let childNode ← match source.lookupExpression? child with
            | some child => pure child | none => throw (IO.userError "tuple group child absent")
          for ids in [[child], [child, child, child]] do
            let retained := {source with nodes := source.nodes.map (fun item => match item with
              | .expression current => if current.id == node.id then
                  .expression {current with form := .tuple ids, type := TypeSystem.Ty.productMany (ids.map (fun _ => childNode.type)), requirements := [], coercions := []}
                else item
              | _ => item)}
            let actual ← get "retained tuple arity" (lower retained 100 node.id)
            let children ← ids.mapM (fun id => get "retained tuple ordered child" (lower retained 99 id))
            require (retained.owner == source.owner && retained.inputs == source.inputs &&
              retained.roots == source.roots) "retained tuple source fields changed"
            require (actual == SourceCoreCalls.packArguments children) "retained tuple singleton/duplicate code changed"
            if ids.length == 1 then singletons := singletons + 1 else repeated := repeated + 1
        | _ => pure ()
      | _ => pure ()
  require (counts == [3, 3, 3, 2, 0] && singletons == 1 && repeated == 1)
    s!"source tuple occurrence inventory changed {counts}/{singletons}/{repeated}"

def run : IO Unit := do
  actual_occurrences
  SourceCoreRecursiveNamedTupleExpressions.run
  IO.println "recursive source tuples: actual empty/pair/nary/nested occurrences + complete numeric ledger; retained singleton/duplicate IR; existing native ordered fault/store/resume audit GREEN"

end Tests.SourceRecursiveStageTupleExpressions
end

section
-- leanmerge: from Solcore.Test.SourceSelectedTemplateInventory
/-! The unchanged full nested qualified program makes the actual prepared
open-call owner connection nonempty through raw public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceSelectedTemplateInventory
open Solcore Frontend SourceInference SourceSemantics TypeSystem CatalogedDirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration instantiation) => expression.requirements.contains requirement && catalog.contains instantiation.declaration
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    let mut openTemplates := 0
    let mut instances := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledCatalogedCallOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        have _owner := SourceCompiledTemplateCallOwner.template_owner compiledEq caller.property template.property
        have _inventory := SourceSelectedTemplateInventory.compile_inventory compiledEq caller.property template.property
        let openEmitter := caller.val.function.typedBody.nodes.any fun node => match node with
          | .expression expression => match expression.form with
            | .call _ _ (.declaration instantiation) =>
                expression.requirements.contains template.val &&
                  !SourcePreparedOpenCallEdges.InstantiationClosed instantiation
            | _ => false
          | _ => false
        if openEmitter then openTemplates := openTemplates + 1
        unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes template.val do
          throw (IO.userError "finalized template lost its selected cataloged emitter")
        templates := templates + 1
      for owner in (localSchemeTemplateOwners caller.val.function.typedBody).attach do
        have _outcome := SourceSelectedTemplateInventory.compile_owner_outcome compiledEq caller.property owner.property
        unless (TypedTraitResolution.predicateVariables owner.val.requirement.predicate).all owner.val.binder.scheme.quantified.contains do
          throw (IO.userError "actual template predicate escapes its same complete lexical owner")
      match SourceSpecializationWorklist.localLambdaInstances caller.val.function.typedBody with
      | .error error => throw (IO.userError s!"actual local discovery: {reprStr error}")
      | .ok discovered => instances := instances + discovered.length
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original cataloged emitter")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected cataloged emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 && openTemplates > 0 && instances > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS selected template inventory and predicate scope: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}, open templates={openTemplates}, actual instances={instances}"

end Tests.SourceSelectedTemplateInventory
end

section
-- leanmerge: from Solcore.Test.SourceCompiledGeneralizedBarrierConnection
/-! The unchanged public-compilation fixture checks template scope in the
original checked function, including a nonempty flexible template predicate.
The proof consumer retains that exact original and its rigid specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledGeneralizedBarrierConnection
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceCompiledLocalFinalization

private theorem original_scope {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations) :
    ∃ original ∈ compiled.program.functions,
      row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original ∧
      (∀ owner, ContainsLocalSchemeTemplate original.typedBody owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified) := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  refine ⟨selected.original, selected.originalMember, selected.specialized, ?_⟩
  intro owner contains
  rw [selected.body.source] at contains
  exact SourceCompiledGeneralizedBarrierConnection.original_template_scoped accepted member selected contains

def main : IO Unit := do
  let workspace := Tests.SourceSelectedTemplateInventory.workspace
  let .ok checked := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut rows := 0
    let mut templates := 0
    let mut variables := 0
    for row in compiled.plan.specializations.attach do
      have _actualOriginal := original_scope compiledEq row.property
      let some original := compiled.program.functions.find?
          (fun function => function.declaration == row.val.function.declaration)
        | throw (IO.userError "missing original checked function")
      for owner in localSchemeTemplateOwners original.typedBody do
        let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
        unless free.all owner.binder.scheme.quantified.contains do
          throw (IO.userError "original finalized predicate escapes its complete owner")
        let some solved := original.solvedRequirements.find?
            (fun solved => solved.id == owner.requirement.templateRequirement)
          | throw (IO.userError "original finalized template has no solved row")
        unless solved.predicate == owner.requirement.predicate do
          throw (IO.userError "original finalized predicate changed in solved ledger")
        templates := templates + 1
        variables := variables + free.length
      rows := rows + 1
    unless rows == 2 && templates == 1 && variables > 0 do
      throw (IO.userError "original template scope coverage is empty or changed")
    IO.println s!"PASS original selected template scope: rows={rows}, templates={templates}, flexible variables={variables}"

end Tests.SourceCompiledGeneralizedBarrierConnection
end
