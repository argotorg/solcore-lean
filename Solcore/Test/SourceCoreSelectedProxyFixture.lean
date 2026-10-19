import Solcore.Test.SourceCoreSelectedProxySource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "proxy artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "proxy original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "proxy original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "proxy global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "proxy substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "proxy ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "proxy ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "proxy unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

def observeLiteral (source : TypedSource) (inner : TypeSystem.Ty) : IO (LiteralShape source inner) := do
  let [.statement id] := source.roots | throw (IO.userError "proxy roots")
  let some returned := source.lookupStatement? id | throw (IO.userError "proxy return lookup")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "proxy return form")
  let some node := source.lookupExpression? expression | throw (IO.userError "proxy expression lookup")
  let ⟨inputs⟩ ← observed (source.inputs = []) "proxy input count"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "proxy root identity"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "proxy return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some node.id)) "proxy child identity"
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "proxy node identity"
  let ⟨form⟩ ← observed (node.form = .proxy inner) "proxy original raw inner type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "proxy requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "proxy coercions"
  return ⟨returned, node, inputs, roots, returnedFound, returnedForm, found, form, requirements, coercions⟩

def observeEcho (source : TypedSource) (inner : TypeSystem.Ty) : IO (EchoShape source inner) := do
  let [binder] := source.inputs | throw (IO.userError "proxy echo input")
  let [.statement id] := source.roots | throw (IO.userError "proxy echo root")
  let some returned := source.lookupStatement? id | throw (IO.userError "proxy echo return")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "proxy echo child")
  let some node := source.lookupExpression? expression | throw (IO.userError "proxy echo read")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder node (.proxy inner)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "proxy echo inputs"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (.proxy inner)) "proxy echo raw input"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "proxy echo root identity"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "proxy echo return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some read.node.id)) "proxy echo child identity"
  return ⟨binder, returned, read, inputs, scheme, roots, returnedFound, returnedForm⟩

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "proxy bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedProxy
