import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.Test.SourceSemantics.CoreLowering.Mixed.Control
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHandles
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicForward
import Solcore.SourceSemantics.CoreLowering.PublicSessions

/-!
# Mixed operator tests

Mixed bodies with operators and builtin handles and values.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueProbe
/-! One unchanged original body combines a generalized identity and a returned
builtin function value. This probe observes actual acceptance and runtime;
independent Source and public correspondence use the same unchanged workspace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function builtinPair(flag: Bool) returns (Bool, function(Word) returns (integer)) {",
    "  let f = lam(value) { return value; };",
    "  return (f(flag), wordToInteger);",
    "}" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: output {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: fuel exhausted")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

def probe : IO Unit := do
  let program ← get "check mixed while" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed while" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed while cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed while" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed while" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "builtin factory" (← initial.run root.key [.bool true] runOptions)
  let .product (.bool true) (.function handle) := first.value | throw (IO.userError "builtin factory output")
  let invoked ← succeeded "returned builtin" (← first.session.invokePacked handle (.word (word 17)) runOptions)
  require (invoked.value == .integer 17) "returned builtin result"
  let second ← succeeded "factory reused" (← invoked.session.run root.key [.bool false] runOptions)
  let .product (.bool false) (.function _) := second.value | throw (IO.userError "reused factory output")
  IO.println s!"MIXED_BUILTIN_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,invoked.session.heapSize,second.session.heapSize]}"
  IO.println "MIXED_BUILTIN_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_BUILTIN_PROBE_PASS"

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
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
      | none => throw (IO.userError "mixed builtin artifact absent")
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
    | throw (IO.userError "mixed builtin original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed builtin original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed builtin global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed builtin substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed builtin ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed builtin ordinary parameters"
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
    | _ => throw (IO.userError "mixed builtin unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed builtin complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed builtin complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed builtin complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "builtinPair"
  IO.println "MIXED_BUILTIN_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.profile {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    Nonempty (CellAwareNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueSource
/-! Independent original Source identity materialization followed by a builtin
value leaf, in the original ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreMixedImperative (StatementAt)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  call : CallShape source f.binder flagRead.node.id .bool
  builtin : ExpressionNode
  builtinName : String
  builtinFound : source.lookupExpression? builtin.id = some builtin
  builtinForm : builtin.form = .reference builtinName (.builtinFunction .wordToInteger)
  builtinRequirements : builtin.requirements = []
  builtinCoercions : builtin.coercions = []
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [call.node.id,builtin.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  fFlag : f.binder.id ≠ flag.id

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "builtin original input")
  let [.expression parameterRead,.statement identityReturn,.expression lambda,.statement initialized,
       .expression flagNode,.expression callee,.expression callNode,.expression builtin,
       .expression tuple,.statement returned] := source.nodes | throw (IO.userError "builtin original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "builtin original declaration")
  let f ← identity source binder lambda parameterRead identityReturn
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let call ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool callee callNode
  let .reference builtinName (.builtinFunction .wordToInteger) := builtin.form
    | throw (IO.userError "original builtin reference")
  let ⟨builtinFound⟩ ← observed (source.lookupExpression? builtin.id = some builtin) "builtin identity"
  let ⟨builtinForm⟩ ← observed (builtin.form = .reference builtinName (.builtinFunction .wordToInteger)) "builtin form"
  let ⟨builtinRequirements⟩ ← observed (builtin.requirements = []) "builtin requirements"
  let ⟨builtinCoercions⟩ ← observed (builtin.coercions = []) "builtin coercions"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [call.node.id,builtin.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "original inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "original roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "distinct identities"
  return ⟨flag,f,flagRead,call,builtin,builtinName,builtinFound,builtinForm,builtinRequirements,builtinCoercions,
    ⟨initialized,initializedFound,initializedForm⟩,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,fFlag⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueSourceFirst
/-! Construct the original declaration, generalized call, and builtin return
before any target execution. The builtin leaf preserves the actual call heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem Shape.call_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {result : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id result) :
    ∃ type, ExpressionHasType source context shape.call.node.id type := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children => cases children with | cons first _ => exact ⟨_,first⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after ∧ HeapAppends before after := by
  obtain ⟨middle, _, _, firstTyped, tailTyped⟩ := head_tail typed
  obtain ⟨declaration, stateNext, stored, _extended⟩ := generalized_step shape.f shape.initialized state wellFormed firstTyped
  obtain ⟨next, _, _, returnedTyped, _⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨type,callTyped⟩ := shape.call_typed state.runtime.graph.nodeOccurrencesUnique tupleTyped
    have allocatedPrefix : HeapAppends before (identityHeap shape.f context environment before) :=
      identityHeap_appends shape.f context environment before
    have flagNext := (flagStored.mono allocatedPrefix).under (identityLocation source environment before) shape.fFlag
    obtain ⟨after, callTrace, append⟩ := stored.invoke stateNext wellFormed shape.call (.inr rfl)
      callTyped (read_value shape.flagRead flagNext)
    have builtinTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment) after shape.builtin.id
        (.builtin ⟨.wordToInteger⟩) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.builtinFound)
      · rw [shape.builtinForm,shape.builtinRequirements,shape.builtinCoercions]
        exact .builtinFunction rfl
      · rw [shape.builtinCoercions]; exact .nil
    have tupleTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
        (identityHeap shape.f context environment before) shape.tuple.id
        (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
      · rw [shape.tupleForm,shape.tupleRequirements,shape.tupleCoercions]
        exact .tuple rfl (.cons callTrace (.cons builtinTrace .nil)) (.cons (.singleton _))
      · rw [shape.tupleCoercions]; exact .nil
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans append⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMixedImperative (SourceState StoredValue)

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.node.id, shape.returned.node.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool)
    (heapTyped : Dynamic.HeapWellTyped selected.packet.header.function.context before) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final after, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)))
      after := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  have allocatedTyped := heapTyped.allocate (.some (.bool flag)) allocation
  have boundTyped : Dynamic.HeapWellTyped header.context (flagHeap before flag) :=
    allocatedTyped.transportClosed fields.signatures certified.runtime.closed runtime.closed
      certified.runtime.variables_closed runtime.residual_variables_open
  have state : SourceState (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      header.function.source header.context header.function.evidence
      (flagEnvironment shape.flag before) (flagHeap before flag) :=
    ⟨runtime, covers, locals, boundTyped⟩
  have stored : StoredValue shape.flag (flagEnvironment shape.flag before) (flagHeap before flag) (.bool flag) :=
    ⟨_, _, .head, allocation.reads_new, rfl, rfl⟩
  obtain ⟨next, after, body, _append⟩ := shape.body_from_source state wellFormed typed flag stored
  exact ⟨bound, next, after, selected.statements shape ▸ body⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueTyping
/-! The builtin-value regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "mixed builtin full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed builtin original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "mixed builtin original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed builtin original complete cache size")
  IO.println "MIXED_BUILTIN_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_BUILTIN_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValuePublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

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
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValuePublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

structure SourceTrace (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (before : Dynamic.Heap) (flag : Bool) where
  finalContext : SourceSemantics.Context
  after : Dynamic.Heap
  allocated : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
  trace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
    selected.packet.header.function.body finalContext
    (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  source : SourceTrace selected shape ⟨[]⟩ flag
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag initial.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  source : SourceTrace selected shape retained.state.heap flag
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag ready.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinHandleCollected
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

theorem SelectedInventory.result_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.resultType = row.original.function.inferredBodyType :=
  selected.packet.header.agreement.result.trans
    (congrArg (fun named => named.function.inferredBodyType) selected.header_original)

def builtinSelection {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {flag : Bool} {handle : SourceCorePublicValues.Handle}
    (types : type = .product .bool (.function .word .integer))
    (values : value = .product (.bool flag) (.function handle)) : Selection type value := by
  cases types
  cases values
  exact .product .skip .function

theorem builtin_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {flag : Bool} {handle : SourceCorePublicValues.Handle}
    (types : type = .product .bool (.function .word .integer))
    (values : value = .product (.bool flag) (.function handle))
    {sourceFlag : Bool} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (builtinSelection types values)
      (.product (.bool sourceFlag) (.builtin ⟨.wordToInteger⟩)) native nativeType fuel entries) :
    ∃ native nativeType remaining,
      entries = [⟨.function .word .integer,.builtin ⟨.wordToInteger⟩,handle,native,nativeType,remaining⟩] := by
  cases types
  cases values
  cases selected with
  | product left right =>
    cases left
    cases right
    exact ⟨_,_,_,rfl⟩

private theorem selected_original {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (same ▸ selection) source native type fuel entries) :
    Selected selection source native type fuel entries := by
  cases same
  exact selected

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_collected
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (_retained : first.Retained returned.session entries) (payload : Core.Value),
      Selected selection (.product (.bool firstFlag) (.builtin ⟨.wordToInteger⟩))
        payload selected.packet.header.output outputFuel entries := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.first_collected _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    let actualSelection : Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨caller,payload,entries,_native,selectedLeaves,_handles,_related,history⟩ := collect actualSelection
    exact ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world, heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩, payload, selected_original atReturned.1 selectedLeaves⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinHandlePlan
/-! The original returned builtin and current typed history supply an
independent Source call before resuming the accepted public handle request. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected shape flag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (entry : Entry) (word : Core.Word)
  (call : CellAwarePublicHandleStart.StartedCall session entry.handle (.word word) runOptions.inputValidationFuel)

structure BuiltinHandlePlan where
  member : entry ∈ entries
  entryType : entry.sourceType = .function .word .integer
  sourceEq : entry.source = .builtin ⟨.wordToInteger⟩
  start : CellAwarePublicHandleStart.Started retained.state entry call .word .integer
  ready : CellAwarePublicHandleStart.Ready retained.state entry call start (.word word)
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context
    .word (.word word) (.word word)
  trace : Dynamic.CallableApplies (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.function.context [] [] retained.state.heap
    entry.source [.word word] (.integer (Int.ofNat word.val)) retained.state.heap

/-- Genuine primitive semantics, with no native execution premise. -/
theorem builtin_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function .word .integer)
    (sourceEq : entry.source = .builtin ⟨.wordToInteger⟩) :
    Nonempty (BuiltinHandlePlan first retained entry word call) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context
      .word (.word word) (.word word) :=
    .data ⟨.word word,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word word⟩
      ⟨.word word,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word word⟩
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  exact ⟨⟨member,entryType,sourceEq,start,ready,input,sourceEq.symm ▸ .builtin (.wordToInteger word)⟩⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinHandleObserved
/-! The observed completion belongs to the builtin call planned independently
from Source. Its unchanged mixed heap and every exported handle are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {first : InitialForward selected shape flag started callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {retained : first.Retained session entries}
  {entry : Entry} {word : Core.Word}
  {call : CellAwarePublicHandleStart.StartedCall session entry.handle (.word word) runOptions.inputValidationFuel}

/-- Native determinism joins the actual completion to the independently
proved primitive call; no numerical sufficient-fuel bound is assumed. -/
theorem BuiltinHandlePlan.observed_retained
    (plan : BuiltinHandlePlan first retained entry word call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    ∃ continued : first.Retained returned.session entries,
      continued.state.heap = retained.state.heap := by
  obtain ⟨sidecar,_issued,_selected⟩ := selected.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size (.value plan.trace)
  have metadata : SourceCoreRawMetadata.Extends plan.start.encodedValues.registry
      plan.ready.receiving.result.context.registry := by
    rw [plan.ready.contextAt]
    exact .refl _
  obtain ⟨native,store,mapping,world,required,run,resultAt⟩ :=
    CellAwarePublicBuiltinHandleMeaning.source_has_sufficient_fuel
      (invocation := RecursiveStageRegistry.scope sidecar [] selected.packet.header.function)
      callableProfile _ plan.ready.history.semantic entry plan.member plan.entryType plan.sourceEq plan.input
      plan.start.started plan.start.parameterView metadata (.singleton (.word word)) measured
  obtain ⟨actual,generation,reached,_exported,atReturned,_related,history,registry,exportsReady⟩ :=
    CellAwarePublicDirectObservedOutput.after_success _ _ plan.start.started
      (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt) retained.exportsReady
      plan.start.atCheckpoint resultAt (run required (Nat.le_refl _)) resumed plan.ready.history
  exact ⟨⟨{
    artifact := retained.state.artifact, session := actual.session,
    mapping := mapping, world := world, heap := retained.state.heap, store := store, caller := reached,
    atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
    receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
    registry := registry, history := history
    },exportsReady⟩,rfl⟩

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_retained
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session []) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.first_success _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    exact ⟨⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

/-- Each actual later success keeps the previous handles and captured cells,
using the independently reconstructed Source execution at the prior heap. -/
theorem NextForward.observed_retained (next : NextForward first retained flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session entries) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control next.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) next.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller next.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      next.ready.history.physical next.ready.stable next.ready.heapTyped next.ready.argumentsTyped issued bodySelected
      next.ready.represented next.ready.history.semantic.current.2.1 rfl next.start.started next.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.after_success _ _ next.start.selected next.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry next.ready.contextAt)
        retained.exportsReady next.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        next.ready.history
    exact ⟨⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := next.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result next.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedBuiltinValue
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinHandleHistory
/-! The complete original fixture and actual returned export retain one genuine
builtin entry through both direct applications and later named calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue.HandlePublic
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure Observed where
  fixture : ProfiledFixture
  row : Row fixture.original
  shape : Shape row.original.function.typedBody
  typing : OriginalTyping fixture.original
  result : row.original.function.inferredBodyType = .product .bool (.function .word .integer)
  callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observe : IO Observed := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "builtinPair"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨result⟩ ← observed (row.original.function.inferredBodyType = .product .bool (.function .word .integer))
    "original builtin output type changed"
  let ⟨profile⟩ ← observed (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "builtin callable profile disabled"
  pure ⟨fixture,row,shape,typing,result,profile⟩

structure Context (observed : Observed) where
  selected : SelectedInventory observed.fixture observed.row
  firstStart : Started observed.fixture.original observed.row.original.key [.bool true]
  first : InitialForward selected observed.shape true firstStart observed.callableProfile

structure History {observed : Observed} (context : Context observed)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) where
  entries : List Entry
  retained : context.first.Retained session entries
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function .word .integer
  sourceEq : entry.source = .builtin ⟨.wordToInteger⟩

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {handle : SourceCorePublicValues.Handle}

theorem Context.collected (context : Context observed)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion context.firstStart.artifact}
    (resumed : context.firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (same : returned.value = .product (.bool true) (.function handle)) :
    Nonempty (History context returned.session handle) := by
  have types := context.selected.result_eq.trans observed.result
  obtain ⟨entries,retained,payload,selected⟩ := context.first.observed_collected observed.typing resumed
    (builtinSelection types same)
  obtain ⟨native,nativeType,fuel,entriesEq⟩ := builtin_selected types same selected
  subst entries
  exact ⟨⟨_,retained,⟨.function .word .integer,.builtin ⟨.wordToInteger⟩,handle,native,nativeType,fuel⟩,by simp,rfl,rfl,rfl⟩⟩

def atEntry {entry : Entry} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (same : entry.handle = handle)
    (call : CellAwarePublicHandleStart.StartedCall session handle argument fuel) :
    CellAwarePublicHandleStart.StartedCall session entry.handle argument fuel :=
  ⟨call.checkpoint,by rw [same]; exact call.accepted⟩

structure HandleStep (history : History context session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) where
  plan : BuiltinHandlePlan context.first history.retained history.entry word (atEntry history.handleEq call)

theorem History.plan_handle (history : History context session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) :
    Nonempty (HandleStep history word call) := by
  obtain ⟨plan⟩ := builtin_plan context.first history.retained history.entry word
    (atEntry history.handleEq call) history.member history.entryType history.sourceEq
  exact ⟨⟨plan⟩⟩

theorem HandleStep.retained {history : History context session handle} {word : Word}
    {call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel}
    (step : HandleStep history word call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (History context returned.session handle) := by
  obtain ⟨retained,_heapEq⟩ := step.plan.observed_retained resumed
  exact ⟨⟨history.entries,retained,history.entry,history.member,history.handleEq,history.entryType,history.sourceEq⟩⟩

structure NamedStep (history : History context session handle) (flag : Bool)
    (call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions) where
  plan : NextForward context.first history.retained flag call

theorem History.plan_named (history : History context session handle) (flag : Bool)
    (call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions) :
    Nonempty (NamedStep history flag call) := by
  obtain ⟨plan⟩ := next_from_source context.first history.retained flag observed.typing call
  exact ⟨⟨plan⟩⟩

theorem NamedStep.retained {history : History context session handle} {flag : Bool}
    {call : SelectedCompilationPublicSessionState.StartedCall session observed.row.original.key [.bool flag] runOptions}
    (step : NamedStep history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (History context returned.session handle) := by
  obtain ⟨retained⟩ := step.plan.observed_retained observed.typing resumed
  exact ⟨⟨history.entries,retained,history.entry,history.member,history.handleEq,history.entryType,history.sourceEq⟩⟩

end Tests.SourceCoreMixedBuiltinValue.HandlePublic
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinHandleRuntime
/-! Every resume follows an independent Source plan. The original exported
builtin remains usable after a later factory call in the same mixed session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue.HandleRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open HandlePublic

variable (observed : Observed) {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}

def Certified (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) : Prop :=
  ∃ context : Context observed, Nonempty (History context session handle)

def Planned (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) : Prop :=
  ∃ (context : Context observed) (history : History context session handle), Nonempty (HandleStep history word call)

theorem plan_handle (certified : Certified observed session handle) (word : Word)
    (call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) :
    Planned observed word call := by
  obtain ⟨context,⟨history⟩⟩ := certified
  exact ⟨context,history,history.plan_handle word call⟩

theorem retained {word : Word}
    {call : CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel}
    (planned : Planned observed word call)
    {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)) :
    Certified observed returned.session handle := by
  obtain ⟨context,history,⟨step⟩⟩ := planned
  exact ⟨context,step.retained resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def handleCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (handle : SourceCorePublicValues.Handle) (word : Word) :
    IO (CellAwarePublicHandleStart.StartedCall session handle (.word word) runOptions.inputValidationFuel) := do
  match accepted : session.startHandlePacked handle (.word word) runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def namedCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) :
    IO (SelectedCompilationPublicSessionState.StartedCall session key [.bool flag] runOptions) := do
  match accepted : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => return ⟨checkpoint,accepted⟩

private def resume {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact) :
    IO {returned : SourceCoreExecution.Completion artifact //
      checkpoint.ResumeAt runOptions.executionFuel runOptions.outputValidationFuel (.succeeded returned)} := do
  let result ← checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
  match same : result.val with
  | .succeeded returned => return ⟨returned,same ▸ result.property⟩
  | _ => throw (IO.userError "Source-certified builtin call did not succeed")

private structure Output {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) where
  handle : SourceCorePublicValues.Handle
  same : returned.value = .product (.bool true) (.function handle)

private def output {artifact : SourceCoreExecution.Artifact} (returned : SourceCoreExecution.Completion artifact) : IO (Output returned) := do
  match same : returned.value with
  | .product (.bool true) (.function handle) => return ⟨handle,same⟩
  | _ => throw (IO.userError "original returned builtin output changed")

/-- Complete original1/cache1/profile1, including actual builtin return,
current packed invocation, intervening named call and original handle reuse. -/
def run : IO Unit := do
  let observed ← observe
  let firstStart ← observeStarted observed.fixture.original observed.row.original.key [.bool true]
  have firstPlan : ∃ selected : SelectedInventory observed.fixture observed.row,
      Nonempty (InitialForward selected observed.shape true firstStart observed.callableProfile) := by
    obtain ⟨selected⟩ := observed.fixture.inventory observed.row observed.typing.wellFormed
    exact ⟨selected,initial_from_source selected observed.shape true observed.typing firstStart observed.callableProfile⟩
  let firstResult ← resume firstStart.call.checkpoint
  let builtin ← output firstResult.val
  have firstHistory : Certified observed firstResult.val.session builtin.handle := by
    obtain ⟨selected,⟨first⟩⟩ := firstPlan
    let context : Context observed := ⟨selected,firstStart,first⟩
    exact ⟨context,context.collected firstResult.property builtin.same⟩
  let firstWord := Word.ofNatModulo 17
  let firstCall ← handleCall firstResult.val.session builtin.handle firstWord
  have firstCallPlan := plan_handle observed firstHistory firstWord firstCall
  let applied ← resume firstCall.checkpoint
  have appliedHistory := retained observed firstCallPlan applied.property
  require (applied.val.value == .integer 17) "Source-certified builtin integer17 changed"
  let nextCall ← namedCall applied.val.session observed.row.original.key false
  have nextPlan : ∃ (context : Context observed) (history : History context applied.val.session builtin.handle),
      Nonempty (NamedStep history false nextCall) := by
    obtain ⟨context,⟨history⟩⟩ := appliedHistory
    exact ⟨context,history,history.plan_named false nextCall⟩
  let nextResult ← resume nextCall.checkpoint
  have nextHistory : Certified observed nextResult.val.session builtin.handle := by
    obtain ⟨context,history,⟨step⟩⟩ := nextPlan
    exact ⟨context,step.retained nextResult.property⟩
  let .product (.bool false) (.function _) := nextResult.val.value
    | throw (IO.userError "intervening original factory output changed")
  let secondWord := Word.ofNatModulo 23
  let reusedCall ← handleCall nextResult.val.session builtin.handle secondWord
  have reusedPlan := plan_handle observed nextHistory secondWord reusedCall
  let reused ← resume reusedCall.checkpoint
  have _finalHistory := retained observed reusedPlan reused.property
  require (reused.val.value == .integer 23) "Source-certified reused builtin integer23 changed"
  let heaps := [firstStart.session.heapSize,firstResult.val.session.heapSize,applied.val.session.heapSize,
    nextResult.val.session.heapSize,reused.val.session.heapSize]
  require (heaps == [2,17,17,32,32]) "Source-certified builtin retained heaps changed"
  IO.println "MIXED_BUILTIN_HANDLE_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; factory/Word17/factory/Word23; proof before every resume"
  IO.println s!"MIXED_BUILTIN_HANDLE_SOURCE_HEAPS: {heaps}"
  IO.println "MIXED_BUILTIN_HANDLE_SOURCE_PUBLIC_PASS"

end Tests.SourceCoreMixedBuiltinValue.HandleRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedBuiltinValueRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "builtinPair"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      let .product (.bool true) (.function _) := firstReturned.value
        | throw (IO.userError "builtin returned value shape")
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        let .product (.bool false) (.function _) := secondReturned.value
          | throw (IO.userError "builtin returned value shape")
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          let .product (.bool true) (.function _) := thirdReturned.value
            | throw (IO.userError "builtin returned value shape")
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,17,32,47]) "mixed builtin Source-certified repeated native heaps changed"
          IO.println "MIXED_BUILTIN_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_BUILTIN_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_BUILTIN_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed builtin certified call did not succeed")
      | _ => throw (IO.userError "second mixed builtin certified call did not succeed")
    | _ => throw (IO.userError "first mixed builtin certified call did not succeed")
  else throw (IO.userError "mixed builtin callable catalog disabled")

end Tests.SourceCoreMixedBuiltinValue.ObservedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsProbe
/-! One unchanged original body combines short-circuit operators, a generalized identity,
and a returned builtin function value. This probe observes acceptance and runtime;
independent Source and public correspondence use the same unchanged workspace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function operatorPair(flag: Bool) returns (Bool, function(Word) returns (integer)) {",
    "  let f = lam(value) { return value; };",
    "  return (f(flag) && !f(false), wordToInteger);",
    "}" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: output {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: fuel exhausted")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

def probe : IO Unit := do
  let program ← get "check mixed operators" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed operators" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed operators cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed operators" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed operators" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "builtin factory" (← initial.run root.key [.bool true] runOptions)
  let .product (.bool true) (.function handle) := first.value | throw (IO.userError "builtin factory output")
  let invoked ← succeeded "returned builtin" (← first.session.invokePacked handle (.word (word 17)) runOptions)
  require (invoked.value == .integer 17) "returned builtin result"
  let second ← succeeded "factory reused" (← invoked.session.run root.key [.bool false] runOptions)
  let .product (.bool false) (.function _) := second.value | throw (IO.userError "reused factory output")
  IO.println s!"MIXED_OPERATORS_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,invoked.session.heapSize,second.session.heapSize]}"
  IO.println "MIXED_OPERATORS_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_OPERATORS_PROBE_PASS"

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
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
      | none => throw (IO.userError "mixed operators artifact absent")
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
    | throw (IO.userError "mixed operators original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed operators original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed operators global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed operators substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed operators ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed operators ordinary parameters"
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
    | _ => throw (IO.userError "mixed operators unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed operators complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed operators complete compiler cache"
  let some profiles := CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed operators complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "operatorPair"
  IO.println "MIXED_OPERATORS_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.profile {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    Nonempty (CellAwareNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsSource
/-! Exact original operator occurrences retain both ordered identity calls and
the following builtin value leaf in the original ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)

structure Shape (source : TypedSource) where
  flag : TypedBinder
  f : IdentityShape source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  falseNode : BooleanAt source false
  firstCall : CallShape source f.binder flagRead.node.id .bool
  secondCall : CallShape source f.binder falseNode.node.id .bool
  negated : ExpressionNode
  negatedFound : source.lookupExpression? negated.id = some negated
  negatedForm : negated.form = .unary .logicalNot secondCall.node.id
  negatedRequirements : negated.requirements = []
  negatedCoercions : negated.coercions = []
  binary : ExpressionNode
  binaryFound : source.lookupExpression? binary.id = some binary
  binaryForm : binary.form = .binary firstCall.node.id .logicalAnd negated.id
  binaryRequirements : binary.requirements = []
  binaryCoercions : binary.coercions = []
  builtin : ExpressionNode
  builtinName : String
  builtinFound : source.lookupExpression? builtin.id = some builtin
  builtinForm : builtin.form = .reference builtinName (.builtinFunction .wordToInteger)
  builtinRequirements : builtin.requirements = []
  builtinCoercions : builtin.coercions = []
  initialized : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [binary.id,builtin.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement initialized.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  fFlag : f.binder.id ≠ flag.id

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def boolean (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name (.builtinBoolean _) := node.form | throw (IO.userError "binary original Boolean")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "binary Boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "binary Boolean value"
  let ⟨requirements⟩ ← observed (node.requirements = []) "binary Boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "binary Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "builtin original input")
  let [.expression parameterRead,.statement identityReturn,.expression lambda,.statement initialized,
       .expression flagNode,.expression firstCallee,.expression firstExpr,
       .expression falseExpr,.expression secondCallee,.expression secondExpr,.expression negated,.expression binary,
       .expression builtin,.expression tuple,.statement returned] := source.nodes | throw (IO.userError "operator original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "builtin original declaration")
  let f ← identity source binder lambda parameterRead identityReturn
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let falseNode ← boolean source falseExpr false
  let firstCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool firstCallee firstExpr
  let secondCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder falseNode.node.id .bool secondCallee secondExpr
  let ⟨negatedFound⟩ ← observed (source.lookupExpression? negated.id = some negated) "negated identity"
  let ⟨negatedForm⟩ ← observed (negated.form = .unary .logicalNot secondCall.node.id) "negated operand"
  let ⟨negatedRequirements⟩ ← observed (negated.requirements = []) "negated requirements"
  let ⟨negatedCoercions⟩ ← observed (negated.coercions = []) "negated coercions"
  let ⟨binaryFound⟩ ← observed (source.lookupExpression? binary.id = some binary) "binary identity"
  let ⟨binaryForm⟩ ← observed (binary.form = .binary firstCall.node.id .logicalAnd negated.id) "binary ordered branches"
  let ⟨binaryRequirements⟩ ← observed (binary.requirements = []) "binary requirements"
  let ⟨binaryCoercions⟩ ← observed (binary.coercions = []) "binary coercions"
  let .reference builtinName (.builtinFunction .wordToInteger) := builtin.form
    | throw (IO.userError "original builtin reference")
  let ⟨builtinFound⟩ ← observed (source.lookupExpression? builtin.id = some builtin) "builtin identity"
  let ⟨builtinForm⟩ ← observed (builtin.form = .reference builtinName (.builtinFunction .wordToInteger)) "builtin form"
  let ⟨builtinRequirements⟩ ← observed (builtin.requirements = []) "builtin requirements"
  let ⟨builtinCoercions⟩ ← observed (builtin.coercions = []) "builtin coercions"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "declaration identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl f.binder (some f.lambda.id)) "declaration form"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "tuple identity"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [binary.id,builtin.id]) "tuple order"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "return form"
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "original inputs"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "original roots"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flag scheme"
  let ⟨fFlag⟩ ← observed (f.binder.id ≠ flag.id) "distinct identities"
  return ⟨flag,f,flagRead,falseNode,firstCall,secondCall,negated,negatedFound,negatedForm,negatedRequirements,negatedCoercions,binary,binaryFound,binaryForm,
    binaryRequirements,binaryCoercions,builtin,builtinName,builtinFound,builtinForm,builtinRequirements,builtinCoercions,
    ⟨initialized,initializedFound,initializedForm⟩,tuple,tupleFound,tupleForm,tupleRequirements,tupleCoercions,
    ⟨returned,returnedFound,returnedForm⟩,inputs,roots,flagScheme,fFlag⟩

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsSourceFirst
/-! Construct the original declaration and operators before target execution.
The first identity call always runs; the second runs only after true. The
following builtin leaf retains the exact heap reached by those calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem Shape.calls_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {result : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id result) :
    ∃ leftType rightType, ExpressionHasType source context shape.firstCall.node.id leftType ∧
      ExpressionHasType source context shape.secondCall.node.id rightType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children =>
      cases children with
      | cons first _ =>
        cases first with
        | intro binaryContains binaryRaw _ _ _ _ =>
          cases Option.some.inj ((lookupExpression?_complete unique binaryContains).symm.trans shape.binaryFound)
          rw [shape.binaryForm] at binaryRaw
          cases binaryRaw with
          | binary left right _ =>
            cases right with
            | intro negatedContains negatedRaw _ _ _ _ =>
              cases Option.some.inj ((lookupExpression?_complete unique negatedContains).symm.trans shape.negatedFound)
              rw [shape.negatedForm] at negatedRaw
              cases negatedRaw with
              | unary operand _ => exact ⟨_,_,left,operand⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after ∧ HeapAppends before after := by
  obtain ⟨middle, _, _, firstTyped, tailTyped⟩ := head_tail typed
  obtain ⟨declaration, stateNext, stored, _extended⟩ := generalized_step shape.f shape.initialized state wellFormed firstTyped
  obtain ⟨next, _, _, returnedTyped, _⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨leftType,rightType,leftTyped,rightTyped⟩ := shape.calls_typed state.runtime.graph.nodeOccurrencesUnique tupleTyped
    have allocatedPrefix : HeapAppends before (identityHeap shape.f context environment before) :=
      identityHeap_appends shape.f context environment before
    have flagNext := (flagStored.mono allocatedPrefix).under (identityLocation source environment before) shape.fFlag
    obtain ⟨leftHeap,leftTrace,leftAppend⟩ := stored.invoke stateNext wellFormed shape.firstCall (.inr rfl)
      leftTyped (read_value shape.flagRead flagNext)
    have leftState := stateNext.after_expression wellFormed leftTyped leftTrace
    have chosen : ∃ after, Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
        (identityHeap shape.f context environment before) shape.binary.id (.bool flag) after ∧
        HeapAppends (identityHeap shape.f context environment before) after := by
      cases flag with
      | false =>
        refine ⟨leftHeap,?_,leftAppend⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.binaryFound)
        · rw [shape.binaryForm,shape.binaryRequirements,shape.binaryCoercions]
          exact .binaryShortCircuit (owned := []) rfl leftTrace .andFalse rfl
        · rw [shape.binaryCoercions]; exact .nil
      | true =>
        obtain ⟨after,rightTrace,rightAppend⟩ := (stored.mono leftAppend).invoke leftState wellFormed
          shape.secondCall (.inr rfl) rightTyped (boolean_value shape.falseNode)
        have negatedTrace : Dynamic.ExpressionEvaluates program middle evidence source
            ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
            leftHeap shape.negated.id (.bool true) after := by
          apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.negatedFound)
          · rw [shape.negatedForm,shape.negatedRequirements,shape.negatedCoercions]
            exact .unary (owned := []) rfl rightTrace (.primitive (.logicalNot false))
          · rw [shape.negatedCoercions]; exact .nil
        refine ⟨after,?_,leftAppend.trans rightAppend⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.binaryFound)
        · rw [shape.binaryForm,shape.binaryRequirements,shape.binaryCoercions]
          exact .binaryEvaluateRight (owned := []) rfl leftTrace .andTrue negatedTrace (.primitive (.logicalAnd true true))
        · rw [shape.binaryCoercions]; exact .nil
    obtain ⟨after, binaryTrace, append⟩ := chosen
    have builtinTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment) after shape.builtin.id
        (.builtin ⟨.wordToInteger⟩) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.builtinFound)
      · rw [shape.builtinForm,shape.builtinRequirements,shape.builtinCoercions]
        exact .builtinFunction rfl
      · rw [shape.builtinCoercions]; exact .nil
    have tupleTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,(identityLocation source environment before)) :: environment)
        (identityHeap shape.f context environment before) shape.tuple.id
        (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
      · rw [shape.tupleForm,shape.tupleRequirements,shape.tupleCoercions]
        exact .tuple rfl (.cons binaryTrace (.cons builtinTrace .nil)) (.cons (.singleton _))
      · rw [shape.tupleCoercions]; exact .nil
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans append⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMixedImperative (SourceState StoredValue)

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.node.id, shape.returned.node.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool)
    (heapTyped : Dynamic.HeapWellTyped selected.packet.header.function.context before) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final after, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)))
      after := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  have allocatedTyped := heapTyped.allocate (.some (.bool flag)) allocation
  have boundTyped : Dynamic.HeapWellTyped header.context (flagHeap before flag) :=
    allocatedTyped.transportClosed fields.signatures certified.runtime.closed runtime.closed
      certified.runtime.variables_closed runtime.residual_variables_open
  have state : SourceState (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      header.function.source header.context header.function.evidence
      (flagEnvironment shape.flag before) (flagHeap before flag) :=
    ⟨runtime, covers, locals, boundTyped⟩
  have stored : StoredValue shape.flag (flagEnvironment shape.flag before) (flagHeap before flag) (.bool flag) :=
    ⟨_, _, .head, allocation.reads_new, rfl, rfl⟩
  obtain ⟨next, after, body, _append⟩ := shape.body_from_source state wellFormed typed flag stored
  exact ⟨bound, next, after, selected.statements shape ▸ body⟩

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsTyping
/-! The builtin-value regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "mixed operators full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed operators original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "mixed operators original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed operators original complete cache size")
  IO.println "MIXED_OPERATORS_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_OPERATORS_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

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
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

structure SourceTrace (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (before : Dynamic.Heap) (flag : Bool) where
  finalContext : SourceSemantics.Context
  after : Dynamic.Heap
  allocated : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
  trace : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
    (flagEnvironment (selected.shape shape).flag before) (flagHeap before flag)
    selected.packet.header.function.body finalContext
    (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  source : SourceTrace selected shape ⟨[]⟩ flag
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag initial.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  source : SourceTrace selected shape retained.state.heap flag
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))
    source.after

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, after, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag ready.heapTyped
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_retained
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session []) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.first_success _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    exact ⟨⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

/-- Each actual later success keeps the previous handles and captured cells,
using the independently reconstructed Source execution at the prior heap. -/
theorem NextForward.observed_retained (next : NextForward first retained flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session entries) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control next.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) next.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller next.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      next.ready.history.physical next.ready.stable next.ready.heapTyped next.ready.argumentsTyped issued bodySelected
      next.ready.represented next.ready.history.semantic.current.2.1 rfl next.start.started next.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.after_success _ _ next.start.selected next.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry next.ready.contextAt)
        retained.exportsReady next.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        next.ready.history
    exact ⟨⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := next.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result next.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedOperators
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedOperatorsRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "operatorPair"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      let .product (.bool true) (.function _) := firstReturned.value
        | throw (IO.userError "builtin returned value shape")
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        let .product (.bool false) (.function _) := secondReturned.value
          | throw (IO.userError "builtin returned value shape")
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          let .product (.bool true) (.function _) := thirdReturned.value
            | throw (IO.userError "builtin returned value shape")
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,23,38,59]) s!"mixed operators Source-certified repeated native heaps changed: {heaps}"
          IO.println "MIXED_OPERATORS_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_OPERATORS_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_OPERATORS_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed operators certified call did not succeed")
      | _ => throw (IO.userError "second mixed operators certified call did not succeed")
    | _ => throw (IO.userError "first mixed operators certified call did not succeed")
  else throw (IO.userError "mixed operators callable catalog disabled")

end Tests.SourceCoreMixedOperators.ObservedRuntime
end
