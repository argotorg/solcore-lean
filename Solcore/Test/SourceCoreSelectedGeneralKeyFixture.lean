import Solcore.Test.SourceCoreSelectedGeneralKeyWriteSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
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
      | none => throw (IO.userError "general key artifact absent")
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
    | throw (IO.userError "general key original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "general key original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "general key global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "general key substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "general key ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "general key ordinary parameters"
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
    | _ => throw (IO.userError "general key unique physical slot")

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

def observeBool (source : TypedSource) (id : ExpressionId) : IO ((value : Bool) × BoolNode source value) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key boolean node")
  let .reference name (.builtinBoolean value) := node.form | throw (IO.userError "general key boolean form")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "general key boolean form identity"
  let ⟨requirements⟩ ← observed (node.requirements = []) "general key boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key boolean coercions"
  return ⟨value,node,found,name,form,requirements,coercions⟩

def observeKey (source : TypedSource) (id : ExpressionId) : IO ((key : Key) × KeyNode source key) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key node")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key identity"
  let ⟨requirements⟩ ← observed (node.requirements = []) "general key requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key coercions"
  match form : node.form with
  | .tuple [first,second] =>
    let ⟨left,leftNode⟩ ← observeBool source first
    let ⟨right,rightNode⟩ ← observeBool source second
    let ⟨actualForm⟩ ← observed (node.form = .tuple [leftNode.node.id,rightNode.node.id]) "general key tuple child order"
    let ⟨type⟩ ← observed (node.type = (.product .bool .bool)) "general key tuple raw type"
    return ⟨.pair left right,node,found,type,requirements,coercions,.pair leftNode rightNode actualForm⟩
  | .proxy inner =>
    let ⟨type⟩ ← observed (node.type = .proxy inner) "general key proxy raw type"
    return ⟨.proxy inner,node,found,type,requirements,coercions,.proxy form⟩
  | .constructor metadata [argument] =>
    let ⟨value,child⟩ ← observeBool source argument
    let ⟨actualForm⟩ ← observed (node.form = .constructor metadata [child.node.id]) "general key nominal child identity"
    let ⟨type⟩ ← observed (node.type = metadata.resultType) "general key nominal raw type"
    let ⟨substitution⟩ ← observed (metadata.parameterSubstitution = []) "general key nominal substitution"
    let ⟨payload⟩ ← observed (metadata.payloadTypes = [.bool]) "general key nominal payload"
    return ⟨.nominal metadata value,node,found,type,requirements,coercions,.nominal child actualForm substitution payload⟩
  | _ => throw (IO.userError s!"general key form changed: {reprStr node.form}")

def observeRead (source : TypedSource) : IO ((key : Key) × ReadShape source key) := do
  let [binder] := source.inputs | throw (IO.userError "general key read input")
  let [.statement id] := source.roots | throw (IO.userError "general key read root")
  let some returned := source.lookupStatement? id | throw (IO.userError "general key read return")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "general key read returned expression")
  let some index := source.lookupExpression? expression | throw (IO.userError "general key index lookup")
  let .index baseId keyId := index.form | throw (IO.userError "general key index form")
  let some baseNode := source.lookupExpression? baseId | throw (IO.userError "general key base lookup")
  let ⟨key,keyNode⟩ ← observeKey source keyId
  let base ← Tests.SourceCoreNamedBranch.observeRead source binder baseNode (mappingType key)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "general key read input identity"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (mappingType key)) "general key read raw input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "general key read root identity"
  let ⟨indexFound⟩ ← observed (source.lookupExpression? index.id = some index) "general key index identity"
  let ⟨indexForm⟩ ← observed (index.form = .index base.node.id keyNode.node.id) "general key ordered index children"
  let ⟨requirements⟩ ← observed (index.requirements = []) "general key index requirements"
  let ⟨coercions⟩ ← observed (index.coercions = []) "general key index coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "general key return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some index.id)) "general key return child"
  return ⟨key,binder,keyNode,base,index,returned,inputs,scheme,roots,indexFound,indexForm,requirements,coercions,returnedFound,returnedForm⟩

def observeWord (source : TypedSource) (id : ExpressionId) : IO (WordNode source) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key RHS lookup")
  let .integerLiteral literal resolution := node.form | throw (IO.userError "general key RHS original literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key RHS identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "general key RHS form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "general key RHS target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "general key RHS requirement identity"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key RHS coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

private def observeSimple (key : Key) : IO (PLift key.Simple) :=
  match key with
  | .pair .. | .proxy .. => pure ⟨True.intro⟩
  | .nominal .. => throw (IO.userError "general key write key form")

def observeWrite (source : TypedSource) : IO ((key : Key) × WriteShape source key) := do
  let [binder] := source.inputs | throw (IO.userError "general key write input")
  let [.statement assignId,.statement returnId] := source.roots | throw (IO.userError "general key write roots")
  let some assigned := source.lookupStatement? assignId | throw (IO.userError "general key assignment lookup")
  let .assignValue assignment .add rhsId := assigned.form | throw (IO.userError "general key actual compound assignment")
  let [.index keyId] := assignment.target.projections | throw (IO.userError "general key mapping projection")
  let ⟨key,keyNode⟩ ← observeKey source keyId
  let ⟨simple⟩ ← observeSimple key
  let right ← observeWord source rhsId
  let some returned := source.lookupStatement? returnId | throw (IO.userError "general key write return lookup")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "general key write return")
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "general key write read lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source binder resultNode (mappingType key)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "general key write input identity"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (mappingType key)) "general key write raw input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id,.statement returned.id]) "general key write ordered roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "general key assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue assignment .add right.node.id) "general key RHS order"
  let ⟨targetRoot⟩ ← observed (assignment.target.root = binder.id) "general key original root binder"
  let ⟨targetProjections⟩ ← observed (assignment.target.projections = [.index keyNode.node.id]) "general key ordered projection"
  let ⟨targetType⟩ ← observed (assignment.target.type = .word) "general key selected raw Word"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "general key write return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "general key write return child"
  return ⟨key,binder,keyNode,simple,right,result,assignment,assigned,returned,inputs,scheme,roots,
    assignedFound,assignedForm,targetRoot,targetProjections,targetType,returnedFound,returnedForm⟩

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
  | .outOfFuel _ => throw (IO.userError "general key bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedGeneralKey
