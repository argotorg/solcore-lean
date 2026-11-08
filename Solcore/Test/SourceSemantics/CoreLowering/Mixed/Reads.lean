import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ImperativeBodies
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
# Mixed read tests

Mixed bodies with index reads and projected places.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadProbe
/-! One original combines a retained generalized identity, a virtual mapping
root, a projected assignment and actual for initializer/post writes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixedIndexRead(flag: Bool) returns (Word, Bool) {",
    "  let f = lam(value) { return value; };",
    "  let table: mapping(Word => Word);",
    "  let active = flag;",
    "  table[3] = f(10);",
    "  for (table[3] += 1; active; table[3] += 2) {",
    "    active = false;",
    "    continue;",
    "  }",
    "  return (table[f(3)], f(flag));",
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
  let program ← get "check mixed index read" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed index read" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed index read cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed index read" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed index read" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "one post" (← initial.run root.key [.bool true] runOptions)
  require (first.value == .product (.word (word 13)) (.bool true)) "mixed true result"
  let second ← succeeded "zero post" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == .product (.word (word 11)) (.bool false)) "mixed false result"
  let repeated ← succeeded "one post reused" (← second.session.run root.key [.bool true] runOptions)
  require (repeated.value == .product (.word (word 13)) (.bool true)) "mixed reused result"
  IO.println s!"MIXED_INDEX_READ_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,repeated.session.heapSize]}"
  IO.println "MIXED_INDEX_READ_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_INDEX_READ_PROBE_PASS"

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
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
      | none => throw (IO.userError "mixed index read artifact absent")
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
    | throw (IO.userError "mixed index read original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed index read original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed index read global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed index read substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed index read ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed index read ordinary parameters"
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
    | _ => throw (IO.userError "mixed index read unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareImperativeNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed index read complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed index read complete compiler cache"
  let some profiles := CellAwareImperativeNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed index read complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "mixedIndexRead"
  IO.println "MIXED_INDEX_READ_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
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
    Nonempty (CellAwareImperativeNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadSource
/-! The complete original mapping transaction and for header occurrences. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)

def mappingType : TypeSystem.Ty := .mapping .word .word
structure Shape (source : TypedSource) where
  flag : TypedBinder
  table : TypedBinder
  active : TypedBinder
  f : IdentityShape source
  key : WordNode source
  initialKey : WordNode source
  postKey : WordNode source
  readKey : WordNode source
  ten : WordNode source
  one : WordNode source
  two : WordNode source
  falseNode : BooleanAt source false
  inputRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  guardRead : Tests.SourceCoreNamedBranch.Read source active .bool
  tableRead : Tests.SourceCoreNamedBranch.Read source table mappingType
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source f.binder ten.node.id .word
  keyCall : CallShape source f.binder readKey.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tableLet : StatementAt source (.letDecl table none)
  activeLet : StatementAt source (.letDecl active (some inputRead.node.id))
  tableWrite : StatementAt source (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  activeWrite : StatementAt source (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  continuing : StatementAt source .continueStmt
  loop : StatementAt source (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  lookup : ExpressionNode
  lookupFound : source.lookupExpression? lookup.id = some lookup
  lookupForm : lookup.form = .index tableRead.node.id keyCall.node.id
  lookupRequirements : lookup.requirements = []
  lookupCoercions : lookup.coercions = []
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [lookup.id,boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,.statement tableLet.node.id,
    .statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  tableScheme : table.scheme = .mono mappingType
  activeScheme : active.scheme = .mono .bool
  keyValue : key.resolution.rawValue = 3
  initialKeyValue : initialKey.resolution.rawValue = 3
  postKeyValue : postKey.resolution.rawValue = 3
  readKeyValue : readKey.resolution.rawValue = 3
  tenValue : ten.resolution.rawValue = 10
  oneValue : one.resolution.rawValue = 1
  twoValue : two.resolution.rawValue = 2
  fFlag : f.binder.id ≠ flag.id
  tableFlag : table.id ≠ flag.id
  tableF : table.id ≠ f.binder.id
  activeFlag : active.id ≠ flag.id
  activeF : active.id ≠ f.binder.id
  activeTable : active.id ≠ table.id

private def observed_variant (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def statementAt (source : TypedSource) (node : StatementNode) (form : StatementForm) :
    IO (StatementAt source form) := do
  let ⟨found⟩ ← observed_variant (source.lookupStatement? node.id = some node) "imperative statement identity"
  let ⟨formEq⟩ ← observed_variant (node.form = form) "imperative original statement form"
  return ⟨node,found,formEq⟩

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed_variant (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed_variant (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed_variant (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed_variant (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed_variant (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed_variant (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed_variant (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed_variant (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed_variant (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed_variant (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed_variant (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed_variant (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed_variant (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed_variant (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed_variant (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed_variant (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed_variant (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

private def booleanNode (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name _ := node.form | throw (IO.userError "loop Boolean form")
  let ⟨found⟩ ← observed_variant (source.lookupExpression? node.id = some node) "loop Boolean identity"
  let ⟨form⟩ ← observed_variant (node.form = .reference name (.builtinBoolean value)) "loop Boolean value"
  let ⟨requirements⟩ ← observed_variant (node.requirements = []) "loop Boolean requirements"
  let ⟨coercions⟩ ← observed_variant (node.coercions = []) "loop Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "mapping input")
  let [.expression fRead,.statement fReturn,.expression fLambda,.statement fInit,
      .statement tableInit,.expression inputNode,.statement activeInit,
      .expression keyExpr,.expression tenExpr,.expression wordCallee,.expression wordCallNode,
      .statement tableWriteNode,.expression initialKeyExpr,.expression oneExpr,.expression guardNode,
      .expression falseExpr,.statement activeWriteNode,.statement continuingNode,
      .expression postKeyExpr,.expression twoExpr,.statement loopNode,
      .expression tableNode,.expression readKeyExpr,.expression keyCallee,.expression keyCallNode,.expression lookup,.expression flagNode,.expression boolCallee,.expression boolCallNode,
      .expression tuple,.statement returnNode] := source.nodes
    | throw (IO.userError "mapping original complete graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "mapping f declaration")
  let .letDecl table _ := tableInit.form | throw (IO.userError "mapping table declaration")
  let .letDecl active _ := activeInit.form | throw (IO.userError "mapping active declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let key ← wordNode source keyExpr
  let initialKey ← wordNode source initialKeyExpr
  let postKey ← wordNode source postKeyExpr
  let readKey ← wordNode source readKeyExpr
  let ten ← wordNode source tenExpr
  let one ← wordNode source oneExpr
  let two ← wordNode source twoExpr
  let falseNode ← booleanNode source falseExpr false
  let inputRead ← Tests.SourceCoreNamedBranch.observeRead source flag inputNode .bool
  let guardRead ← Tests.SourceCoreNamedBranch.observeRead source active guardNode .bool
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead source table tableNode mappingType
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let wordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder ten.node.id .word wordCallee wordCallNode
  let keyCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder readKey.node.id .word keyCallee keyCallNode
  let boolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool boolCallee boolCallNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let tableLet ← statementAt source tableInit (.letDecl table none)
  let activeLet ← statementAt source activeInit (.letDecl active (some inputRead.node.id))
  let tableWrite ← statementAt source tableWriteNode (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  let activeWrite ← statementAt source activeWriteNode (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  let continuing ← statementAt source continuingNode .continueStmt
  let loop ← statementAt source loopNode (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨lookupFound⟩ ← observed_variant (source.lookupExpression? lookup.id = some lookup) "mapping read identity"
  let ⟨lookupForm⟩ ← observed_variant (lookup.form = .index tableRead.node.id keyCall.node.id) "mapping read base-before-key"
  let ⟨lookupRequirements⟩ ← observed_variant (lookup.requirements = []) "mapping read requirements"
  let ⟨lookupCoercions⟩ ← observed_variant (lookup.coercions = []) "mapping read coercions"
  let ⟨tupleFound⟩ ← observed_variant (source.lookupExpression? tuple.id = some tuple) "mapping tupleFound"
  let ⟨tupleForm⟩ ← observed_variant (tuple.form = .tuple [lookup.id,boolCall.node.id]) "mapping tupleForm"
  let ⟨tupleRequirements⟩ ← observed_variant (tuple.requirements = []) "mapping tupleRequirements"
  let ⟨tupleCoercions⟩ ← observed_variant (tuple.coercions = []) "mapping tupleCoercions"
  let ⟨inputs⟩ ← observed_variant (source.inputs = [flag]) "mapping inputs"
  let ⟨roots⟩ ← observed_variant (source.roots = [.statement fLet.node.id,.statement tableLet.node.id,.statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]) "mapping roots"
  let ⟨flagScheme⟩ ← observed_variant (flag.scheme = .mono .bool) "mapping flagScheme"
  let ⟨tableScheme⟩ ← observed_variant (table.scheme = .mono mappingType) "mapping tableScheme"
  let ⟨activeScheme⟩ ← observed_variant (active.scheme = .mono .bool) "mapping activeScheme"
  let ⟨keyValue⟩ ← observed_variant (key.resolution.rawValue = 3) "mapping keyValue"
  let ⟨initialKeyValue⟩ ← observed_variant (initialKey.resolution.rawValue = 3) "mapping initialKeyValue"
  let ⟨postKeyValue⟩ ← observed_variant (postKey.resolution.rawValue = 3) "mapping postKeyValue"
  let ⟨readKeyValue⟩ ← observed_variant (readKey.resolution.rawValue = 3) "mapping read key"
  let ⟨tenValue⟩ ← observed_variant (ten.resolution.rawValue = 10) "mapping tenValue"
  let ⟨oneValue⟩ ← observed_variant (one.resolution.rawValue = 1) "mapping oneValue"
  let ⟨twoValue⟩ ← observed_variant (two.resolution.rawValue = 2) "mapping twoValue"
  let ⟨fFlag⟩ ← observed_variant (f.binder.id ≠ flag.id) "mapping fFlag"
  let ⟨tableFlag⟩ ← observed_variant (table.id ≠ flag.id) "mapping tableFlag"
  let ⟨tableF⟩ ← observed_variant (table.id ≠ f.binder.id) "mapping tableF"
  let ⟨activeFlag⟩ ← observed_variant (active.id ≠ flag.id) "mapping activeFlag"
  let ⟨activeF⟩ ← observed_variant (active.id ≠ f.binder.id) "mapping activeF"
  let ⟨activeTable⟩ ← observed_variant (active.id ≠ table.id) "mapping activeTable"
  return {
    flag := flag
    table := table
    active := active
    f := f
    key := key
    initialKey := initialKey
    postKey := postKey
    readKey := readKey
    ten := ten
    one := one
    two := two
    falseNode := falseNode
    inputRead := inputRead
    guardRead := guardRead
    tableRead := tableRead
    flagRead := flagRead
    wordCall := wordCall
    keyCall := keyCall
    boolCall := boolCall
    fLet := fLet
    tableLet := tableLet
    activeLet := activeLet
    tableWrite := tableWrite
    activeWrite := activeWrite
    continuing := continuing
    loop := loop
    lookup := lookup
    lookupFound := lookupFound
    lookupForm := lookupForm
    lookupRequirements := lookupRequirements
    lookupCoercions := lookupCoercions
    tuple := tuple
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    returned := returned
    inputs := inputs
    roots := roots
    flagScheme := flagScheme
    tableScheme := tableScheme
    activeScheme := activeScheme
    keyValue := keyValue
    initialKeyValue := initialKeyValue
    postKeyValue := postKeyValue
    readKeyValue := readKeyValue
    tenValue := tenValue
    oneValue := oneValue
    twoValue := twoValue
    fFlag := fFlag
    tableFlag := tableFlag
    tableF := tableF
    activeFlag := activeFlag
    activeF := activeF
    activeTable := activeTable
  }

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadSourceHeap
/-! The mapping root is updated in the heap reached by the right-hand call.
All earlier cells and the exact appended parameter cells remain present. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def mappingValue (value : Word) : Dynamic.Value :=
  .mapping .word .word [(.word (Word.ofNatModulo 3),.word value)]
def phaseHeap (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨mappingType,value.map mappingValue,none⟩,⟨.bool,some (.bool active),none⟩] ++ suffix⟩
def phaseEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.active.id,⟨base.cells.length+1⟩) :: (shape.table.id,⟨base.cells.length⟩) :: environment

theorem phaseHeap.prefix (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : HeapAppends base (phaseHeap base value active suffix) :=
  ⟨_,List.append_assoc _ _ _⟩

private theorem cell_append (earlier : List Dynamic.Cell) {tail : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (read : Dynamic.Heap.CellAt tail index cell) :
    Dynamic.Heap.CellAt (earlier ++ tail) (earlier.length + index) cell := by
  induction earlier with
  | nil => simpa using read
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellAt.tail ih

private theorem write_append (earlier : List Dynamic.Cell) {before after : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (write : Dynamic.Heap.CellsWrite before index cell after) :
    Dynamic.Heap.CellsWrite (earlier ++ before) (earlier.length + index) cell (earlier ++ after) := by
  induction earlier with
  | nil => simpa using write
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellsWrite.tail ih

theorem phaseHeap.table (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length⟩
      ⟨mappingType,value.map mappingValue,none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero] using
    cell_append base.cells (Dynamic.Heap.CellAt.head (cells := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.active (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length+1⟩ ⟨.bool,some (.bool active),none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    cell_append base.cells (Dynamic.Heap.CellAt.tail (cell := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellAt.head (cells := suffix)))

theorem phaseHeap.write_table (base : Dynamic.Heap) (value : Option Word) (next : Word)
    (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length⟩
      (some (mappingValue next)) (phaseHeap base (some next) active suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.table base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero,Option.map_some] using
    write_append base.cells (Dynamic.Heap.CellsWrite.head
      (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (replacement := ⟨mappingType,some (mappingValue next),none⟩)
      (rest := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.write_active (base : Dynamic.Heap) (value : Option Word)
    (active next : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length+1⟩
      (some (.bool next)) (phaseHeap base value next suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.active base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    write_append base.cells (Dynamic.Heap.CellsWrite.tail (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellsWrite.head (previous := ⟨.bool,some (.bool active),none⟩)
        (replacement := ⟨.bool,some (.bool next),none⟩) (rest := suffix)))

theorem Shape.active_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.active (phaseEnvironment shape base environment) (phaseHeap base value active suffix) (.bool active) :=
  ⟨_,_,.head,phaseHeap.active base value active suffix,rfl,rfl⟩
theorem Shape.table_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.table (phaseEnvironment shape base environment) (phaseHeap base (some value) active suffix)
      (mappingValue value) :=
  ⟨_,_,.tail shape.activeTable .head,phaseHeap.table base (some value) active suffix,rfl,rfl⟩

theorem projected_first {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) key (.word (Word.ofNatModulo 3)) (phaseHeap base none active []))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) rhs (.word right) (phaseHeap base none active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      environment (phaseHeap base none active []) ⟨root,[.index key],.word⟩ rhs (mappingValue right)
      (phaseHeap base (some right) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base none active []) (.index keyTrace .nil)
    (phaseHeap.table base none active []) (.emptyMapping .word .word) (.indexDefault .nil .word .nil))
    rightTrace (.intro (phaseHeap.table base none active suffix) rfl (.emptyMapping .word .word)
      (.indexDefault .nil .word (.leaf (.equal _ _)) (.append .nil))
      (phaseHeap.write_table base none right active suffix))

theorem projected_add {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {old right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) key (.word (Word.ofNatModulo 3)) (phaseHeap base (some old) active suffix))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) rhs (.word right) (phaseHeap base (some old) active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .add)
      environment (phaseHeap base (some old) active suffix) ⟨root,[.index key],.word⟩ rhs (mappingValue (old.add right))
      (phaseHeap base (some (old.add right)) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base (some old) active suffix) (.index keyTrace .nil)
    (phaseHeap.table base (some old) active suffix) .initialized (.indexFound (.head (.refl (.word _))) .nil))
    rightTrace (.intro (phaseHeap.table base (some old) active suffix) rfl .initialized
      (.indexFound (.head (.refl (.word _))) (.leaf (.add (.wordAdd _ _))) (.update (.head (.refl (.word _)))))
      (phaseHeap.write_table base (some old) (old.add right) active suffix))

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadSourceLoop
/-! Independent Source execution of the mapping initializer and the continue/post
path. Both writes rebuild the mapping in the exact current heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

theorem projected_key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root : Resolved.LocalId} {key : ExpressionId} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context ⟨root,[.index key],.word⟩ type) :
    ∃ keyType, ExpressionHasType source context key keyType := by
  cases typed with
  | intro _ projections _ =>
    cases projections with | index key _ => exact ⟨_,key⟩

private theorem Shape.header_add {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (active : Bool) (suffix : List Dynamic.Cell) (old : Word)
    (key right : Tests.SourceCoreSelectedInterleavedLocal.WordNode source)
    (keyValue : key.resolution.rawValue = 3)
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source context ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id) :
    Dynamic.ForItemsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix)
      [.assignValue ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id] context
      (phaseEnvironment shape base environment)
      (phaseHeap base (some (old.add (Word.ofNatModulo right.resolution.rawValue))) active suffix) := by
  cases typed with
  | wordCompound _ place rightTyped _ =>
    obtain ⟨_,keyTyped⟩ := projected_key_typed place
    have keyTrace := key.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique keyTyped
    rw [keyValue] at keyTrace
    have rightTrace := right.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique rightTyped
    exact .cons (.assignValue (projected_add (.tail shape.activeTable .head) keyTrace rightTrace)) .nil

def loopValue (flag : Bool) : Word := Word.ofNatModulo (if flag then 13 else 11)

private theorem Shape.loop_body {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (value : Word) (suffix : List Dynamic.Cell) :
    Dynamic.StatementsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some value) true suffix) [shape.activeWrite.node.id,shape.continuing.node.id]
      context (.continuing (phaseEnvironment shape base environment))
      (phaseHeap base (some value) false suffix) := by
  have assigned := Dynamic.StatementExecutes.assignValue (program := program) (context := context)
    (evidence := evidence) (environment := phaseEnvironment shape base environment)
    (lookupStatement?_sound shape.activeWrite.found) shape.activeWrite.formEq
    (Dynamic.SourcePlaceAssignment.intro
      (.intro .head (phaseHeap.active base (some value) true suffix) .nil
        (phaseHeap.active base (some value) true suffix) .initialized .nil)
      (boolean_value shape.falseNode)
      (.intro (phaseHeap.active base (some value) true suffix) rfl .initialized
        (.leaf (.equal _ _)) (phaseHeap.write_active base (some value) true false suffix)))
  exact .cons assigned (.terminal
    (.continueStmt (lookupStatement?_sound shape.continuing.found) shape.continuing.formEq) (.continuing _))

theorem Shape.loop_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.loop.node.id final facts)
    (flag : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some (Word.ofNatModulo 10)) flag suffix) shape.loop.node.id final
      (.fallthrough (phaseEnvironment shape base environment))
      (phaseHeap base (some (loopValue flag)) false suffix) := by
  have form := form_at unique shape.loop.found typed
  rw [shape.loop.formEq] at form
  cases form with
  | forLoop initial _ _ post =>
    cases initial with
    | cons initialized tail =>
      cases initialized with
      | assignValue initialTyped =>
        cases tail
        cases post with
        | cons postItem tail =>
          cases postItem with
          | assignValue postTyped =>
            have initialTrace := shape.header_add (program := program) evidence base environment flag suffix
              (Word.ofNatModulo 10) shape.initialKey shape.one shape.initialKeyValue unique initialTyped
            rw [shape.oneValue] at initialTrace
            have add1 : (Word.ofNatModulo 10).add (Word.ofNatModulo 1) = Word.ofNatModulo 11 := by decide
            rw [add1] at initialTrace
            apply Dynamic.StatementExecutes.forLoop (program := program) (evidence := evidence)
              (outcome := .fallthrough (phaseEnvironment shape base environment))
              (lookupStatement?_sound shape.loop.found) shape.loop.formEq initialTrace
            cases flag with
            | false => exact .done (read_value shape.guardRead (shape.active_stored base environment _ false suffix))
            | true =>
              have postTrace := shape.header_add (program := program) evidence base environment false suffix
                (Word.ofNatModulo 11) shape.postKey shape.two shape.postKeyValue unique postTyped
              rw [shape.twoValue] at postTrace
              have add2 : (Word.ofNatModulo 11).add (Word.ofNatModulo 2) = Word.ofNatModulo 13 := by decide
              rw [add2] at postTrace
              exact .nextContinue (read_value shape.guardRead (shape.active_stored base environment _ true suffix))
                (shape.loop_body _ evidence base environment _ suffix) postTrace
                (.done (read_value shape.guardRead (shape.active_stored base environment _ false suffix)))

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadSourceFirst
/-! Construct the original ordinary Source body independently: capture the
polymorphic identity, allocate the absent mapping, commit the right-hand call,
execute the for headers, and return the updated mapping and Bool instance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def absentHeap (before : Dynamic.Heap) (binder : TypedBinder) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨binder.scheme.body,none,none⟩]⟩

private theorem absent_step {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} (site : StatementAt source (.letDecl binder none))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((binder.id,⟨before.cells.length⟩) :: environment)) (absentHeap before binder) ∧
    SourceState program source final evidence ((binder.id,⟨before.cells.length⟩) :: environment) (absentHeap before binder) ∧
    BinderExtends source.owner context binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letUninitialized mono extended =>
    have allocation : Dynamic.Heap.Allocates before binder.scheme.body none
        ⟨before.cells.length⟩ (absentHeap before binder) := .append
    have trace := Dynamic.StatementExecutes.letUninitialized (program := program) (environment := environment)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq mono extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,extended⟩

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.lookup.id left ∧
      ExpressionHasType source context shape.boolCall.node.id right := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second _ => exact ⟨_,_,first,second⟩

private theorem lookup_key_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.lookup.id type) :
    ∃ keyType, ExpressionHasType source context shape.keyCall.node.id keyType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.lookupFound)
    rw [shape.lookupForm] at raw
    cases raw with | index _ keyTyped => exact ⟨_,keyTyped⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : BodyFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] finalContext
      (.returned (.product (.word (loopValue flag)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,tail1⟩ := head_tail typed
  obtain ⟨tableContext,_,_,tableTyped,tail2⟩ := head_tail tail1
  obtain ⟨activeContext,_,_,activeTyped,tail3⟩ := head_tail tail2
  obtain ⟨writeContext,_,_,writeTyped,tail4⟩ := head_tail tail3
  obtain ⟨loopContext,_,_,loopTyped,tail5⟩ := head_tail tail4
  obtain ⟨_,_,_,returnTyped,_⟩ := head_tail tail5
  obtain ⟨fTrace,fState,fStored,_fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let base := identityHeap shape.f context environment before
  let outer : Dynamic.Environment := (shape.f.binder.id,(identityLocation source environment before)) :: environment
  have baseAppend : HeapAppends before base := identityHeap_appends shape.f context environment before
  have flagAtF := (flagStored.mono baseAppend).under (identityLocation source environment before) shape.fFlag
  obtain ⟨tableTrace,tableState,tableExtended⟩ := absent_step shape.tableLet fState wellFormed tableTyped
  let tableHeap := absentHeap base shape.table
  have flagAtTable := (flagAtF.mono (show HeapAppends base tableHeap from ⟨_,rfl⟩)).under
    ⟨base.cells.length⟩ shape.tableFlag
  obtain ⟨activeTrace,activeState,_,activeExtended⟩ := ordinary_step shape.activeLet tableState wellFormed
    (by rw [shape.activeScheme]; rfl) activeTyped (read_value shape.inputRead flagAtTable)
  have sameHeap : valueHeap tableHeap shape.active (.bool flag) = phaseHeap base none flag [] := by
    simp only [tableHeap,absentHeap,valueHeap,phaseHeap,shape.tableScheme,shape.activeScheme,
      TypeSystem.Scheme.mono,List.append_nil,Option.map_none,List.append_assoc,List.cons_append,List.nil_append]
  have sameEnvironment :
      (shape.active.id,⟨tableHeap.cells.length⟩) :: (shape.table.id,⟨base.cells.length⟩) :: outer =
      phaseEnvironment shape base outer := by
    simp only [tableHeap,absentHeap,phaseEnvironment,List.length_append,List.length_cons,List.length_nil]
  rw [sameHeap,sameEnvironment] at activeState activeTrace
  have fAtActive : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
      (phaseHeap base none flag []) := by
    rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
    exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
      (phaseHeap.prefix base none flag []).read read,descriptor,
      (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
  have writeForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.tableWrite.found writeTyped
  rw [shape.tableWrite.formEq] at writeForm
  cases writeForm with
  | assignValue assigned =>
    cases assigned with
    | equal place wordTyped _ =>
      obtain ⟨_,keyTyped⟩ := projected_key_typed place
      obtain ⟨_,_,_,tenTyped⟩ := call_typed shape.wordCall state.runtime.graph.nodeOccurrencesUnique wordTyped
      have tenTrace := shape.ten.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique tenTyped
      rw [shape.tenValue] at tenTrace
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtActive.invoke activeState wellFormed shape.wordCall
        (.inl rfl) wordTyped tenTrace
      obtain ⟨suffix,appendEq⟩ := wordAppend
      have wordHeapEq : wordHeap = phaseHeap base none flag suffix := by
        cases wordHeap
        simp only [phaseHeap,List.append_nil] at appendEq ⊢
        exact congrArg Dynamic.Heap.mk appendEq
      rw [wordHeapEq] at wordTrace
      have keyTrace := shape.key.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique keyTyped
      rw [shape.keyValue] at keyTrace
      have writeTrace := Dynamic.StatementExecutes.assignValue (program := program) (context := activeContext)
        (evidence := evidence) (environment := phaseEnvironment shape base outer)
        (lookupStatement?_sound shape.tableWrite.found) shape.tableWrite.formEq
        (projected_first (.tail shape.activeTable .head) keyTrace wordTrace)
      have writtenState := activeState.after_statement wellFormed writeTyped writeTrace
      have loopTrace := shape.loop_trace (program := program) evidence base outer
        state.runtime.graph.nodeOccurrencesUnique loopTyped flag suffix
      have loopForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.loop.found loopTyped
      rw [shape.loop.formEq] at loopForm
      cases loopForm with
      | forLoop _ _ _ _ =>
        have afterState := writtenState.after_statement wellFormed loopTyped loopTrace
        have fAtLoop : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) := by
          rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
          exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
            (phaseHeap.prefix base (some (loopValue flag)) false suffix).read read,descriptor,
            (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
        have flagAtLoop : StoredValue shape.flag (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) (.bool flag) :=
          ((flagAtF.mono (phaseHeap.prefix base (some (loopValue flag)) false suffix)).under
            ⟨base.cells.length⟩ shape.tableFlag).under ⟨base.cells.length+1⟩ shape.activeFlag
        have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
        rw [shape.returned.formEq] at returnForm
        cases returnForm with
        | returnValue tupleTyped =>
          obtain ⟨_,_,lookupTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
          obtain ⟨_,keyCallTyped⟩ := lookup_key_typed shape state.runtime.graph.nodeOccurrencesUnique lookupTyped
          obtain ⟨_,_,_,readKeyTyped⟩ := call_typed shape.keyCall state.runtime.graph.nodeOccurrencesUnique keyCallTyped
          have readKeyTrace := shape.readKey.evaluates (program := program) evidence (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) state.runtime.graph.nodeOccurrencesUnique readKeyTyped
          rw [shape.readKeyValue] at readKeyTrace
          obtain ⟨keyHeap,keyTrace,keyAppend⟩ := fAtLoop.invoke afterState wellFormed shape.keyCall
            (.inl rfl) keyCallTyped readKeyTrace
          have lookupTrace : Dynamic.ExpressionEvaluates program activeContext evidence source
              (phaseEnvironment shape base outer) (phaseHeap base (some (loopValue flag)) false suffix)
              shape.lookup.id (.word (loopValue flag)) keyHeap := by
            apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lookupFound)
            · rw [shape.lookupForm]
              exact .indexFound (by rw [shape.lookupRequirements,shape.lookupCoercions]; rfl)
                (read_value shape.tableRead (shape.table_stored base outer (loopValue flag) false suffix))
                keyTrace (.head (.refl (.word _)))
            · rw [shape.lookupCoercions]; exact .nil
          have lookupState := afterState.after_expression wellFormed lookupTyped lookupTrace
          obtain ⟨after,boolTrace,boolAppend⟩ := (fAtLoop.mono keyAppend).invoke lookupState wellFormed shape.boolCall
            (.inr rfl) boolTyped (read_value shape.flagRead (flagAtLoop.mono keyAppend))
          have tupleTrace : Dynamic.ExpressionEvaluates program activeContext evidence source
              (phaseEnvironment shape base outer) (phaseHeap base (some (loopValue flag)) false suffix) shape.tuple.id
              (.product (.word (loopValue flag)) (.bool flag)) after := by
            apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
            · rw [shape.tupleForm]
              exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
                (.cons lookupTrace (.cons boolTrace .nil)) (.cons (.singleton _))
            · rw [shape.tupleCoercions]; exact .nil
          have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
            shape.returned.formEq tupleTrace
          refine ⟨activeContext,after,.cons fTrace (.cons tableTrace (.cons activeTrace (.cons writeTrace (.cons loopTrace ?_)))),
            baseAppend.trans ((phaseHeap.prefix base (some (loopValue flag)) false suffix).trans (keyAppend.trans boolAppend))⟩
          apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
          · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
          · exact returned
    | wordCompound impossible _ _ _ => cases impossible

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
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
    selected.packet.header.function.body = [shape.fLet.node.id, shape.tableLet.node.id, shape.activeLet.node.id, shape.tableWrite.node.id, shape.loop.node.id, shape.returned.node.id] :=
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
      (.returned (.product (.word (loopValue flag)) (.bool flag)))
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

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadTyping
/-! The loop regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
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
      "mixed index read full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed index read original signature membership")
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
  | _ => throw (IO.userError "mixed index read original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed index read original complete cache size")
  IO.println "MIXED_INDEX_READ_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_INDEX_READ_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
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


end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedIndexRead
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
    (.returned (.product (.word (loopValue flag)) (.bool flag))) after

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
    (.product (.word (loopValue flag)) (.bool flag))
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
  have forward := CellAwarePublicImperativeNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedIndexRead
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
    (.product (.word (loopValue flag)) (.bool flag))
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
  have forward := CellAwarePublicImperativeNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedIndexRead
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
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
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
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
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

end Tests.SourceCoreMixedIndexRead
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedIndexReadRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead.ObservedRuntime
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
  let row ← observeRow fixture.original "mixedIndexRead"
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
      require (firstReturned.value == .product (.word (Word.ofNatModulo 13)) (.bool true))
        "first mixed index read retained Source value changed"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool false))
          "second mixed index read retained Source value changed"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == .product (.word (Word.ofNatModulo 13)) (.bool true))
            "third mixed index read retained Source value changed"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,56,104,158]) "mixed index read Source-certified repeated native heaps changed"
          IO.println "MIXED_INDEX_READ_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_INDEX_READ_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_INDEX_READ_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed index read certified call did not succeed")
      | _ => throw (IO.userError "second mixed index read certified call did not succeed")
    | _ => throw (IO.userError "first mixed index read certified call did not succeed")
  else throw (IO.userError "mixed index read callable catalog disabled")

end Tests.SourceCoreMixedIndexRead.ObservedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedProbe
/-! One original combines a retained generalized identity, a virtual mapping
root, a projected assignment and actual for initializer/post writes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixedProjected(flag: Bool) returns (mapping(Word => Word), Bool) {",
    "  let f = lam(value) { return value; };",
    "  let table: mapping(Word => Word);",
    "  let active = flag;",
    "  table[3] = f(10);",
    "  for (table[3] += 1; active; table[3] += 2) {",
    "    active = false;",
    "    continue;",
    "  }",
    "  return (table, f(flag));",
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
  let program ← get "check mixed projected" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed projected" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed projected cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed projected" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed projected" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "one post" (← initial.run root.key [.bool true] runOptions)
  require (first.value == .product (.mapping .word .word [(.word (word 3), .word (word 13))]) (.bool true)) "mixed true result"
  let second ← succeeded "zero post" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == .product (.mapping .word .word [(.word (word 3), .word (word 11))]) (.bool false)) "mixed false result"
  let repeated ← succeeded "one post reused" (← second.session.run root.key [.bool true] runOptions)
  require (repeated.value == .product (.mapping .word .word [(.word (word 3), .word (word 13))]) (.bool true)) "mixed reused result"
  IO.println s!"MIXED_PROJECTED_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,repeated.session.heapSize]}"
  IO.println "MIXED_PROJECTED_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_PROJECTED_PROBE_PASS"

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
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
      | none => throw (IO.userError "mixed projected artifact absent")
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
    | throw (IO.userError "mixed projected original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "mixed projected original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "mixed projected global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "mixed projected substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "mixed projected ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "mixed projected ordinary parameters"
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
    | _ => throw (IO.userError "mixed projected unique physical slot")

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareImperativeNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  let ⟨originals⟩ ← observed (original.recipe.compiled.sourceProgram.functions.length = 1)
    "mixed projected complete original program"
  let ⟨cached⟩ ← observed (original.recipe.compiled.indexed.base.functions.length = 1)
    "mixed projected complete compiler cache"
  let some profiles := CellAwareImperativeNamedProgramProfiles.profile? original.recipe.compiled.indexed
    | throw (IO.userError "mixed projected complete profile rejected")
  return ⟨original, originals, cached, profiles⟩

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

def profileProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let _row ← observeRow fixture.original "mixedProjected"
  IO.println "MIXED_PROJECTED_COMPLETE_PROFILE: originals1/cache1/profile1"

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
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
    Nonempty (CellAwareImperativeNamedProgramProfiles.Entry fixture.original.recipe.compiled.indexed
      selected.packet.header.named) := by
  rw [selected.packet.aligned.named]
  exact fixture.profiles.at_slot selected.input.prepared.selected

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedSource
/-! The complete original mapping transaction and for header occurrences. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode CallShape)
open Tests.SourceCoreMixedImperative (StatementAt BooleanAt)

def mappingType : TypeSystem.Ty := .mapping .word .word
structure Shape (source : TypedSource) where
  flag : TypedBinder
  table : TypedBinder
  active : TypedBinder
  f : IdentityShape source
  key : WordNode source
  initialKey : WordNode source
  postKey : WordNode source
  ten : WordNode source
  one : WordNode source
  two : WordNode source
  falseNode : BooleanAt source false
  inputRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  guardRead : Tests.SourceCoreNamedBranch.Read source active .bool
  tableRead : Tests.SourceCoreNamedBranch.Read source table mappingType
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source f.binder ten.node.id .word
  boolCall : CallShape source f.binder flagRead.node.id .bool
  fLet : StatementAt source (.letDecl f.binder (some f.lambda.id))
  tableLet : StatementAt source (.letDecl table none)
  activeLet : StatementAt source (.letDecl active (some inputRead.node.id))
  tableWrite : StatementAt source (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  activeWrite : StatementAt source (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  continuing : StatementAt source .continueStmt
  loop : StatementAt source (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  tuple : ExpressionNode
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [tableRead.node.id,boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returned : StatementAt source (.returnStmt (some tuple.id))
  inputs : source.inputs = [flag]
  roots : source.roots = [.statement fLet.node.id,.statement tableLet.node.id,
    .statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]
  flagScheme : flag.scheme = .mono .bool
  tableScheme : table.scheme = .mono mappingType
  activeScheme : active.scheme = .mono .bool
  keyValue : key.resolution.rawValue = 3
  initialKeyValue : initialKey.resolution.rawValue = 3
  postKeyValue : postKey.resolution.rawValue = 3
  tenValue : ten.resolution.rawValue = 10
  oneValue : one.resolution.rawValue = 1
  twoValue : two.resolution.rawValue = 2
  fFlag : f.binder.id ≠ flag.id
  tableFlag : table.id ≠ flag.id
  tableF : table.id ≠ f.binder.id
  activeFlag : active.id ≠ flag.id
  activeF : active.id ≠ f.binder.id
  activeTable : active.id ≠ table.id

private def observed_variant (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def statementAt (source : TypedSource) (node : StatementNode) (form : StatementForm) :
    IO (StatementAt source form) := do
  let ⟨found⟩ ← observed_variant (source.lookupStatement? node.id = some node) "imperative statement identity"
  let ⟨formEq⟩ ← observed_variant (node.form = form) "imperative original statement form"
  return ⟨node,found,formEq⟩

private def identity (source : TypedSource) (binder : TypedBinder)
    (lambda parameterNode : ExpressionNode) (returned : StatementNode) : IO (IdentityShape source) := do
  let .lambda [parameter] (.variable typeVar) _ := lambda.form | throw (IO.userError "identity original lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVar)
  let ⟨scheme⟩ ← observed_variant (binder.scheme = ⟨[typeVar], .function (.variable typeVar) (.variable typeVar)⟩) "identity principal scheme"
  let ⟨requirements⟩ ← observed_variant (binder.schemeRequirements = []) "identity scheme requirements"
  let ⟨parameterScheme⟩ ← observed_variant (parameter.scheme = .mono (.variable typeVar)) "identity parameter"
  let ⟨parameterRequirements⟩ ← observed_variant (parameter.schemeRequirements = []) "identity parameter requirements"
  let ⟨found⟩ ← observed_variant (source.lookupExpression? lambda.id = some lambda) "identity lambda occurrence"
  let ⟨form⟩ ← observed_variant (lambda.form = .lambda [parameter] (.variable typeVar) [returned.id]) "identity body"
  let ⟨raw⟩ ← observed_variant (lambda.rawType = binder.scheme.body) "identity raw type"
  let ⟨type⟩ ← observed_variant (lambda.type = binder.scheme.body) "identity type"
  let ⟨lambdaRequirements⟩ ← observed_variant (lambda.requirements = []) "identity lambda requirements"
  let ⟨coercions⟩ ← observed_variant (lambda.coercions = []) "identity lambda coercions"
  let ⟨returnFound⟩ ← observed_variant (source.lookupStatement? returned.id = some returned) "identity return identity"
  let ⟨returnForm⟩ ← observed_variant (returned.form = .returnStmt (some parameterRead.node.id)) "identity return parameter"
  return ⟨binder,parameter,typeVar,lambda,returned,parameterRead,scheme,requirements,parameterScheme,
    parameterRequirements,found,form,raw,type,lambdaRequirements,coercions,returnFound,returnForm⟩

private def wordNode (source : TypedSource) (node : ExpressionNode) : IO (WordNode source) := do
  let .integerLiteral literal resolution := node.form | throw (IO.userError "imperative Word literal")
  let ⟨found⟩ ← observed_variant (source.lookupExpression? node.id = some node) "Word identity"
  let ⟨form⟩ ← observed_variant (node.form = .integerLiteral literal resolution) "Word form"
  let ⟨target⟩ ← observed_variant (resolution.targetType = .word) "Word target"
  let ⟨requirements⟩ ← observed_variant (node.requirements = [resolution.requirement]) "Word requirements"
  let ⟨coercions⟩ ← observed_variant (node.coercions = []) "Word coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

private def booleanNode (source : TypedSource) (node : ExpressionNode) (value : Bool) :
    IO (BooleanAt source value) := do
  let .reference name _ := node.form | throw (IO.userError "loop Boolean form")
  let ⟨found⟩ ← observed_variant (source.lookupExpression? node.id = some node) "loop Boolean identity"
  let ⟨form⟩ ← observed_variant (node.form = .reference name (.builtinBoolean value)) "loop Boolean value"
  let ⟨requirements⟩ ← observed_variant (node.requirements = []) "loop Boolean requirements"
  let ⟨coercions⟩ ← observed_variant (node.coercions = []) "loop Boolean coercions"
  return ⟨node,name,found,form,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "mapping input")
  let [.expression fRead,.statement fReturn,.expression fLambda,.statement fInit,
      .statement tableInit,.expression inputNode,.statement activeInit,
      .expression keyExpr,.expression tenExpr,.expression wordCallee,.expression wordCallNode,
      .statement tableWriteNode,.expression initialKeyExpr,.expression oneExpr,.expression guardNode,
      .expression falseExpr,.statement activeWriteNode,.statement continuingNode,
      .expression postKeyExpr,.expression twoExpr,.statement loopNode,
      .expression tableNode,.expression flagNode,.expression boolCallee,.expression boolCallNode,
      .expression tuple,.statement returnNode] := source.nodes
    | throw (IO.userError "mapping original complete graph")
  let .letDecl fBinder _ := fInit.form | throw (IO.userError "mapping f declaration")
  let .letDecl table _ := tableInit.form | throw (IO.userError "mapping table declaration")
  let .letDecl active _ := activeInit.form | throw (IO.userError "mapping active declaration")
  let f ← identity source fBinder fLambda fRead fReturn
  let key ← wordNode source keyExpr
  let initialKey ← wordNode source initialKeyExpr
  let postKey ← wordNode source postKeyExpr
  let ten ← wordNode source tenExpr
  let one ← wordNode source oneExpr
  let two ← wordNode source twoExpr
  let falseNode ← booleanNode source falseExpr false
  let inputRead ← Tests.SourceCoreNamedBranch.observeRead source flag inputNode .bool
  let guardRead ← Tests.SourceCoreNamedBranch.observeRead source active guardNode .bool
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead source table tableNode mappingType
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let wordCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder ten.node.id .word wordCallee wordCallNode
  let boolCall ← Tests.SourceCoreSelectedInterleavedLocal.observeCall source f.binder flagRead.node.id .bool boolCallee boolCallNode
  let fLet ← statementAt source fInit (.letDecl f.binder (some f.lambda.id))
  let tableLet ← statementAt source tableInit (.letDecl table none)
  let activeLet ← statementAt source activeInit (.letDecl active (some inputRead.node.id))
  let tableWrite ← statementAt source tableWriteNode (.assignValue ⟨⟨table.id,[.index key.node.id],.word⟩,[]⟩ .equal wordCall.node.id)
  let activeWrite ← statementAt source activeWriteNode (.assignValue ⟨⟨active.id,[],.bool⟩,[]⟩ .equal falseNode.node.id)
  let continuing ← statementAt source continuingNode .continueStmt
  let loop ← statementAt source loopNode (.forLoop
    [.assignValue ⟨⟨table.id,[.index initialKey.node.id],.word⟩,[]⟩ .add one.node.id]
    guardRead.node.id [.assignValue ⟨⟨table.id,[.index postKey.node.id],.word⟩,[]⟩ .add two.node.id]
    [activeWrite.node.id,continuing.node.id])
  let returned ← statementAt source returnNode (.returnStmt (some tuple.id))
  let ⟨tupleFound⟩ ← observed_variant (source.lookupExpression? tuple.id = some tuple) "mapping tupleFound"
  let ⟨tupleForm⟩ ← observed_variant (tuple.form = .tuple [tableRead.node.id,boolCall.node.id]) "mapping tupleForm"
  let ⟨tupleRequirements⟩ ← observed_variant (tuple.requirements = []) "mapping tupleRequirements"
  let ⟨tupleCoercions⟩ ← observed_variant (tuple.coercions = []) "mapping tupleCoercions"
  let ⟨inputs⟩ ← observed_variant (source.inputs = [flag]) "mapping inputs"
  let ⟨roots⟩ ← observed_variant (source.roots = [.statement fLet.node.id,.statement tableLet.node.id,.statement activeLet.node.id,.statement tableWrite.node.id,.statement loop.node.id,.statement returned.node.id]) "mapping roots"
  let ⟨flagScheme⟩ ← observed_variant (flag.scheme = .mono .bool) "mapping flagScheme"
  let ⟨tableScheme⟩ ← observed_variant (table.scheme = .mono mappingType) "mapping tableScheme"
  let ⟨activeScheme⟩ ← observed_variant (active.scheme = .mono .bool) "mapping activeScheme"
  let ⟨keyValue⟩ ← observed_variant (key.resolution.rawValue = 3) "mapping keyValue"
  let ⟨initialKeyValue⟩ ← observed_variant (initialKey.resolution.rawValue = 3) "mapping initialKeyValue"
  let ⟨postKeyValue⟩ ← observed_variant (postKey.resolution.rawValue = 3) "mapping postKeyValue"
  let ⟨tenValue⟩ ← observed_variant (ten.resolution.rawValue = 10) "mapping tenValue"
  let ⟨oneValue⟩ ← observed_variant (one.resolution.rawValue = 1) "mapping oneValue"
  let ⟨twoValue⟩ ← observed_variant (two.resolution.rawValue = 2) "mapping twoValue"
  let ⟨fFlag⟩ ← observed_variant (f.binder.id ≠ flag.id) "mapping fFlag"
  let ⟨tableFlag⟩ ← observed_variant (table.id ≠ flag.id) "mapping tableFlag"
  let ⟨tableF⟩ ← observed_variant (table.id ≠ f.binder.id) "mapping tableF"
  let ⟨activeFlag⟩ ← observed_variant (active.id ≠ flag.id) "mapping activeFlag"
  let ⟨activeF⟩ ← observed_variant (active.id ≠ f.binder.id) "mapping activeF"
  let ⟨activeTable⟩ ← observed_variant (active.id ≠ table.id) "mapping activeTable"
  return {
    flag := flag
    table := table
    active := active
    f := f
    key := key
    initialKey := initialKey
    postKey := postKey
    ten := ten
    one := one
    two := two
    falseNode := falseNode
    inputRead := inputRead
    guardRead := guardRead
    tableRead := tableRead
    flagRead := flagRead
    wordCall := wordCall
    boolCall := boolCall
    fLet := fLet
    tableLet := tableLet
    activeLet := activeLet
    tableWrite := tableWrite
    activeWrite := activeWrite
    continuing := continuing
    loop := loop
    tuple := tuple
    tupleFound := tupleFound
    tupleForm := tupleForm
    tupleRequirements := tupleRequirements
    tupleCoercions := tupleCoercions
    returned := returned
    inputs := inputs
    roots := roots
    flagScheme := flagScheme
    tableScheme := tableScheme
    activeScheme := activeScheme
    keyValue := keyValue
    initialKeyValue := initialKeyValue
    postKeyValue := postKeyValue
    tenValue := tenValue
    oneValue := oneValue
    twoValue := twoValue
    fFlag := fFlag
    tableFlag := tableFlag
    tableF := tableF
    activeFlag := activeFlag
    activeF := activeF
    activeTable := activeTable
  }

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedSourceHeap
/-! The mapping root is updated in the heap reached by the right-hand call.
All earlier cells and the exact appended parameter cells remain present. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def mappingValue (value : Word) : Dynamic.Value :=
  .mapping .word .word [(.word (Word.ofNatModulo 3),.word value)]
def phaseHeap (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨mappingType,value.map mappingValue,none⟩,⟨.bool,some (.bool active),none⟩] ++ suffix⟩
def phaseEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.active.id,⟨base.cells.length+1⟩) :: (shape.table.id,⟨base.cells.length⟩) :: environment

theorem phaseHeap.prefix (base : Dynamic.Heap) (value : Option Word) (active : Bool)
    (suffix : List Dynamic.Cell) : HeapAppends base (phaseHeap base value active suffix) :=
  ⟨_,List.append_assoc _ _ _⟩

private theorem cell_append (earlier : List Dynamic.Cell) {tail : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (read : Dynamic.Heap.CellAt tail index cell) :
    Dynamic.Heap.CellAt (earlier ++ tail) (earlier.length + index) cell := by
  induction earlier with
  | nil => simpa using read
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellAt.tail ih

private theorem write_append (earlier : List Dynamic.Cell) {before after : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (write : Dynamic.Heap.CellsWrite before index cell after) :
    Dynamic.Heap.CellsWrite (earlier ++ before) (earlier.length + index) cell (earlier ++ after) := by
  induction earlier with
  | nil => simpa using write
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellsWrite.tail ih

theorem phaseHeap.table (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length⟩
      ⟨mappingType,value.map mappingValue,none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero] using
    cell_append base.cells (Dynamic.Heap.CellAt.head (cells := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.active (base : Dynamic.Heap) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Reads (phaseHeap base value active suffix) ⟨base.cells.length+1⟩ ⟨.bool,some (.bool active),none⟩ := by
  apply Dynamic.Heap.Reads.intro
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    cell_append base.cells (Dynamic.Heap.CellAt.tail (cell := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellAt.head (cells := suffix)))

theorem phaseHeap.write_table (base : Dynamic.Heap) (value : Option Word) (next : Word)
    (active : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length⟩
      (some (mappingValue next)) (phaseHeap base (some next) active suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.table base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero,Option.map_some] using
    write_append base.cells (Dynamic.Heap.CellsWrite.head
      (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (replacement := ⟨mappingType,some (mappingValue next),none⟩)
      (rest := ⟨.bool,some (.bool active),none⟩ :: suffix))

theorem phaseHeap.write_active (base : Dynamic.Heap) (value : Option Word)
    (active next : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.Heap.Writes (phaseHeap base value active suffix) ⟨base.cells.length+1⟩
      (some (.bool next)) (phaseHeap base value next suffix) := by
  apply Dynamic.Heap.Writes.intro (phaseHeap.active base value active suffix)
  simpa only [phaseHeap,List.append_assoc,List.cons_append,List.nil_append] using
    write_append base.cells (Dynamic.Heap.CellsWrite.tail (previous := ⟨mappingType,value.map mappingValue,none⟩)
      (Dynamic.Heap.CellsWrite.head (previous := ⟨.bool,some (.bool active),none⟩)
        (replacement := ⟨.bool,some (.bool next),none⟩) (rest := suffix)))

theorem Shape.active_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Option Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.active (phaseEnvironment shape base environment) (phaseHeap base value active suffix) (.bool active) :=
  ⟨_,_,.head,phaseHeap.active base value active suffix,rfl,rfl⟩
theorem Shape.table_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (value : Word) (active : Bool) (suffix : List Dynamic.Cell) :
    StoredValue shape.table (phaseEnvironment shape base environment) (phaseHeap base (some value) active suffix)
      (mappingValue value) :=
  ⟨_,_,.tail shape.activeTable .head,phaseHeap.table base (some value) active suffix,rfl,rfl⟩

theorem projected_first {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) key (.word (Word.ofNatModulo 3)) (phaseHeap base none active []))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base none active []) rhs (.word right) (phaseHeap base none active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      environment (phaseHeap base none active []) ⟨root,[.index key],.word⟩ rhs (mappingValue right)
      (phaseHeap base (some right) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base none active []) (.index keyTrace .nil)
    (phaseHeap.table base none active []) (.emptyMapping .word .word) (.indexDefault .nil .word .nil))
    rightTrace (.intro (phaseHeap.table base none active suffix) rfl (.emptyMapping .word .word)
      (.indexDefault .nil .word (.leaf (.equal _ _)) (.append .nil))
      (phaseHeap.write_table base none right active suffix))

theorem projected_add {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {base : Dynamic.Heap} {active : Bool} {suffix : List Dynamic.Cell}
    {root : Resolved.LocalId} {key rhs : ExpressionId} {old right : Word}
    (lookup : Dynamic.Environment.LooksUp environment root ⟨base.cells.length⟩)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) key (.word (Word.ofNatModulo 3)) (phaseHeap base (some old) active suffix))
    (rightTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      (phaseHeap base (some old) active suffix) rhs (.word right) (phaseHeap base (some old) active suffix)) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .add)
      environment (phaseHeap base (some old) active suffix) ⟨root,[.index key],.word⟩ rhs (mappingValue (old.add right))
      (phaseHeap base (some (old.add right)) active suffix) := by
  exact .intro (.intro lookup (phaseHeap.table base (some old) active suffix) (.index keyTrace .nil)
    (phaseHeap.table base (some old) active suffix) .initialized (.indexFound (.head (.refl (.word _))) .nil))
    rightTrace (.intro (phaseHeap.table base (some old) active suffix) rfl .initialized
      (.indexFound (.head (.refl (.word _))) (.leaf (.add (.wordAdd _ _))) (.update (.head (.refl (.word _)))))
      (phaseHeap.write_table base (some old) (old.add right) active suffix))

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedSourceLoop
/-! Independent Source execution of the mapping initializer and the continue/post
path. Both writes rebuild the mapping in the exact current heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedProjected
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

theorem projected_key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root : Resolved.LocalId} {key : ExpressionId} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context ⟨root,[.index key],.word⟩ type) :
    ∃ keyType, ExpressionHasType source context key keyType := by
  cases typed with
  | intro _ projections _ =>
    cases projections with | index key _ => exact ⟨_,key⟩

private theorem Shape.header_add {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (active : Bool) (suffix : List Dynamic.Cell) (old : Word)
    (key right : Tests.SourceCoreSelectedInterleavedLocal.WordNode source)
    (keyValue : key.resolution.rawValue = 3)
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source context ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id) :
    Dynamic.ForItemsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix)
      [.assignValue ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id] context
      (phaseEnvironment shape base environment)
      (phaseHeap base (some (old.add (Word.ofNatModulo right.resolution.rawValue))) active suffix) := by
  cases typed with
  | wordCompound _ place rightTyped _ =>
    obtain ⟨_,keyTyped⟩ := projected_key_typed place
    have keyTrace := key.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique keyTyped
    rw [keyValue] at keyTrace
    have rightTrace := right.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique rightTyped
    exact .cons (.assignValue (projected_add (.tail shape.activeTable .head) keyTrace rightTrace)) .nil

def loopValue (flag : Bool) : Word := Word.ofNatModulo (if flag then 13 else 11)

private theorem Shape.loop_body {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (value : Word) (suffix : List Dynamic.Cell) :
    Dynamic.StatementsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some value) true suffix) [shape.activeWrite.node.id,shape.continuing.node.id]
      context (.continuing (phaseEnvironment shape base environment))
      (phaseHeap base (some value) false suffix) := by
  have assigned := Dynamic.StatementExecutes.assignValue (program := program) (context := context)
    (evidence := evidence) (environment := phaseEnvironment shape base environment)
    (lookupStatement?_sound shape.activeWrite.found) shape.activeWrite.formEq
    (Dynamic.SourcePlaceAssignment.intro
      (.intro .head (phaseHeap.active base (some value) true suffix) .nil
        (phaseHeap.active base (some value) true suffix) .initialized .nil)
      (boolean_value shape.falseNode)
      (.intro (phaseHeap.active base (some value) true suffix) rfl .initialized
        (.leaf (.equal _ _)) (phaseHeap.write_active base (some value) true false suffix)))
  exact .cons assigned (.terminal
    (.continueStmt (lookupStatement?_sound shape.continuing.found) shape.continuing.formEq) (.continuing _))

theorem Shape.loop_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.loop.node.id final facts)
    (flag : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some (Word.ofNatModulo 10)) flag suffix) shape.loop.node.id final
      (.fallthrough (phaseEnvironment shape base environment))
      (phaseHeap base (some (loopValue flag)) false suffix) := by
  have form := form_at unique shape.loop.found typed
  rw [shape.loop.formEq] at form
  cases form with
  | forLoop initial _ _ post =>
    cases initial with
    | cons initialized tail =>
      cases initialized with
      | assignValue initialTyped =>
        cases tail
        cases post with
        | cons postItem tail =>
          cases postItem with
          | assignValue postTyped =>
            have initialTrace := shape.header_add (program := program) evidence base environment flag suffix
              (Word.ofNatModulo 10) shape.initialKey shape.one shape.initialKeyValue unique initialTyped
            rw [shape.oneValue] at initialTrace
            have add1 : (Word.ofNatModulo 10).add (Word.ofNatModulo 1) = Word.ofNatModulo 11 := by decide
            rw [add1] at initialTrace
            apply Dynamic.StatementExecutes.forLoop (program := program) (evidence := evidence)
              (outcome := .fallthrough (phaseEnvironment shape base environment))
              (lookupStatement?_sound shape.loop.found) shape.loop.formEq initialTrace
            cases flag with
            | false => exact .done (read_value shape.guardRead (shape.active_stored base environment _ false suffix))
            | true =>
              have postTrace := shape.header_add (program := program) evidence base environment false suffix
                (Word.ofNatModulo 11) shape.postKey shape.two shape.postKeyValue unique postTyped
              rw [shape.twoValue] at postTrace
              have add2 : (Word.ofNatModulo 11).add (Word.ofNatModulo 2) = Word.ofNatModulo 13 := by decide
              rw [add2] at postTrace
              exact .nextContinue (read_value shape.guardRead (shape.active_stored base environment _ true suffix))
                (shape.loop_body _ evidence base environment _ suffix) postTrace
                (.done (read_value shape.guardRead (shape.active_stored base environment _ false suffix)))

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedSourceFirst
/-! Construct the original ordinary Source body independently: capture the
polymorphic identity, allocate the absent mapping, commit the right-hand call,
execute the for headers, and return the updated mapping and Bool instance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMixedProjected
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def absentHeap (before : Dynamic.Heap) (binder : TypedBinder) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨binder.scheme.body,none,none⟩]⟩

private theorem absent_step {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} (site : StatementAt source (.letDecl binder none))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((binder.id,⟨before.cells.length⟩) :: environment)) (absentHeap before binder) ∧
    SourceState program source final evidence ((binder.id,⟨before.cells.length⟩) :: environment) (absentHeap before binder) ∧
    BinderExtends source.owner context binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letUninitialized mono extended =>
    have allocation : Dynamic.Heap.Allocates before binder.scheme.body none
        ⟨before.cells.length⟩ (absentHeap before binder) := .append
    have trace := Dynamic.StatementExecutes.letUninitialized (program := program) (environment := environment)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq mono extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,extended⟩

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.tableRead.node.id left ∧
      ExpressionHasType source context shape.boolCall.node.id right := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second _ => exact ⟨_,_,first,second⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : BodyFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] finalContext
      (.returned (.product (mappingValue (loopValue flag)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,tail1⟩ := head_tail typed
  obtain ⟨tableContext,_,_,tableTyped,tail2⟩ := head_tail tail1
  obtain ⟨activeContext,_,_,activeTyped,tail3⟩ := head_tail tail2
  obtain ⟨writeContext,_,_,writeTyped,tail4⟩ := head_tail tail3
  obtain ⟨loopContext,_,_,loopTyped,tail5⟩ := head_tail tail4
  obtain ⟨_,_,_,returnTyped,_⟩ := head_tail tail5
  obtain ⟨fTrace,fState,fStored,_fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let base := identityHeap shape.f context environment before
  let outer : Dynamic.Environment := (shape.f.binder.id,(identityLocation source environment before)) :: environment
  have baseAppend : HeapAppends before base := identityHeap_appends shape.f context environment before
  have flagAtF := (flagStored.mono baseAppend).under (identityLocation source environment before) shape.fFlag
  obtain ⟨tableTrace,tableState,tableExtended⟩ := absent_step shape.tableLet fState wellFormed tableTyped
  let tableHeap := absentHeap base shape.table
  have flagAtTable := (flagAtF.mono (show HeapAppends base tableHeap from ⟨_,rfl⟩)).under
    ⟨base.cells.length⟩ shape.tableFlag
  obtain ⟨activeTrace,activeState,_,activeExtended⟩ := ordinary_step shape.activeLet tableState wellFormed
    (by rw [shape.activeScheme]; rfl) activeTyped (read_value shape.inputRead flagAtTable)
  have sameHeap : valueHeap tableHeap shape.active (.bool flag) = phaseHeap base none flag [] := by
    simp only [tableHeap,absentHeap,valueHeap,phaseHeap,shape.tableScheme,shape.activeScheme,
      TypeSystem.Scheme.mono,List.append_nil,Option.map_none,List.append_assoc,List.cons_append,List.nil_append]
  have sameEnvironment :
      (shape.active.id,⟨tableHeap.cells.length⟩) :: (shape.table.id,⟨base.cells.length⟩) :: outer =
      phaseEnvironment shape base outer := by
    simp only [tableHeap,absentHeap,phaseEnvironment,List.length_append,List.length_cons,List.length_nil]
  rw [sameHeap,sameEnvironment] at activeState activeTrace
  have fAtActive : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
      (phaseHeap base none flag []) := by
    rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
    exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
      (phaseHeap.prefix base none flag []).read read,descriptor,
      (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
  have writeForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.tableWrite.found writeTyped
  rw [shape.tableWrite.formEq] at writeForm
  cases writeForm with
  | assignValue assigned =>
    cases assigned with
    | equal place wordTyped _ =>
      obtain ⟨_,keyTyped⟩ := projected_key_typed place
      obtain ⟨_,_,_,tenTyped⟩ := call_typed shape.wordCall state.runtime.graph.nodeOccurrencesUnique wordTyped
      have tenTrace := shape.ten.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique tenTyped
      rw [shape.tenValue] at tenTrace
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtActive.invoke activeState wellFormed shape.wordCall
        (.inl rfl) wordTyped tenTrace
      obtain ⟨suffix,appendEq⟩ := wordAppend
      have wordHeapEq : wordHeap = phaseHeap base none flag suffix := by
        cases wordHeap
        simp only [phaseHeap,List.append_nil] at appendEq ⊢
        exact congrArg Dynamic.Heap.mk appendEq
      rw [wordHeapEq] at wordTrace
      have keyTrace := shape.key.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique keyTyped
      rw [shape.keyValue] at keyTrace
      have writeTrace := Dynamic.StatementExecutes.assignValue (program := program) (context := activeContext)
        (evidence := evidence) (environment := phaseEnvironment shape base outer)
        (lookupStatement?_sound shape.tableWrite.found) shape.tableWrite.formEq
        (projected_first (.tail shape.activeTable .head) keyTrace wordTrace)
      have writtenState := activeState.after_statement wellFormed writeTyped writeTrace
      have loopTrace := shape.loop_trace (program := program) evidence base outer
        state.runtime.graph.nodeOccurrencesUnique loopTyped flag suffix
      have loopForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.loop.found loopTyped
      rw [shape.loop.formEq] at loopForm
      cases loopForm with
      | forLoop _ _ _ _ =>
        have afterState := writtenState.after_statement wellFormed loopTyped loopTrace
        have fAtLoop : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) := by
          rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
          exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
            (phaseHeap.prefix base (some (loopValue flag)) false suffix).read read,descriptor,
            (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
        have flagAtLoop : StoredValue shape.flag (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) (.bool flag) :=
          ((flagAtF.mono (phaseHeap.prefix base (some (loopValue flag)) false suffix)).under
            ⟨base.cells.length⟩ shape.tableFlag).under ⟨base.cells.length+1⟩ shape.activeFlag
        have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
        rw [shape.returned.formEq] at returnForm
        cases returnForm with
        | returnValue tupleTyped =>
          obtain ⟨_,_,_tableTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
          obtain ⟨after,boolTrace,boolAppend⟩ := fAtLoop.invoke afterState wellFormed shape.boolCall
            (.inr rfl) boolTyped (read_value shape.flagRead flagAtLoop)
          have tupleTrace : Dynamic.ExpressionEvaluates program activeContext evidence source
              (phaseEnvironment shape base outer) (phaseHeap base (some (loopValue flag)) false suffix) shape.tuple.id
              (.product (mappingValue (loopValue flag)) (.bool flag)) after := by
            apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
            · rw [shape.tupleForm]
              exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
                (.cons (read_value shape.tableRead (shape.table_stored base outer (loopValue flag) false suffix))
                  (.cons boolTrace .nil)) (.cons (.singleton _))
            · rw [shape.tupleCoercions]; exact .nil
          have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
            shape.returned.formEq tupleTrace
          refine ⟨activeContext,after,.cons fTrace (.cons tableTrace (.cons activeTrace (.cons writeTrace (.cons loopTrace ?_)))),
            baseAppend.trans ((phaseHeap.prefix base (some (loopValue flag)) false suffix).trans boolAppend)⟩
          apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
          · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
          · exact returned
    | wordCompound impossible _ _ _ => cases impossible

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
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
    selected.packet.header.function.body = [shape.fLet.node.id, shape.tableLet.node.id, shape.activeLet.node.id, shape.tableWrite.node.id, shape.loop.node.id, shape.returned.node.id] :=
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
      (.returned (.product (mappingValue (loopValue flag)) (.bool flag)))
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

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedTyping
/-! The loop regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
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
      "mixed projected full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "mixed projected original signature membership")
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
  | _ => throw (IO.userError "mixed projected original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "mixed projected original complete cache size")
  IO.println "MIXED_PROJECTED_ORIGINAL_TYPING: originals1/cache1"
  IO.println "MIXED_PROJECTED_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected
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


end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedProjected
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
    (.returned (.product (mappingValue (loopValue flag)) (.bool flag))) after

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
    (.product (mappingValue (loopValue flag)) (.bool flag))
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
  have forward := CellAwarePublicImperativeNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedProjected
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
    (.product (mappingValue (loopValue flag)) (.bool flag))
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
  have forward := CellAwarePublicImperativeNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, ⟨final,after,allocated,sourceTrace⟩, forward⟩⟩

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedProjected
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
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
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
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicImperativeSourceRoot.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
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

end Tests.SourceCoreMixedProjected
end

section
-- leanmerge: from Solcore.Test.SourceCoreMixedProjectedRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedProjected.ObservedRuntime
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
  let row ← observeRow fixture.original "mixedProjected"
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
      require (firstReturned.value == .product (.mapping .word .word [(.word (Word.ofNatModulo 3),.word (Word.ofNatModulo 13))]) (.bool true))
        "first mixed projected retained Source value changed"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == .product (.mapping .word .word [(.word (Word.ofNatModulo 3),.word (Word.ofNatModulo 11))]) (.bool false))
          "second mixed projected retained Source value changed"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == .product (.mapping .word .word [(.word (Word.ofNatModulo 3),.word (Word.ofNatModulo 13))]) (.bool true))
            "third mixed projected retained Source value changed"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,48,88,134]) "mixed projected Source-certified repeated native heaps changed"
          IO.println "MIXED_PROJECTED_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"MIXED_PROJECTED_SOURCE_HEAPS: {heaps}"
          IO.println "MIXED_PROJECTED_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third mixed projected certified call did not succeed")
      | _ => throw (IO.userError "second mixed projected certified call did not succeed")
    | _ => throw (IO.userError "first mixed projected certified call did not succeed")
  else throw (IO.userError "mixed projected callable catalog disabled")

end Tests.SourceCoreMixedProjected.ObservedRuntime
end
