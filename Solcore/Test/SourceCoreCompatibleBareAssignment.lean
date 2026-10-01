import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Concrete typed RHS trees discharge the child interface for bare assignment
success, all source faults, and completed reflection. Runtime fixtures use the
actual common compiler in a renamed environment with captured ambient values. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleBareAssignment
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatibleBareAssignment

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}

variable {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}

theorem preserves_prefix
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  exact CompatibleBareAssignment.preserves_prefix layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped trace invalid

theorem preserves_fault
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  exact CompatibleBareAssignment.preserves_fault layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped trace next outputType invalid invalidToken

theorem reflects
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  have meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing
  exact CompatibleBareAssignment.reflects layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped invalidToken completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function initializeWord() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root = vals[false] + 2; return root; }",
    "function initializeBool() returns (Bool) { let root: Bool; root = false; return root; }",
    "function initializePair() returns ((Word, Bool)) { let root: (Word, Bool); root = (2, false); return root; }",
    "function initializeNominal() returns (Box<Word>) { let root: Box<Word>; root = .Box(2); return root; }",
    "function initializeMapping() returns (Word) { let root: mapping(Bool => Word); let donor: mapping(Bool => Word); root = donor; return root[true]; }",
    "function compoundPresent() returns (Word) { let root: Word = 10; let vals: mapping(Bool => Word); root += vals[false] + 2; return root; }",
    "function compoundAbsent() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root += vals[false] + 2; return root; }",
    "function rhsFault() returns (Word) { let root: Word; let vals: mapping(Bool => Word); let missing: Word; root += vals[false] + missing; return root; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "bare assignment fixture missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "bare assignment diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "bare assignment owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "bare assignment binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "bare assignment mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | _ => pure none
    let initial := if binder.name == "root" && name == "compoundPresent" then
        OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 10))
      else OptionalCell.allocate type
    bindings := bindings ++ [(binder, type, initial, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "bare assignment return missing")
  let next ← get "bare assignment continuation" (child 150 source scope nextId reasonAt)
  match bare : assignment.target.projections with
  | _ :: _ => throw (IO.userError "bare fixture unexpectedly projected")
  | [] =>
    match accepted : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures child 150 source scope
        (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
        reasonAt invalid invalid (fun _ => invalid) with
    | .error error => throw (IO.userError s!"bare actual compiler: {reprStr error}")
    | .ok lowered =>
      have receipt := CompatibleBareAssignment.of_lower (compilation := values) (source := source) (scope := scope)
        (expression := child) bare accepted
      let _receipt := receipt
      let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
      let frameExpr := SourceCoreCallableIndexedFrames.empty frame
      let closureType := Ty.function .unit frame.type
      let closure := Expr.lambda .unit frame.type (.var 1)
      let body := bindings.foldl (fun body (_, _, initial, _) => Expr.letE initial body)
        (.letE (.integer 91) (lowered.weakenAt 0))
      let native : Core.Program := ⟨LanguageResult.resultType next.type,
        .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
      assertTrue native.check s!"bare assignment {name} ambient checker rejected"
      let completed ← match native.runStateful 200000 with
        | .done result store => pure (result, store)
        | other => throw (IO.userError s!"bare assignment {name} incomplete: {reprStr other}")
      for fuel in [0, 5, 40, 120] do
        let result := match native.runStateful fuel with
          | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
          | other => other
        assertTrue (result == .done completed.1 completed.2) s!"bare assignment {name} resume changed result/store"
      assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
        "bare assignment changed existing captured ambient closure"
      let fault := name == "compoundAbsent" || name == "rhsFault"
      if fault then
        let token ← if name == "rhsFault" then do
          let occurrence ← match source.nodes.findSome? fun
            | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
            | _ => none with
            | some id => pure id | none => throw (IO.userError "bare RHS missing occurrence")
          pure (reasonAt occurrence)
        else pure invalid
        assertTrue (completed.1 == .inLeft next.type (.word token)) s!"bare assignment {name} fault order changed"
      else
        let expected : Option Value := match name with
          | "initializeWord" => some (.word (Word.ofNatModulo 2))
          | "initializeBool" => some (.bool false)
          | "initializePair" => some (.pair (.word (Word.ofNatModulo 2)) (.bool false))
          | "initializeMapping" => some (.word Word.zero)
          | "compoundPresent" => some (.word (Word.ofNatModulo 12))
          | _ => none
        match expected with
        | some expected => assertTrue (completed.1 == .inRight .word expected) s!"bare assignment {name} wrong result"
        | none => match completed.1 with
          | .inRight .word (.constructed tag (.pair (.word header) (.word word))) =>
            let metadata ← match source.nodes.findSome? fun
              | .expression {form := .constructor metadata _, ..} => some metadata
              | _ => none with
              | some metadata => pure metadata | none => throw (IO.userError "bare nominal source metadata absent")
            assertTrue (word == Word.ofNatModulo 2 && values.registry.id? (.constructor metadata) == some header &&
              checked.catalog.constructor? metadata == some tag) "bare nominal payload/raw header changed"
          | _ => throw (IO.userError "bare nominal result lost raw carrier")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let cell ← match completed.2[bindings.length - position]? with
          | some cell => pure cell | none => throw (IO.userError "bare assignment lost source cell")
        if binder.name == "root" then
          if fault then assertTrue (cell == .inLeft type .unit) "bare assignment wrote before fault"
          else if name == "initializeMapping" then
            let some expected := expected | throw (IO.userError "bare mapping header absent")
            assertTrue (cell == .inRight .unit expected) "bare mapping assignment changed retained metadata"
          else match completed.1 with
            | .inRight .word value => assertTrue (cell == .inRight .unit value) "bare assignment result differs from root"
            | _ => throw (IO.userError "bare successful result missing")
        else if binder.name == "missing" then
          assertTrue (cell == .inLeft type .unit) "bare RHS fault rewrote missing local"
        else
          let some expected := expected | throw (IO.userError "bare mapping effect fixture absent")
          assertTrue (cell == .inRight .unit expected) s!"bare assignment {name} lost earlier mapping effect"

-- Integer compound syntax remains rejected by source inference. This separate
-- typed IR fixture checks the already accepted compiler policy boundary.
private def integerOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"bare_integer", by decide⟩], by decide⟩⟩, 0⟩
private def integerRoot : Resolved.LocalId := ⟨integerOwner, 0⟩
private def integerRight : Resolved.LocalId := ⟨integerOwner, 1⟩
private def integerId : ExpressionId := ⟨⟨integerOwner, 0⟩⟩
private def integerSource : TypedSource := {
  owner := integerOwner
  inputs := [{id := integerRoot, name := "root", scheme := .mono .integer}, {id := integerRight, name := "rhs", scheme := .mono .integer}]
  roots := [.expression integerId]
  nodes := [.expression {
    id := integerId
    span := {source := {origin := .main, path := "bare_integer.solc"}, startByte := 0, endByte := 1}
    type := .integer
    form := .reference "rhs" (.local integerRight) }]
}

private def integerPolicy (checked : SourceCoreCompatibleCatalog.Checked) : IO Unit := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let scope : SourceCoreLocalCell.Scope := [(integerRight, .integer), (integerRoot, .integer)]
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt => do
    let (_, type) ← SourceCoreCompatibleDataExpressions.readExpression checked source id
    let expression ← SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id)
    pure ⟨type, expression⟩
  let assignment : AssignmentResolution := {target := {root := integerRoot, projections := [], type := .integer}}
  let invalid := Word.ofNatModulo 999
  let readReason := Word.ofNatModulo 777
  let next := OptionalCell.read .integer (.var 1) readReason
  for (operator, expected) in ([
      (.equal, 3), (.add, -4), (.subtract, -10), (.multiply, -21), (.divide, -3),
      (.modulo, 2), (.bitAnd, 1), (.bitOr, -5), (.bitXor, -6)] : List (Syntax.ValueAssignOp × Int)) do
    match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 100 integerSource scope
        (.occurrence integerId.occurrence) assignment operator (some integerId) .integer next
        (fun _ => readReason) invalid invalid (fun _ => invalid) with
    | .error error => throw (IO.userError s!"bare Integer actual compiler: {reprStr error}")
    | .ok code =>
      have receipt := CompatibleBareAssignment.of_lower (compilation := values) (expression := child) rfl accepted
      let _receipt := receipt
      let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
      for (old, right) in ([(some (-7), some 3), (none, some 3), (none, none)] : List (Option Int × Option Int)) do
        let allocate := fun value => match value with
          | some value => OptionalCell.allocateInitialized .integer (.integer value)
          | none => OptionalCell.allocate .integer
        let body := Expr.letE (SourceCoreCallableIndexedFrames.empty frame)
          (.letE (.newCell (.function .unit frame.type) (.lambda .unit frame.type (.var 1)))
            (.letE (allocate old) (.letE (allocate right) (.letE (.integer 91) (code.weakenAt 0)))))
        let native : Core.Program := ⟨LanguageResult.resultType .integer, body, checked.catalog.definitions ++ [frame.definition]⟩
        assertTrue native.check "bare Integer ambient checker rejected"
        let changed := if right.isNone then old else if old.isNone && operator != .equal then old else some expected
        let result := if right.isNone then .inLeft .integer (.word readReason)
          else if old.isNone && operator != .equal then .inLeft .integer (.word invalid)
          else .inRight .word (.integer expected)
        let optional := fun value => match value with
          | some value => Value.inRight .unit (.integer value)
          | none => .inLeft .integer .unit
        let expectedStore := [.closure .unit frame.type (.var 1) [.constructed frame.empty .unit], optional changed, optional right]
        let completed := native.runStateful 20000
        assertTrue (completed == .done result expectedStore) s!"bare Integer result/store/order changed: {reprStr operator}"
        for fuel in [0, 4, 25, 70] do
          let resumed := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 20000 checkpoint
            | other => other
          assertTrue (resumed == completed) "bare Integer resume changed exact store"
  let rejected : Workspace.RawWorkspace := {
    entry := "main.solc"
    externalLibraries := []
    mainSources := [{path := "main.solc", content := "function rejected(x: integer, y: integer) returns (integer) { x += y; return x; }"}]}
  match checkProgram rejected with
  | .error [.inference _] => pure ()
  | _ => throw (IO.userError "bare Integer compound source admission changed")

def run : IO Unit := do
  let program ← get "bare assignment checked source" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"bare specialization: {reprStr other}")
  let automatic ← get "bare assignment factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 8) "bare assignment fixture coverage missing"
  integerPolicy automatic.checked
  IO.println "bare assignment: absent/equal, Word/Integer compound, mapping/raw carriers, effects, capture and resume GREEN"

end Tests.SourceCoreCompatibleBareAssignment
