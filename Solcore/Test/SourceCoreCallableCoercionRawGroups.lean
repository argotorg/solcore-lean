import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
import Solcore.Test.SourceCompilerFeatureSupport

/-! The consumers begin with actual delegated acceptance and its actual
contextual callback, then close raw meaning with a concrete builtin child.
Runtime fixtures deliberately insert retained IR groups; they do not claim the
parser or checker places a coercion on the written group's parent node. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawGroups
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionRawGroupCertificates

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  (receipt : Delegated compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)


variable {readFuel : Nat} {inner : ExpressionId}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (rawUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (rawMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {administrative : Core.Context} {canonical : Environment} {actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)


variable {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localsCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localsCatalog parents
    assignments diagnostics compilation (some native) parent skipInitializer)
  (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type)
  (avoids : CallableLambdaBodyReachability.Avoids source [.expression inner] [node.id])
  (syntaxTree : CompatibleExpressionBuiltins.Syntax source inner)
  (ordinary : CompatibleExpressionBuiltins.Ordinary (SourceCoreEvidence.withNode source (rawNode node [])) localsCatalog compilation.owner)
  (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (SourceCoreEvidence.withNode source (rawNode node [])) scope context)
  (sourceSignatures : context.signatures = values.checked.signatures)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry valid rawUninitialized rawMissing environments heaps locals agrees actualTyped childEq form typed avoids syntaxTree ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy in
theorem accepted_preserves
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨childTree⟩ := CallableCoercionRawGroupCertificates.of_contextual receipt childEq unique form typed avoids syntaxTree
    ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawGroupMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt emitted steps chain ledger entry childTree valid rawUninitialized rawMissing
    environments heaps locals agrees actualTyped unique trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry valid rawUninitialized rawMissing environments heaps locals agrees actualTyped childEq form typed avoids syntaxTree ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy in
theorem accepted_reflects
    (unique : NodeOccurrencesUnique source)
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨childTree⟩ := CallableCoercionRawGroupCertificates.of_contextual receipt childEq unique form typed avoids syntaxTree
    ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawGroupMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt emitted steps chain entry childTree valid rawUninitialized rawMissing
    environments heaps locals agrees actualTyped completed

end Accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function identity(value: Word) returns (Word) { let rawEffect: Word = 19; return value; }",
    "function rawFail() returns (Word) { let rawEffect: Word = 23; let rawGap: Word; return rawGap; }",
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = identity(value); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }",
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value + 0; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value + 0; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = rawFail(); return result; }",
    "function operand() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let missing: Word; let result: Final = missing + 0; return result; }",
    "function empty(value: Word) returns (Word) { return value; }"
  ]}] }


private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")


/-- Insert a fresh raw child below the original selected occurrence. The parent
keeps the exact requirement IDs and plan edges. This is retained IR test data,
not a claim about where inference attaches output coercions in surface groups. -/
private def auditRetainedGroup (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "raw group caller missing")
  let caller := named.specialized
  let original := caller.function.typedBody
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let indexed := entry.cached.indexed
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "raw group diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
    | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "raw group owner diagnostics missing")
  let mut localScope : Scope := []
  for binder in SourceCoreDataPlaces.declaredBinders original do
    if binder.name == "missing" then
      let native ← SourceCompilerFeatureSupport.get "raw group local type" (entry.cached.compatible.checked.catalog.project binder.scheme.body)
      localScope := (binder.id, native) :: localScope
  let scope := localScope ++ named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
  let reasonAt := diagnostics.reasonAt named.signature.key
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let mut count := 0
  for item in original.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        if let .binary .. := node.form then
          let fresh : ExpressionId := ⟨⟨original.owner, 100000 + node.id.occurrence.index⟩⟩
          SourceCompilerFeatureSupport.require (original.lookupExpression? fresh |>.isNone) "raw group fresh ID collided"
          let inner := {rawNode node [] with id := fresh}
          let outer := {node with form := .group fresh}
          let source := {(SourceCoreEvidence.withNode original outer) with
            nodes := (SourceCoreEvidence.withNode original outer).nodes ++ [.expression inner]}
          SourceCompilerFeatureSupport.require (source.lookupExpression? node.id == some outer &&
            source.lookupExpression? fresh == some inner && outer.requirements == node.requirements &&
            outer.coercions == node.coercions && SourceCompilationPlan.ordinaryOwnedRequirements? outer == some [])
            "raw group lost exact retained metadata"
          let rawSource := SourceCoreEvidence.withNode source (rawNode outer [])
          let rootCode ← SourceCompilerFeatureSupport.get "actual sanitized group child" (child 150 rawSource scope outer.id reasonAt)
          let innerCode ← SourceCompilerFeatureSupport.get "actual sanitized inner subtree" (child 150 rawSource scope fresh reasonAt)
          let originalInner ← SourceCompilerFeatureSupport.get "original source inner subtree" (child 150 source scope fresh reasonAt)
          SourceCompilerFeatureSupport.require (rootCode == innerCode && innerCode == originalInner)
            "actual group/sanitizer changed child code"
          let lowered ← SourceCompilerFeatureSupport.get "actual retained group outer"
            (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
              150 source scope outer.id reasonAt policy)
          let prior ← SourceCompilerFeatureSupport.get "actual prior delegated outer"
            (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
              150 original scope node.id reasonAt policy)
          SourceCompilerFeatureSupport.require (lowered.isSome && lowered == prior)
            "retained group changed the full ordered native expression"
          let available ← SourceCompilerFeatureSupport.get "actual group evidence"
            (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
          let suffix ← SourceCompilerFeatureSupport.get "actual group suffix"
            (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType compilation caller available scope outer policy rootCode outer.coercions)
          SourceCompilerFeatureSupport.require (lowered == some suffix) "group suffix code/order changed"
          let noneResult := SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation
            (fun _ _ _ id _ => .error (.missingExpression id)) 150 rawSource scope outer.id reasonAt policy
          SourceCompilerFeatureSupport.require (match noneResult with | .ok none => true | _ => false)
            "empty group path must bypass before a rejecting child"
          count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "retained group fixture lacks one delegated occurrence"

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "raw group checked fixture" (checkProgram workspace 1024)
  for name in ["path", "late", "operand"] do
    auditRetainedGroup (← SourceCompilerFeatureSupport.compileNamed checked name)
  let operand ← SourceCompilerFeatureSupport.compileNamed checked "operand"
  for budget in [0, 41, 137, 500000] do
    let initial ← operand.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "raw group operand resume" (initial.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state =>
      SourceCompilerFeatureSupport.require
        (reprStr (state.heap.map fun cell => (cell.type, cell.value)) ==
          reprStr ([(.word, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)))
        "raw group operand fault did not skip every method allocation"
    | other => throw (IO.userError s!"raw group operand outcome changed: {reprStr other}")
  let box ← constructorFor checked "Box"
  let final ← constructorFor checked "Final"
  let broken ← constructorFor checked "Broken"
  let path ← SourceCompilerFeatureSupport.compileNamed checked "path"
  let late ← SourceCompilerFeatureSupport.compileNamed checked "late"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (late, true)] do
        let initial ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "raw group exact-artifact resume" (initial.resume 500000)
        let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "retained group original artifact changed successful result"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "all methods"
        | .fault (.uninitializedLocal binder) state =>
          let expectedName := if input == 0 then "firstGap" else if input == 2 then "secondGap" else "lastGap"
          let declarations := entry.cached.indexed.base.functions.flatMap
            (fun named => SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody)
          SourceCompilerFeatureSupport.require (declarations.any (fun declared => declared.id == binder && declared.name == expectedName))
            "retained group changed the actual first fault binder"
          if input == 0 then cells state (firstCells ++ [(.bool, none)]) "first method; suffix skipped"
          else if input == 2 then cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle method; suffix skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1) "unexpected terminal method fault"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "final method"
        | other => throw (IO.userError s!"raw group artifact outcome changed: {reprStr other}")
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume operand []
  IO.println "raw groups: retained IR sanitizer/child/full suffix code equality, empty bypass, same-artifact ordered heaps/faults/public resume GREEN"

end Tests.SourceCoreCallableCoercionRawGroups
