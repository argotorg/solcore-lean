import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
import Solcore.Test.SourceCoreUnifiedCorpusSupport
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! The public named Head consumers close RHS/body meanings with concrete
recursive named Trees, preserving actual installed authority and typed slots.
Core-only admitted sources exercise absent/present scalars, post-write faults,
raw mapping copies, exact argument effects, opaque prefix and real resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedBareNamedAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open NamedAssignmentHeads CompatibleEquality CompatibleHeap CoreProof
section Static
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : SourceSemantics.Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) :=
  NamedAssignmentHeads.preserves_prefix functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing trace

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentHeads.preserves_fault functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors trace next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_reflects (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :=
  NamedAssignmentHeads.reflects functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors completed

end Static

private def content : String := String.intercalate "\n" [
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function key(value: Word) returns (Word) { let copied = value; return copied; }",
  "function same(raw: mapping(Word => Word)) returns (mapping(Word => Word)) { let copied = raw; return copied; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function absentEqual(seed: Word) returns (Word) { let root: Word; root = first(seed); return first(root); }",
  "function compoundPresent(seed: Word) returns (Word) { let root = first(10); root += first(seed); return first(root); }",
  "function absentCompound(seed: Word) returns (Word) { let root: Word; root += first(seed); return first(99); }",
  "function rhsFault(seed: Word) returns (Word) { let root = first(10); root += bad(seed); return first(99); }",
  "function lateFault(seed: Word) returns (Word) { let root = first(10); root += first(seed); return bad(root); }",
  "function assignmentUnit(seed: Word) { let root: Word; root = first(seed); first(root); }",
  "function rawEqual(raw: mapping(Word => Word)) returns (Word) { let root: mapping(Word => Word); root = same(raw); return first(root[key(1)]); }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word,some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"guarded bare resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"guarded bare prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type,cell.value))) == reprStr expected)
    s!"guarded bare ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "guarded bare gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "guarded bare exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected bare named assignments" content
    ["absentEqual","compoundPresent","absentCompound","rhsFault","lateFault","assignmentUnit","rawEqual"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word,none⟩,⟨.word,some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0,43,300000] do
    for (name,result,numbers) in [("absentEqual",7,[7,7,7,7,7,7]),("compoundPresent",17,[7,10,10,17,7,7,17,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .done value final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue result)) s!"guarded bare result {name}"
        cells initial final (numbers.map present) name
      | other => throw (IO.userError s!"guarded bare {name}: {reprStr other}")
    match ← finish compiled "absentCompound" [wordValue 7] fuel initial with
    | .fault (.invalidAssignmentOperands operator left right) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (operator == .add && left == none && right == some .word) "absent compound diagnostics changed"
      cells initial final [present 7,(.word,none),present 7,present 7] "absentCompound"
    | other => throw (IO.userError s!"guarded bare absent compound: {reprStr other}")
    for (name,numbers) in [("rhsFault",[7,10,10,10,7]),("lateFault",[7,10,10,17,7,7,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"guarded bare fault binder {name}"
        cells initial final (numbers.map present ++ [(.word,none)]) name
      | other => throw (IO.userError s!"guarded bare written fault {name}: {reprStr other}")
    match ← finish compiled "assignmentUnit" [wordValue 7] fuel initial with
    | .done .unit final => cells initial final ([7,7,7,7,7,7].map present) "assignmentUnit"
    | other => throw (IO.userError s!"guarded bare Unit: {reprStr other}")
    let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
      [(wordValue 1,wordValue 37),(wordValue 1,wordValue 91)]
    match ← finish compiled "rawEqual" [raw] fuel initial with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue 37)) "raw bare mapping order changed"
      let copied : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.mapping .word .word,some raw)
      cells initial final ([copied,copied,copied,copied] ++ [1,1,37,37].map present) "rawEqual"
    | other => throw (IO.userError s!"guarded bare raw mapping: {reprStr other}")
  IO.println "protected bare named assignments: concrete RHS/body guards, actual snapshots/typed seven slots, absent operands, write-before-fault, raw duplicate mappings/prefix and resume GREEN"
end Tests.SourceCoreProtectedBareNamedAssignments
