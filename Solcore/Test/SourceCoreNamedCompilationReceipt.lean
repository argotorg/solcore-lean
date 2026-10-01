import Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt.Receipt.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The generic compiler receipt is instantiated with a concrete static empty
body shape. The typed-prefix consumer uses successful real parameter lowering,
represented arguments and initial environment typing, without final typing or
semantic body assumptions. Native regressions retain captures, raw metadata,
parameter allocation order and checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedCompilationReceipt
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

private theorem empty_request
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (signatures : ProgramSignatures) (plan : SourceSpecializationWorklist.Plan)
    (globals : List SourceCoreCalls.Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option SourceCoreGeneralFunctions.CallableContext)
    (parents : List SourceCoreLocalEvidence.Prepared) (own : SourceCoreProgramFaultSites.Function)
    (named : SourceCoreGeneralFunctions.Function) (resultType : named.signature.resultType = .unit) :
    NamedCompilationReceipt.bodyRequest program representation signatures plan globals diagnostics locals native parents own
      named [] 10 = .ok (CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        own.fellThroughReason own.table.escapedReason) := by
  simp only [NamedCompilationReceipt.bodyRequest, resultType]
  rfl

/-- Only static compiler receipts precede this extraction. The certificate
identifies the actual empty body, independently of its runtime execution. -/
theorem empty_compilation_receipt
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {locals : SourceCoreLocalPolymorphism.Catalog} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {named : SourceCoreGeneralFunctions.Function} {allocate : SourceCoreSourceCells.Allocator} {code : Expr}
    (roots : named.specialized.function.typedBody.roots = []) (resultType : named.signature.resultType = .unit)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some allocate)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native 10 named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals native parents own
      named [] 10 allocate (fun body => body = CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        own.fellThroughReason own.table.escapedReason) code) := by
  apply NamedCompilationReceipt.of_accepted roots parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  have empty := empty_request program representation signatures plan globals diagnostics locals native parents own named resultType
  exact Except.ok.inj (lowered.symm.trans empty)

/-- Two real parameters retain their two projection temporaries as well as
both source references. No continuation body is executed to derive this type. -/
theorem two_parameter_body_typed
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} (left right : TypedBinder) (leftType rightType : Ty) {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner [] onError))
      source [] [(left, leftType), (right, rightType)] output SourceCoreFunctions.argumentProjection body = .ok code)
    (inputs : source.inputs = [left, right])
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {first second : Dynamic.Value} {firstNative secondNative : Value}
    (leftRep : model.Represents mapping world left.scheme.body first firstNative leftType)
    (rightRep : model.Represents mapping world right.scheme.body second secondNative rightType)
    {administrative actualContext : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (agrees : EnvironmentsAgree ξ (.pair firstNative secondNative :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalActual finalStore finalWorld embedding,
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (OptionalCell.referenceType rightType :: rightType :: OptionalCell.referenceType leftType :: leftType :: actualContext)
        nativeDefinitions ∧ WorldExtends world finalWorld ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename embedding) := by
  have arguments : Arguments model mapping world [(left, leftType), (right, rightType)]
      [first, second] [firstNative, secondNative] := .cons leftRep (.cons rightRep .nil)
  obtain ⟨_, _, _, finalActual, finalStore, _, finalWorld, embedding, _, _, _, _, worlds, _, _, typed, agreement⟩ :=
    CallableIndexedParameterTyped.named_prefix onError accepted inputs definitions registered arguments environments heaps
      agrees actualTyped reference read unmapped
  exact ⟨finalActual, finalStore, finalWorld, embedding, typed, worlds, agreement⟩

example (initial : Core.Context) (binder : TypedBinder) :
    CallableIndexedParameterTyped.prefixContext [(binder, .function .word (LanguageResult.resultType .word))] initial =
      OptionalCell.referenceType (.function .word (LanguageResult.resultType .word)) ::
      .function .word (LanguageResult.resultType .word) :: initial := rfl

private def content : String := String.intercalate "\n" [
  "function empty(flag: Bool, value: Word) { }",
  "function selected(flag: Bool, value: Word, values: mapping(Word => Word)) returns (Word) { return flag ? values[value] : value; }",
  "function duplicate(values: mapping(Word => Word), key: Word) returns (Word) { return values[key]; }",
  "function captured(seed: Word) returns (function(Word) returns (Word)) { let shared = seed; return lam(delta: Word) -> Word { shared += delta; return shared; }; }",
  "function identity(value: Word) returns (Word) { return value; }",
  "function invoke(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 23, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "static receipt resumption" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match resumed.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed named receipt result {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"typed named receipt changed initial prefix {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).take arguments.length |>.map (·.value)) == reprStr (arguments.map some))
        s!"typed named receipt parameter order {name}"
    | other => throw (IO.userError s!"typed named receipt failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "generic named receipt" content
    ["empty", "selected", "duplicate", "captured", "identity", "invoke"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩]}
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let key : SourceTypedRuntime.Value := .word (Word.ofNatModulo 2)
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .word) .word
    [(key, seven), (key, .word (Word.ofNatModulo 99))]
  check compiled "empty" [.bool false, seven] .unit initial
  check compiled "selected" [.bool true, key, mapping] seven initial
  check compiled "selected" [.bool false, key, mapping] key initial
  check compiled "duplicate" [mapping, key] seven initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  check compiled "invoke" [.global identity [], seven] seven initial
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled "captured" [seven] 300000 initial
  match first.observation with
  | .done (.closure _ _ _ _ _ captures _) final =>
    SourceCoreUnifiedCorpusSupport.assertTrue (captures.length > 0) "returned closure lost parameter/local captures"
    SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + 2) "closure parameter/local cell count"
  | other => throw (IO.userError s!"closure payload receipt failed: {reprStr other}")
  IO.println "generic named compilation receipt and typed parameter environments: ordered cells, indices, raw mapping, closure and resume GREEN"

end Tests.SourceCoreNamedCompilationReceipt
