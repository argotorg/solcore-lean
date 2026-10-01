import Solcore.SourceSemantics.CoreLowering.TypedNamedParameterIndexed
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.TypedNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static zero-parameter compilation receipts and concrete checked source
regressions. Semantic certificates are extracted at one actual body context;
neither a universal body IH nor a finite source execution is a static premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedNamedBody

private def source (owner : Resolved.DeclarationId) : TypedSource := {
  owner, inputs := [], roots := [], nodes := [] }
private def compilation (plan : SourceSpecializationWorklist.Plan)
    (owner : SourceSpecialization.SpecializationKey) : SourceCoreFunctions.Context := {
  plan, owner, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) :
    SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan owner) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
}
private def code (fellThrough escaped : Word) : Expr :=
  TypedStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

/-- The typed named body uses the actual contextual compiler and explicit
source context. No `BodyPreserves` or `BodyReflects` premise is hidden here. -/
theorem nil_certificate (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (owner : SourceSpecialization.SpecializationKey)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceSemantics.Context) (fellThrough escaped : Word)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate readFuel values (source owner.declaration) context [] (fun _ => Word.zero) [] [] .unit .unit
      (policy program representation plan owner values assignments diagnostics) 10 fellThrough escaped (code fellThrough escaped)) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan owner)
      (native := none) (parent := none) (skipInitializer := none) ?_ ?_ closed residual ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl rfl .nil rfl rfl
  · constructor
    · intro id node _ found
      change none = some node at found; cases found
    · intro id node _ found
      change none = some node at found; cases found
    · intros; rfl
    · intros; rfl
  · cbv; decide
  · intro binder declared index native selected accepted
    cases selected

example (environment : Environment) (store : Store) (fellThrough escaped : Word) :
    Evaluates environment store (code fellThrough escaped) (.inRight .word .unit) store := by
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal .unit escaped (LocalLoop.fallthrough_evaluates .unit environment store))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit)
        (.inRight .word .unit) store from .inRight .unit))

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Word) }",
  "function empty(flag: Bool, value: Word) { }",
  "function repeated(m: mapping(Bool => Bool)) returns (Bool) { m[true]; return m[false]; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool))) returns (Bool) { (m[true][false], !m[false][true]); return m[false][false] ? m[true][true] : !m[true][false]; }",
  "function early(m: mapping(Bool => Item)) returns (Bool) { return true; m[true]; }",
  "function firstFault(m: mapping(Bool => Item)) returns (Bool) { m[true]; return false; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function keep(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { flag; return f; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 39, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "typed named parameter resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed named result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"typed named inert prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + arguments.length)
        s!"typed named parameter count changed {name}"
    | other => throw (IO.userError s!"typed named execution failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed named bodies" content
    ["empty", "repeated", "nested", "early", "firstFault", "identity", "keep"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  check compiled "empty" [.bool false, .word (Word.ofNatModulo 7)] .unit initial
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .bool) .bool []
  check compiled "repeated" [mapping] (.bool false) initial
  check compiled "nested" [.mapping .bool (.mapping .bool .bool) []] (.bool true) initial
  let item ← SourceCoreUnifiedCorpusSupport.get "typed named Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with
      | some item => Except.ok item
      | none => Except.error "no data signature")
  let missing : SourceTypedRuntime.Value := .mapping .bool (.nominal item.id []) []
  check compiled "early" [missing] (.bool true) initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  check compiled "keep" [.global identity [], .bool false] (.global identity []) initial
  for fuel in [0, 39, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled "firstFault" [missing] fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "typed named fault resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .fault (.typeMismatch expected none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr expected == reprStr (.nominal item.id [] : TypeSystem.Ty))
        "typed named missing-default type changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + 1)
        "typed named missing-default parameter allocation changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap[initial.heap.length]?.map (·.value)) == reprStr (some (some missing)))
        "typed named fault changed its mapping parameter"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        "typed named fault changed inert prefix"
    | other => throw (IO.userError s!"typed named first fault changed: {reprStr other}")
  IO.println "typed named bodies and parameter prefixes: nested indices, raw mapping, callable, early return, exact fault and resume GREEN"

end Tests.SourceCoreTypedNamedParameters
