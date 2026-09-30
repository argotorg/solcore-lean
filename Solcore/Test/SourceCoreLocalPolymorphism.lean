import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.Core.ExactFuelProperties

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue

/-! Discovery/projection tests use checked source metadata. Shared capture
execution uses an explicit typed Core bundle; this module does not claim that
the whole source compiler already routes generalized local lets through it. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalPolymorphism

open Solcore Solcore.Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sameInnerType(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function dependentInner(flag: Bool) returns ((Word, Word), (Bool, Bool)) {",
    " let outer = lam(value) { let inner = lam(item) { return (value, item); }; return inner(value); };",
    " return (outer(1), outer(flag)); }",
    "function sharedCapture(flag: Bool) returns (Word) {",
    " let total: Word = 0; let f = lam(item) { total += 1; return item; };",
    " f(1); f(flag); f(2); return total; }",
    "function qualified(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function unused() returns (Word) {",
    " let outer = lam(value) { let inner = lam(item) { return item; }; return inner(value); }; return 9; }"
  ] }] }

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"local bundle fixture missing: {name}")
  pure ⟨signature.id, []⟩

private def plan (program : CheckedProgram) (requests : List SourceSpecializationWorklist.Request) :
    IO SourceSpecializationWorklist.Plan :=
  match SourceSpecializationWorklist.run program requests 64 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"local bundle worklist failed: {reprStr other}")

private def binding (catalog : Catalog) (name : String) : IO Binding :=
  match catalog.bindings.filter (·.binder.name == name) with
  | [binding] => pure binding
  | _ => throw (IO.userError s!"local bundle binding missing: {name}")

private def references (binding : Binding) : List ExpressionId :=
  binding.source.nodes.filterMap fun
    | .expression { id, form := .reference _ (.local selected), .. } =>
        if selected == binding.binder.id then some id else none
    | _ => none

private def checkRead (binding : Binding) (catalog : Catalog) (active : Substitution)
    (id : ExpressionId) : IO SourceCoreBasic.LoweredExpr := do
  let source := binding.source.applySubstitution active
  let payload := binding.bundleType active
  match lowerRead catalog binding.caller active source [(binding.binder.id, payload)] id (word 31) with
  | .ok lowered =>
      assertTrue (Core.infer? [Core.OptionalCell.referenceType payload] lowered.expression ==
        some (Core.LanguageResult.resultType lowered.type)) "local bundle read did not type-check"
      pure lowered
  | .error error => throw (IO.userError s!"local bundle read rejected: {reprStr error}")

/-- Both instances capture the same reference at index zero. Their argument
types differ; both increment the same optional Word cell before returning it. -/
private def countingClosure (parameter : Core.Ty) : Core.Expr :=
  Core.TaggedFunction.anonymous (.lambda parameter (Core.LanguageResult.resultType parameter)
    (Core.LanguageResult.bind parameter (Core.OptionalCell.read .word (.var 1) (word 31))
      (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
        (Core.LanguageResult.success (.var 2)))))

private def wordFunction : Core.Ty := Core.TaggedFunction.functionType .word .word
private def boolFunction : Core.Ty := Core.TaggedFunction.functionType .bool .bool
private def bundleType : Core.Ty := ProductBundle.type [wordFunction, boolFunction]
private def readWord : Core.Expr := read bundleType wordFunction (.var 0) (.first (.var 0)) (word 31)
private def readBool : Core.Expr := read bundleType boolFunction (.var 0) (.second (.var 0)) (word 31)
private def sharedProgram : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := Core.LocalSequence.letInitialized .word .word (Core.LanguageResult.success (literal 0))
    (Core.LocalSequence.letInitialized .word bundleType
      (Core.LanguageResult.success (ProductBundle.expression [countingClosure .word, countingClosure .bool]))
      (Core.LocalSequence.discard .word
        (Core.TaggedFunction.call .word readWord (Core.LanguageResult.success (literal 7)))
        (Core.LocalSequence.discard .word
          (Core.TaggedFunction.call .bool readBool (Core.LanguageResult.success (.bool true)))
          (Core.OptionalCell.read .word (.var 1) (word 31))))) }

example {definitions : Core.DataEnvironment} {context : Core.Context}
    {left right : Core.Expr}
    (leftTyped : Core.HasType context left wordFunction definitions)
    (rightTyped : Core.HasType context right boolFunction definitions) :
    Core.HasType context (ProductBundle.expression [left, right]) bundleType definitions :=
  ProductBundle.expression_hasType (.cons leftTyped (.cons rightTyped .nil))

example {definitions : Core.DataEnvironment} {context : Core.Context} {bundle : Core.Expr}
    (typed : Core.HasType context bundle bundleType definitions) :
    Core.HasType context (.second bundle) boolFunction definitions :=
  ProductBundle.project_hasType (types := [wordFunction, boolFunction]) (index := 1) rfl rfl typed

example {environment : Core.Environment} {store : Core.Store} :
    Core.Evaluates environment store
      (ProductBundle.expression [countingClosure .word, countingClosure .bool])
      (ProductBundle.value [
        .pair (.inLeft .word .unit) (.closure .word (Core.LanguageResult.resultType .word)
          (Core.LanguageResult.bind .word (Core.OptionalCell.read .word (.var 1) (word 31))
            (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
              (Core.LanguageResult.success (.var 2)))) environment),
        .pair (.inLeft .word .unit) (.closure .bool (Core.LanguageResult.resultType .bool)
          (Core.LanguageResult.bind .bool (Core.OptionalCell.read .word (.var 1) (word 31))
            (.letE (.storeCell (.var 2) (.inRight .unit (.binary .wordAdd (.var 0) (literal 1))))
              (Core.LanguageResult.success (.var 2)))) environment)]) store :=
  ProductBundle.expression_evaluates (.cons (.pair (.inLeft .unit) .lambda)
    (.cons (.pair (.inLeft .unit) .lambda) .nil))

private theorem sharedProgram_checked : sharedProgram.check = true := by
  simp [sharedProgram, Core.LocalSequence.letInitialized, Core.LocalSequence.discard,
    Core.OptionalCell.read, Core.OptionalCell.allocateInitialized, SourceCoreLocalPolymorphism.read,
    ProductBundle.expression,
    ProductBundle.type, bundleType, wordFunction, boolFunction, Core.TaggedFunction.call,
    Core.TaggedFunction.anonymous, countingClosure, readWord, readBool,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.LanguageResult.bind, Core.Expr.weakenAt, literal]
  decide

example (fuel : Nat) : (sharedProgram.runStateful fuel).HasType sharedProgram.resultType :=
  Core.Program.checked_runStateful_has_type sharedProgram_checked fuel

example (fuel additional : Nat) (checkpoint : Core.State)
    (exhausted : sharedProgram.runStateful fuel = .outOfFuel checkpoint) :
    Core.runStateful additional checkpoint = sharedProgram.runStateful (fuel + additional) :=
  Core.runStateful_resume exhausted additional

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"local bundle source rejected: {reprStr error}")
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128 [.word, .bool] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"local bundle scalar catalog failed: {reprStr error}")
  let samePlan ← plan program [← request program "sameInnerType"]
  let same ← match prepare checked samePlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"contextual local bundle discovery failed: {reprStr error}")
  let outer ← binding same "outer"
  let inner ← binding same "inner"
  assertTrue (outer.instances.length == 2 && inner.instances.length == 2)
    "nested local instances were lost"
  match inner.instances with
  | [first, second] =>
      assertTrue (first.type == second.type && first.origin.substitution != second.origin.substitution)
        "equal final function types merged different outer contexts"
  | _ => throw (IO.userError "expected two nested contexts")
  for candidate in outer.instances do
    let active := candidate.origin.substitution
    assertTrue ((inner.atContext active).length == 1) "nested bundle selected another outer context"
    assertTrue (inner.bundleType active == wordFunction) "singleton contextual bundle changed its type"
    for id in references inner do discard <| checkRead inner same active id
    match lowerBinder same inner.caller active (inner.source.applySubstitution active) []
      (inner.binder.applySubstitution active) with
    | .ok payload => assertTrue (payload == wordFunction) "contextual binder payload mismatch"
    | .error error => throw (IO.userError s!"contextual binder metadata rejected: {reprStr error}")

  let dependentPlan ← plan program [← request program "dependentInner"]
  let dependent ← match prepare checked dependentPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"dependent nested local metadata failed: {reprStr error}")
  let dependentOuter ← binding dependent "outer"
  let dependentInner ← binding dependent "inner"
  for candidate in dependentOuter.instances do
    let active := candidate.origin.substitution
    assertTrue ((dependentInner.atContext active).length == 1) "dependent inner lost its enclosing context"
    for id in references dependentInner do discard <| checkRead dependentInner dependent active id

  let sharedPlan ← plan program [← request program "sharedCapture", ← request program "sharedCapture"]
  let shared ← match prepare checked sharedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"shared local bundle discovery failed: {reprStr error}")
  let f ← binding shared "f"
  assertTrue (f.instances.length == 2 && f.bundleType [] == bundleType)
    "repeated same-type uses or duplicate roots duplicated local closures"
  let types ← (references f).mapM fun id => return (← checkRead f shared [] id).type
  assertTrue (types == [wordFunction, boolFunction, wordFunction]) "local read selected the wrong bundle ordinal"
  match lowerBinder shared f.caller [] f.source [] { f.binder with name := "forged" } with
  | .error (.bindingMetadataMismatch _) => pure ()
  | _ => throw (IO.userError "tampered generalized binder metadata was accepted")
  match lowerBinder shared f.caller [] f.source [(f.binder.id, bundleType)] f.binder with
  | .error (.metadata (.duplicateBinding _)) => pure ()
  | _ => throw (IO.userError "duplicate generalized binder scope was accepted")
  let firstRead ← match references f with
    | id :: _ => pure id
    | [] => throw (IO.userError "shared local lost its read occurrences")
  let tampered := { f.source with nodes := f.source.nodes.map fun
    | .expression node => .expression (if node.id == firstRead then { node with type := .bool } else node)
    | .statement node => .statement node }
  match lowerRead shared f.caller [] tampered [(f.binder.id, bundleType)] firstRead (word 31) with
  | .error (.bindingMetadataMismatch _) => pure ()
  | _ => throw (IO.userError "tampered local read bypassed the original scheme metadata")
  let total ← match f.source.nodes.findSome? fun
      | .statement { form := .letDecl binder _, .. } => if binder.name == "total" then some binder.id else none
      | _ => none with
    | some total => pure total
    | none => throw (IO.userError "shared source capture disappeared")
  for candidate in f.instances do
    assertTrue (candidate.origin.instantiatedBodyNodes.filterMap (fun
      | .statement { form := .assignValue assignment _ _, .. } => some assignment.target.root
      | _ => none) == [total]) "local instantiation changed the shared source reference identity"

  let unusedPlan ← plan program [← request program "unused"]
  let unused ← match prepare checked unusedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"unused local bundle failed: {reprStr error}")
  for binding in unused.bindings do
    assertTrue (binding.instances.isEmpty && binding.bundleType [] == .unit) "unused local requires a dummy function"
    match lowerInitializer binding [] (fun candidate => .error (.openInstance binding.binder.id candidate.origin.binder.scheme.body)) with
    | .ok lowered =>
        assertTrue (lowered.type == .unit && lowered.expression == Core.LanguageResult.success .unit)
          "empty local initializer invoked its closure compiler"
    | .error _ => throw (IO.userError "unused bundle attempted to compile a nonexisting instance")

  let qualifiedPlan ← plan program [← request program "qualified"]
  let qualified ← match prepare checked qualifiedPlan with
    | .ok catalog => pure catalog
    | .error error => throw (IO.userError s!"qualified local metadata discovery failed: {reprStr error}")
  let qualifiedF ← binding qualified "f"
  assertTrue (qualifiedF.instances.length == 2 && !qualifiedF.binder.schemeRequirements.isEmpty)
    "local catalog discarded qualified template metadata"
  for candidate in qualifiedF.instances do
    assertTrue (candidate.origin.solvedRequirements ==
      (qualifiedPlan.specializations.find? (fun function => function.key == candidate.origin.caller) |>.map
        (·.function.solvedRequirements) |>.getD [])) "local catalog substituted the original evidence ledger"
  match prepare checked samePlan (some 0) with
  | .error (.discovery (.localPolymorphicContextFuelExhausted _)) => pure ()
  | _ => throw (IO.userError "bounded local instance discovery bypassed exhaustion")
  match prepare checked { samePlan with specializations := samePlan.specializations ++ samePlan.specializations } with
  | .error (.discovery (.duplicatePlanSpecializations _ 2)) => pure ()
  | _ => throw (IO.userError "duplicate enclosing specialization was accepted")

  assertTrue sharedProgram.check "shared instance bundle did not pass the Core checker"
  match sharedProgram.runStateful 65536 with
  | .done (.inRight .word (.word result)) store =>
      assertTrue (result == word 2 && store[0]? == some (.inRight .unit (.word (word 2))))
        "two closures did not mutate the same captured optional cell"
  | _ => throw (IO.userError "shared instance bundle execution failed")
  match sharedProgram.runStateful 2 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 65536 checkpoint == sharedProgram.runStateful 65538)
        "shared local bundle checkpoint changed execution"
  | _ => throw (IO.userError "shared local bundle did not suspend")
  IO.println "local polymorphism catalog, exact contexts and typed shared bundles GREEN"

end Tests.SourceCoreLocalPolymorphism
