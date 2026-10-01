import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameterIndexed
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A static mixed-body receipt and an independent initializer-fault trace
retain the context before the failed declaration. Checked cached calls retain
ordered parameter/local cells, raw mapping metadata and real Core resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreTypedMixedNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open TypedMixedNamedBody

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"typed_mixed_named", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "mixed_named.solc"⟩, 0, 1⟩
private def expression : ExpressionId := ⟨⟨owner, 0⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .bool, [], false, none⟩
private def absentNode : ExpressionNode := {
  id := expression, span, type := .bool, form := .reference "value" (.local (binder 0).id) }
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some expression)⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def statements := [statement 0, statement 1, statement 2]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement,
  nodes := [.expression absentNode, .statement first, .statement second, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial := SourceSemantics.Context.ofSignatures signatures
private def entered := initial.withLocal (binder 0).id (binder 0).scheme
private def complete := entered.withLocal (binder 1).id (binder 1).scheme
private theorem firstExtension : BinderExtends owner initial (binder 0) entered := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := .ofSignatures signatures, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner entered (binder 1) complete := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {binders := (TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _, quantified_nodup := by simp [binder, TypeSystem.Scheme.mono], body := .builtin .bool}
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, entered, initial, SourceSemantics.Context.ofSignatures,
      SourceSemantics.Context.withLocal, binder]
private theorem absentTyped : ExpressionHasType source entered expression .bool := by
  have admitted : TypeAdmissible entered .bool := .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal _ _)
  apply ExpressionHasType.ofOrdinary (node := absentNode) (rawType := .bool) (lookupExpression?_sound rfl)
    (.reference (.local .head .head (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible admitted) []
      .empty (by intro metavariable replacement member; cases member) (SchemeInstantiates.empty_apply _)
      (by simp) (by intro _ member; cases member) .nil))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem absentSyntax : CompatibleExpressionTyped.Syntax source expression :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := absentNode) rfl rfl))))))
private theorem syntaxTree : TypedStatementMixed.Syntax source initial statements .unit :=
  .uninitialized (node := first) rfl rfl rfl rfl firstExtension (by decide)
    (.initialized (node := second) (initializerNode := absentNode) rfl rfl rfl rfl secondExtension (by decide)
      rfl rfl absentTyped absentSyntax (.body (.returnUnit (node := returned) [] rfl rfl rfl)))
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def compilation (plan : SourceSpecializationWorklist.Plan) : SourceCoreFunctions.Context := {
  plan, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 1, solvedRequirements := [], internalReason := Word.zero }
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program) : SourceCoreLoops.Policy := {
  lowerExpression := SourceCoreGeneralFunctions.lowerContextualExpression program representation program.signatures
    ⟨[]⟩ [] assignments diagnostics (compilation plan) none none none
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation ⟨[]⟩ ⟨owner, []⟩ []
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Actual contextual success supplies both let receipts and the remaining
body tree. The static premises contain no child/body semantic theorem. -/
theorem mixed_certificate (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (globals : Nat) (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (plan : SourceSpecializationWorklist.Plan) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (sourceSignatures : initial.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (lowerBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    {fuel : Nat} {code : Expr} (fellThrough escaped : Word)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel
      source [] statements .unit (fun _ => Word.zero) fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts ⟨owner, []⟩ [] frame globals onError readFuel values source initial []
      (fun _ => Word.zero) [] statements .unit .unit
      (policy layouts frame globals onError program representation plan values assignments diagnostics) fuel fellThrough escaped code) := by
  apply of_contextual (locals := ⟨[]⟩) (compilation := compilation plan)
      (native := none) (parent := none) (skipInitializer := none) ?_ unique rfl rfl ?_ sourceSignatures
      readExpression lowerRead leafLowerer rfl lowerBinder rfl rfl rfl syntaxTree rfl accepted
  · constructor
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intro id node _ found
      have member := (lookupExpression?_sound found).1
      simp [source] at member
      subst node
      rfl
    · intros; rfl
    · intros; rfl
  · intro id declared index type selected authentic
    cases selected

private def closure : Dynamic.Closure := ⟨[], .unit, statements, source, [], initial, []⟩
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def faultHeap : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩

/-- The independent source fault occurs in `entered`, before `complete` exists.
It connects directly to the function body trace used by the named bridge. -/
theorem initializer_fault :
    Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements entered
      (.uninitializedLocation ⟨0⟩) faultHeap ∧
    FunctionCallBody.Trace program closure initial [] ⟨[]⟩ (.fault (.uninitializedLocation ⟨0⟩)) faultHeap ∧
    entered ≠ complete := by
  have failed : Dynamic.FunctionStatementsFault program initial [] source [] ⟨[]⟩ statements entered
      (.uninitializedLocation ⟨0⟩) faultHeap := by
    apply Dynamic.FunctionStatementsFault.tail
      (Dynamic.StatementExecutes.letUninitialized (node := first) (lookupStatement?_sound rfl) rfl rfl firstExtension .append)
    apply Dynamic.FunctionStatementsFault.head
    apply Dynamic.StatementFaults.letInitializer (node := second) (lookupStatement?_sound rfl) rfl rfl
    apply Dynamic.ExpressionFaults.form (node := absentNode) (lookupExpression?_sound rfl)
    exact .localUninitialized (owned := []) (coercions := []) (cell := ⟨.bool, none, none⟩)
      rfl .head (.intro .head) rfl rfl (by rintro ⟨key, value, impossible⟩; cases impossible)
  refine ⟨failed, .fault failed, ?_⟩
  intro same
  have impossible : 1 = 2 := congrArg (fun context => context.locals.length) same
  omega

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function mixed(flag: Bool, value: Word) returns (Bool) { let unused: Word; let first = flag; let absent: Bool; let last = !first; return last; }",
  "function lazy(flag: Bool) returns (Bool) { let before: Word; let m: mapping(Bool => Bool); let first = m[flag]; let gap: Bool; let last = m[!flag]; return first || last; }",
  "function nested(m: mapping(Bool => mapping(Bool => Bool)), flag: Bool) returns (Bool) { let before: Word; let first = m[flag][false]; let gap: Bool; let last = !m[!flag][true]; return first ? first : last; }",
  "function early(flag: Bool) returns (Bool) { let first = flag; let gap: Word; return first; let unreachable: Word; }",
  "function absent(flag: Bool) returns (Bool) { let first = flag; let gap: Bool; let failed = gap; let unreachable = true; return unreachable; }",
  "function missing(flag: Bool) returns (Bool) { let first = flag; let gap: Word; let m: mapping(Bool => Item); let failed = m[flag]; return true; }",
  "function identity(flag: Bool) returns (Bool) { return flag; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { let gap: Word; let saved = f; let same = saved; return same; }"
]

private def finished (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initialState : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let firstResult ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initialState
  let result ← SourceCoreUnifiedCorpusSupport.get "typed mixed named resume" (SourceCoreUnifiedCompilation.Result.resume firstResult 300000)
  pure result.observation

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (initialState : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    match ← finished compiled name arguments fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"typed mixed named result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        s!"typed mixed named prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
        s!"typed mixed named ordered cells changed {name}: {reprStr final.heap}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"typed mixed named unsafe final heap {name}"
    | other => throw (IO.userError s!"typed mixed named failed {name}: {reprStr other}")

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name localName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "typed mixed named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "typed mixed named exact binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "typed mixed named bodies" content
    ["mixed", "lazy", "nested", "early", "absent", "missing", "identity", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  let flag : SourceTypedRuntime.Value := .bool false
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  check compiled "mixed" [flag, seven] (.bool true)
    [(.bool, some flag), (.word, some seven), (.word, none), (.bool, some flag), (.bool, none), (.bool, some (.bool true))] initialState
  let emptyMap : SourceTypedRuntime.Value := .mapping .bool .bool []
  check compiled "lazy" [flag] flag
    [(.bool, some flag), (.word, none), (.mapping .bool .bool, some emptyMap), (.bool, some flag), (.bool, none), (.bool, some flag)] initialState
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .bool) (.mapping .bool .bool) []
  check compiled "nested" [rawMap, flag] (.bool true)
    [(.mapping .bool (.mapping .bool .bool), some rawMap), (.bool, some flag), (.word, none), (.bool, some flag), (.bool, none), (.bool, some (.bool true))] initialState
  check compiled "early" [flag] flag [(.bool, some flag), (.bool, some flag), (.word, none)] initialState
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let fn : SourceTypedRuntime.Value := .global identity []
  check compiled "callable" [fn, flag] fn
    [(.function .bool .bool, some fn), (.bool, some flag), (.word, none), (.function .bool .bool, some fn), (.function .bool .bool, some fn)] initialState
  let gap ← faultBinder compiled "absent" "gap"
  for fuel in [0, 41, 300000] do
    match ← finished compiled "absent" [flag] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "failed initializer changed its exact fault binder"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initialState.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([ (.bool, some flag), (.bool, some flag), (.bool, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)))
        "failed initializer allocated a binder or changed preceding source cells"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        "failed initializer changed the inert prefix"
    | other => throw (IO.userError s!"typed mixed named initializer fault changed: {reprStr other}")
    match ← finished compiled "missing" [flag] fuel initialState with
    | .fault (.typeMismatch raw none) final =>
      let item ← SourceCoreUnifiedCorpusSupport.get "typed mixed named Item"
        (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "missing-default raw result metadata changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initialState.heap.length + 4)
        "missing-default initializer allocated its failed binder"
      match (final.heap.drop initialState.heap.length)[3]? with
      | some cell =>
        match cell.type, cell.value with
        | .mapping .bool valueType, some (.mapping .bool valueMetadata []) =>
          SourceCoreUnifiedCorpusSupport.assertTrue (valueType == raw && valueMetadata == raw)
            "lazy mapping initialization lost raw nominal metadata"
        | _, _ => throw (IO.userError s!"missing-default source mapping changed: {reprStr cell}")
      | none => throw (IO.userError "missing-default source mapping disappeared")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initialState.heap.length) == reprStr initialState.heap)
        "missing-default initializer changed the inert prefix"
    | other => throw (IO.userError s!"typed mixed named missing default changed: {reprStr other}")
  IO.println "typed mixed named bodies: reached contexts, parameter/local order, lazy nested mappings, callable aliases, exact initializer faults and resume GREEN"

end Tests.SourceCoreTypedMixedNamedParameters
