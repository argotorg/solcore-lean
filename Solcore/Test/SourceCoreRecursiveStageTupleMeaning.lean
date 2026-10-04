import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceRecursiveStageTupleExpressions
import Solcore.Test.SourceCoreRecursiveStagePrimitiveMeaning

/-! Actual tuple acceptance retains the ordered child receipts. These static
obligations are explicit; the staged meanings of the children come from the
single supported-tree proof. The runtime audit retains every ledger row and cell. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageTupleMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly RecursiveStageTupleMeaning

section Accepted
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {budget fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {reasonAt : ExpressionId → Word}
  {code : SourceCoreBasic.LoweredExpr}
  (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
  (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
  (special : ∀ child remaining, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok code)
  (extract : ∀ child, child ∈ ids → ∀ childNode lowered, source.lookupExpression? child = some childNode →
    ExpressionHasType source context child childNode.type →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok lowered →
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope child lowered)

include unique found form typed special readPolicy leafPolicy accepted extract in
theorem accepted_root : Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  of_functions unique found form typed special readPolicy leafPolicy accepted extract

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger runtime uninitialized in
theorem accepted_reflects
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects functions program stages invocation sameSource sameLedger runtime uninitialized
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees evaluated

include unique found form typed special readPolicy leafPolicy accepted extract sameSource sameLedger runtime uninitialized in
theorem accepted_preserves (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {mapping : LocationMap} {world : StoreTyping} {admin : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      admin scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type code.type (FaultRep faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves functions program stages invocation sameSource sameLedger runtime uninitialized unique extension
    (accepted_root unique found form typed special readPolicy leafPolicy accepted extract)
    (sameSource ▸ found) environments heaps locals agrees trace
end Accepted

section Static
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id child : ExpressionId} {node childNode : ExpressionNode}
  {code : SourceCoreBasic.LoweredExpr}

theorem accepted_leaf {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context}
    (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ action remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation action remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  literal (CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted)

/-- Three occurrences retain the same real leaf receipt three times, in order. -/
theorem repeated_three
    (header : CompatibleExpressionTuples.Header values source id node [child, child, child]
      [childNode.type, childNode.type, childNode.type] [code, code, code])
    (found : source.lookupExpression? child = some childNode)
    (leaf : Certificate fuel values source context solved reasonAt scope child code) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments [code, code, code]) := by
  obtain ⟨tree, sites⟩ := leaf
  let entries := [(child, code)]
  have sequence : DataExpressionSequence.Tree source (Entries scope entries) scope
      [child, child, child] [childNode.type, childNode.type, childNode.type] [code, code, code] :=
    .cons found ⟨rfl, by simp [entries]⟩ (.cons found ⟨rfl, by simp [entries]⟩ (.single found ⟨rfl, by simp [entries]⟩))
  have children : ∀ current lowered, (current, lowered) ∈ entries → Tree fuel values source context solved reasonAt scope current lowered := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact tree
  have support : ∀ current lowered (member : (current, lowered) ∈ entries), Supported (children current lowered member) := by
    intro current lowered member
    have same : current = child ∧ lowered = code := by simpa [entries, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact sites
  exact ⟨.tuple header sequence children, .tuple header sequence children support⟩

theorem empty_tuple
    (header : CompatibleExpressionTuples.Header values source id node [] [] []) :
    Certificate fuel values source context solved reasonAt scope id (SourceCoreCalls.packArguments []) := by
  have children : ∀ child code, (child, code) ∈ ([] : List (ExpressionId × SourceCoreBasic.LoweredExpr)) →
      Tree fuel values source context solved reasonAt scope child code := by simp
  exact ⟨.tuple header .nil children, .tuple header .nil children (by simp)⟩

abbrev original_source_inversion := @RecursiveStageTupleMeaning.source_inv
abbrev old_unit := @Tests.SourceCoreRecursiveStagePrimitiveMeaning.source_unit
abbrev old_pair := @Tests.SourceRecursiveStageTupleExpressions.old_pair
abbrev singleton_source := @Tests.SourceRecursiveStageTupleExpressions.singleton
abbrev first_source_fault := @Tests.SourceRecursiveStageTupleExpressions.stage_at_head
abbrev later_source_fault := @Tests.SourceRecursiveStageTupleExpressions.stage_after_prefix
end Static

section Boundaries
theorem no_stage_result {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {id : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ FaultRep faults (.stage scope id reason) token := by intro impossible; exact impossible

abbrev nonempty_not_atomic := @Tests.SourceRecursiveStageTupleExpressions.nonempty_tuple_not_atomic
abbrev required_parent := @Tests.SourceRecursiveStageTupleExpressions.required_parent_excluded
abbrev coerced_parent := @Tests.SourceRecursiveStageTupleExpressions.coerced_parent_excluded
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : Core.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function empty() { let unused: Word = 13; return (); }",
  "function single() returns (Word) { return (7); }",
  "function pair(a: Word, b: Word) returns ((Word, Word)) { return (a + 3, ~b); }",
  "function triple(a: Word, b: Word) returns ((Word, Bool, Word)) { return (a + 3, true, ~b); }",
  "function nested(a: Word, b: Word) returns (((Word, Bool, Word), Word, Bool)) { return ((a, true, 3), b, false); }",
  "function firstFault() returns ((Word, Word, Word)) { let first: Word; let second: Word; return (first, second, 3); }",
  "function laterFault() returns ((Word, Word, Word)) { let first: Word = 9; let second: Word; return (first, second, 3); }"
]

private def finish (code : Core.Expr) (environment : Core.Environment) (store : Core.Store) (fuel : Nat) : IO (Core.Value × Core.Store) := do
  let first := Core.runStateful fuel (.initial code environment store)
  let result := match first with
    | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
    | other => other
  match result with
  | .done value after => pure (value, after)
  | other => throw (IO.userError s!"native staged tuple incomplete: {reprStr other}")

/-- The singleton and repeated-three cases are retained IR mutations of an
actual checked group; all other root tuples come directly from the checker. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut cases := 0
  let mut lengths : List Nat := []
  for name in ["empty", "single", "pair", "triple", "nested", "firstFault", "laterFault"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "actual tuple root not unique")
    let selected ← get "same full tuple specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "tuple full metadata changed"
    let original := selected.function.typedBody
    let binders := (SourceCoreDataPlaces.declaredBinders original).reverse
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let captured := Core.Value.closure .unit .word (.var 1) [w 97, w 101]
    let initialCells : Core.Store := [captured, w 103]
    let mut scope : SourceCoreLocalCell.Scope := []
    let mut native : Core.Environment := []
    let mut fields : Core.Store := []
    for binder in binders do
      let type ← get "tuple ordinary read actual type" (values.checked.catalog.project binder.scheme.body)
      require (binder.scheme.quantified.isEmpty && binder.schemeRequirements.isEmpty) "tuple read generalized"
      scope := scope ++ [(binder.id, type)]
      native := native ++ [.cellRef (OptionalCell.cellType type) (initialCells.length + fields.length)]
      let payload : Option Core.Value := if binder.name == "a" then some (w 11) else if binder.name == "b" then some (w 5)
        else if binder.name == "first" && name == "laterFault" then some (w 9) else none
      fields := fields ++ [match payload with | some value => .inRight .unit value | none => .inLeft type .unit]
    native := native ++ [captured]
    let store := initialCells ++ fields
    let reasonAt := fun id : ExpressionId => Word.ofNatModulo (2000 + id.occurrence.index)
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression ⟨⟨original.owner, 0⟩⟩ (.tuple []))
    let results := original.nodes.filterMap fun item => match item with
      | .statement statement => match statement.form with | .returnStmt (some id) => some id | _ => none
      | _ => none
    let id ← match results with | [id] => pure id | _ => throw (IO.userError "tuple return occurrence changed")
    let node ← match original.lookupExpression? id with | some node => pure node | none => throw (IO.userError "tuple node absent")
    let variants ← if name == "single" then do
      let child ← match node.form with | .group child => pure child | _ => throw (IO.userError "checked singleton group changed")
      let childNode ← match original.lookupExpression? child with | some child => pure child | none => throw (IO.userError "group child absent")
      pure ([1, 3].map fun count =>
        let ids := List.replicate count child
        {original with nodes := original.nodes.map fun item => match item with
          | .expression current => if current.id == id then .expression {current with
              form := .tuple ids, type := TypeSystem.Ty.productMany (List.replicate count childNode.type), requirements := [], coercions := []} else item
          | _ => item})
      else pure [original]
    for source in variants do
      require (source.owner == original.owner && source.inputs == original.inputs && source.roots == original.roots)
        "tuple retained source fields changed"
      let root ← match source.lookupExpression? id with | some root => pure root | none => throw (IO.userError "tuple root absent")
      let ids ← match root.form with | .tuple ids => pure ids | _ => throw (IO.userError "tuple root form changed")
      require (root.requirements.isEmpty && root.coercions.isEmpty) "tuple parent not ordinary"
      for item in source.nodes do
        match item with
        | .expression current =>
          match current.form with
          | .integerLiteral literal resolution =>
            let _ ← get "tuple actual Selected full row" (SourceCoreElaboration.validateWordIntegerLiteral selected.function.solvedRequirements current literal resolution)
            require (current.requirements == [resolution.requirement]) "tuple numeric ownership changed"
          | .reference _ (.local _) =>
            let _ ← get "tuple actual ordinary read" (SourceCoreCompatibleDataExpressions.lowerRead 100 values source scope current.id (reasonAt current.id))
          | .tuple .. | .unary .. | .binary .. =>
            require (current.requirements.isEmpty && current.coercions.isEmpty) "tuple primitive parent metadata changed"
          | _ => pure ()
        | _ => pure ()
      let ledger := selected.function.solvedRequirements
      let rows ← match ledger with
        | [] => throw (IO.userError "tuple full ledger unexpectedly empty")
        | first :: _ =>
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          pure [ledger, extra :: ledger, ledger ++ [extra]]
      let compilation : SourceCoreFunctions.Context := {
        plan := compiled.indexed.base.plan, owner := named.signature.key, globals := compiled.indexed.base.globals,
        administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
      let lower := fun fuel compilation child => SourceCoreFunctions.lowerExpressionWithPolicy policy noBody fuel compilation source scope child reasonAt
      let base ← get "actual tuple root" (lower 100 compilation id)
      let originalChildren ← ids.mapM fun child => get "actual ordered tuple child" (lower 99 compilation child)
      require (base == SourceCoreCalls.packArguments originalChildren && originalChildren.length == ids.length)
        "tuple actual pack/minfuel/code/order changed"
      for complete in rows do
        let lowered ← get "tuple full unused ledger" (lower 100 {compilation with solvedRequirements := complete} id)
        require (lowered == base) "tuple full unused ledger changed code"
        let expected ← if name == "firstFault" || name == "laterFault" then do
          let missingName := if name == "firstFault" then "first" else "second"
          let missing ← match source.nodes.filterMap (fun item => match item with
              | .expression current => match current.form with
                | .reference binderName (.local _) => if binderName == missingName then some current.id else none
                | _ => none
              | _ => none) with
            | [missing] => pure missing | _ => throw (IO.userError "actual tuple missing occurrence changed")
          pure (Core.Value.inLeft lowered.type (.word (reasonAt missing)))
          else do
            let payload := if name == "empty" then Core.Value.unit
              else if name == "single" then if ids.length == 1 then w 7 else .pair (w 7) (.pair (w 7) (w 7))
              else if name == "pair" then .pair (w 14) (.word (Word.ofNatModulo 5).bitNot)
              else if name == "triple" then .pair (w 14) (.pair (.bool true) (.word (Word.ofNatModulo 5).bitNot))
              else .pair (.pair (w 11) (.pair (.bool true) (w 3))) (.pair (w 5) (.bool false))
            pure (.inRight .word payload)
        for fuel in [0, 1, 17, 300000] do
          let result ← finish lowered.expression native store fuel
          require (result == (expected, store)) "tuple result/first fault/full captured store/resume changed"
      lengths := lengths ++ [ids.length]
      cases := cases + 1
  require (cases == 8 && lengths == [0, 1, 3, 2, 3, 3, 3, 3]) s!"tuple native scope changed {cases}/{lengths}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "native staged tuples" content
    ["empty", "single", "pair", "triple", "nested", "firstFault", "laterFault"]
  inspect compiled
  IO.println "staged native tuples: actual ordered code/0-1-2-3/nested/duplicate/full Selected rows/unused ledger/first-later fault/full captured heap/resume GREEN"

end Tests.SourceCoreRecursiveStageTupleMeaning
