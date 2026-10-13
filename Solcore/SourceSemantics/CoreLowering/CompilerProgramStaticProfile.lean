import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyProfile
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! Executable finite checks inspect every actual cache row and every original
lambda. They retain raw forms, edges, metadata, target ranges and evidence.
The accepted compiler actions supply body and expression proofs separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedOrdinarySyntaxTable (Table)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)
open CallableIndexedOwnedPreparedScopedMethodAdmission (Excluded)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

def LambdaAllowed (allowed : Option ExpressionNode) : Node → Prop
  | .statement _ => True
  | .expression node => match node.form with
    | .lambda _ _ _ => allowed = some node
    | _ => True

def lambdas? (source : TypedSource) (allowed : Option ExpressionNode) :
    Option (PLift (∀ node ∈ source.nodes, LambdaAllowed allowed node)) :=
  allProof? (LambdaAllowed allowed) (fun node => by
    cases node with
    | statement statement => exact some ⟨True.intro⟩
    | expression expression =>
      cases form : expression.form
      case lambda parameters result body =>
        exact if same : allowed = some expression then
          some ⟨by simpa only [LambdaAllowed, form] using same⟩ else none
      all_goals exact some ⟨by simp only [LambdaAllowed, form]⟩) source.nodes

abbrev ExpressionProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) := AcceptedCompilerExpressionProfile.Profile compiled.indexed named
      named.specialized.function.typedBody rows directOnly

structure Scoped (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) where
  expressions : ExpressionProfile compiled named rows directOnly
  body : AcceptedCompilerBodyProfile.Profile named.specialized.function.typedBody expressions.Reached
  returns : AcceptedCompilerBodyProfile.HasReturn named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)
  lambdas : ∀ node ∈ named.specialized.function.typedBody.nodes, LambdaAllowed none node

def scoped? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) : Option (Scoped compiled named rows directOnly) := do
  let expressions ← AcceptedCompilerExpressionProfile.certify compiled.indexed named
    named.specialized.function.typedBody rows directOnly
  let ⟨body⟩ ← AcceptedCompilerBodyProfile.validate named.specialized.function.typedBody expressions.Reached
  let ⟨returns⟩ ← AcceptedCompilerBodyProfile.hasReturn? named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)
  let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody none
  pure ⟨expressions, body, returns, lambdas⟩

/-- The factory lane records the original outer return and singleton inner
return. Every lambda in the complete original node table is accounted for. -/
structure Factory (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  expressions : ExpressionProfile compiled named rows true
  outer : StatementId
  rest : List StatementId
  outerNode : StatementNode
  expression : ExpressionId
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statement : StatementId
  returnNode : StatementNode
  inner : ExpressionId
  roots : statements named.specialized.function.typedBody = outer :: rest
  outerFound : named.specialized.function.typedBody.lookupStatement? outer = some outerNode
  outerForm : outerNode.form = .returnStmt (some expression)
  found : named.specialized.function.typedBody.lookupExpression? expression = some node
  form : node.form = .lambda parameters result [statement]
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  returnFound : named.specialized.function.typedBody.lookupStatement? statement = some returnNode
  returnForm : returnNode.form = .returnStmt (some inner)
  innerReached : expressions.Reached inner
  lambdas : ∀ actual ∈ named.specialized.function.typedBody.nodes, LambdaAllowed (some node) actual

def factory? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Factory compiled named rows) := do
  let expressions ← AcceptedCompilerExpressionProfile.certify compiled.indexed named
    named.specialized.function.typedBody rows true
  match roots : statements named.specialized.function.typedBody with
  | [] => none
  | outer :: rest =>
    match outerFound : named.specialized.function.typedBody.lookupStatement? outer with
    | none => none
    | some outerNode =>
      match outerForm : outerNode.form with
      | .returnStmt (some expression) =>
        match found : named.specialized.function.typedBody.lookupExpression? expression with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result [statement] =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                if ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
                    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                      binding.initializer = expression)) = none then
                  match returnFound : named.specialized.function.typedBody.lookupStatement? statement with
                  | none => none
                  | some returnNode =>
                    match returnForm : returnNode.form with
                    | .returnStmt (some inner) =>
                      if innerReached : expressions.Reached inner then do
                        let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody (some node)
                        pure ⟨expressions, outer, rest, outerNode, expression, node, parameters, result,
                          statement, returnNode, inner, roots, outerFound, outerForm, found, form,
                          requirements, coercions, ordinary, returnFound, returnForm, innerReached, lambdas⟩
                      else none
                    | _ => none
                else none
              else none
            else none
          | _ => none
      | _ => none

inductive Ordinary (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  | scoped (profile : Scoped compiled named rows false)
  | factory (profile : Factory compiled named rows)

def ordinary? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Ordinary compiled named rows) :=
  match scoped? compiled named rows false with
  | some profile => some (.scoped profile)
  | none => (factory? compiled named rows).map Ordinary.factory

def NoOrdinary (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  ∀ signature ∈ compiled.sourceProgram.signatures.functions, named.specialized.declaration ≠ signature.id

inductive Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  | ordinary (eligible : Eligible compiled named.specialized) (excluded : Excluded compiled named)
      (profile : Ordinary compiled named rows)
  | method (excluded : NoOrdinary compiled named)
      (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
        named.specialized.parameterSubstitution)
      (forms : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource
        named.specialized.function.typedBody)
      (profile : Scoped compiled named rows true)

def row? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named)
    (rows : List SourceSpecialization.SpecializedFunction) : Option (Row compiled named rows) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
    let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
    let ⟨forms⟩ ← CallableIndexedOwnedPreparedScopedMethodAdmission.directSource? named.specialized.function.typedBody
    let profile ← scoped? compiled named rows true
    pure (.method (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member))
      range forms profile)
  else
    let ⟨eligible⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.eligible? compiled wellFormed
      (max 1 compiled.indexed.fuel) named selected
    if excluded : (Program.ofChecked compiled.sourceProgram).methods.all (fun definition =>
        decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      let profile ← ordinary? compiled named rows
      pure (.ordinary eligible (fun definition member =>
        of_decide_eq_true (List.all_eq_true.mp excluded definition member)) profile)
    else none

structure StaticProfile (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : Table compiled
  catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled
  rows : ∀ index : Fin compiled.indexed.base.functions.length,
    Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows)
  callable : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

/-- The only traversal budgets bound original type formation. Body and
expression acceptance comes from the retained compiler receipts. -/
def validateProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Option (StaticProfile compiled) := do
  if callable : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed
        (max 1 compiled.indexed.fuel)
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun index : Fin compiled.indexed.base.functions.length =>
          Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows))
        (fun index => do
          let profile ← row? compiled wellFormed compiled.indexed.base.functions[index.val]
            (List.getElem?_eq_getElem index.isLt) table.rows
          pure ⟨⟨profile⟩⟩) (List.finRange compiled.indexed.base.functions.length)
      pure ⟨table, catalog, fun index => rows index (List.mem_finRange index), callable, diagnostics, present⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
