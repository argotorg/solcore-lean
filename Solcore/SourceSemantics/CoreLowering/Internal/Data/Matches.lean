import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Data.HeapsAndBindings
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopLayouts
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming

/-!
# Data: matches

Certificates and decisions of data matches, their allocation, branch prefixes and Source scopes.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
/-! Static certificates for the actual general match compiler. Expression and
body certificates are supplied by the caller's structural compiler proof; the
extraction assumptions mention only successful compilation, never evaluation.
The hidden scrutinee occurs in the Core scope. It is not a source lexical binder;
a later heap/environment correspondence must retain that distinction. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
open Frontend Frontend.SourceInference SourceCoreDataMatches

abbrev ExpressionCertificate := Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev BodyCertificate := Scope → List StatementId → Core.Expr → Prop

def armScope (scope : Scope) (pattern : Pattern) : Scope :=
  pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope

inductive Arms (compilation : SourceCoreDataMatches.Context) (source : TypedSource) (site : StatementId)
    (scope : Scope) (expected : TypeSystem.Ty) (bodyCertificate : BodyCertificate) :
    List TypedMatchCase → List (Pattern × Core.Expr) → Prop where
  | nil : Arms compilation source site scope expected bodyCertificate [] []
  | cons {arm rest pattern body arms}
      (patternCertificate : DataPatternCertificates.Certificate compilation source scope site
        arm.span expected arm.pattern pattern)
      (typed : Core.HasType [] pattern.matcher pattern.functionType compilation.checked.catalog.definitions)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body)
      (tail : Arms compilation source site scope expected bodyCertificate rest arms) :
      Arms compilation source site scope expected bodyCertificate (arm :: rest) ((pattern, body) :: arms)

inductive Fallback (bodyCertificate : BodyCertificate) (scope : Scope) (resultType : Core.Ty) :
    Option (List StatementId) → Core.Expr → Prop where
  | none : Fallback bodyCertificate scope resultType none (Core.LocalLoop.fallthrough resultType)
  | some {statements body} (certificate : bodyCertificate scope statements body) :
      Fallback bodyCertificate scope resultType (some statements) body

/-- This constructor records the exact emitted layout, including both the
hidden cell reference and the loaded scrutinee temporary. -/
inductive Certificate (compilation : SourceCoreDataMatches.Context) (source : TypedSource) (scope : Scope)
    (id : StatementId) (resolution : MatchResolution) (resultType : Core.Ty)
    (internalReason : Core.Word) (expressionCertificate : ExpressionCertificate)
    (bodyCertificate : BodyCertificate) : Core.Expr → Prop where
  | matchWith {node statementType scrutineeNode type scrutinee arms fallback}
      (read : SourceCoreGeneralTypes.readStatement compilation.checked source id = .ok (node, statementType))
      (statementTypeValid : statementType = .unit ∨ statementType = resultType)
      (form : node.form = .matchWith resolution)
      (requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements))
      (hiddenOwned : resolution.hiddenScrutinee.owner = source.owner)
      (hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) = false)
      (scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (projection : projected compilation source scrutineeNode.type = .ok type)
      (expression : expressionCertificate scope resolution.scrutinee scrutinee)
      (sameType : type = scrutinee.type)
      (armCertificates : Arms compilation source id ((resolution.hiddenScrutinee, type) :: scope)
        scrutineeNode.type bodyCertificate resolution.cases arms)
      (fallbackCertificate : Fallback bodyCertificate ((resolution.hiddenScrutinee, type) :: scope)
        resultType resolution.defaultBody fallback) :
      Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) type scrutinee.expression
          (.caseE (.loadCell (.var 0))
            (Core.LanguageResult.failure (Core.LocalLoop.controlType resultType) (.word internalReason))
            (arms.foldr (fun (pattern, body) next => attempt pattern (Core.LocalLoop.controlType resultType) body next)
              (fallback.weakenAt 0))))

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem arms_of_mapM {compilation : SourceCoreDataMatches.Context} {source : TypedSource} {site : StatementId}
    {scope : Scope} {expected : TypeSystem.Ty} {bodyCertificate : BodyCertificate}
    {lowerBody : BodyLowerer} {fuel : Nat} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word}
    (bodyExtract : ∀ scope statements code,
      lowerBody fuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    {cases : List TypedMatchCase} {arms : List (Pattern × Core.Expr)}
    (accepted : cases.mapM (fun arm => do
      let pattern ← compilePattern compilation fuel source scope site arm.span expected arm.pattern
      let body ← lowerBody fuel source (armScope scope pattern.pattern) arm.body resultType reasonAt internalReason
      pure (pattern.pattern, body)) = .ok arms) :
    Arms compilation source site scope expected bodyCertificate cases arms := by
  induction cases generalizing arms with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    exact .nil
  | cons arm rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, acceptedHead, accepted⟩ := bind_ok accepted
    obtain ⟨tail, acceptedTail, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst arms
    obtain ⟨pattern, compiled, acceptedHead⟩ := bind_ok acceptedHead
    obtain ⟨body, bodyAccepted, acceptedHead⟩ := bind_ok acceptedHead
    simp only [pure, Except.pure, Except.ok.injEq] at acceptedHead
    subst head
    exact .cons (DataPatternCertificates.certificate_of_compilePattern _ _ _ _ _ _ _ _ _ compiled)
      pattern.typed (bodyExtract _ _ _ bodyAccepted) (ih acceptedTail)

/-- The actual compiler's success supplies all match metadata and pattern
certificates. Callback extraction is static and uses the exact child budget and
scope; it can be discharged by an enclosing compiler's structural induction. -/
theorem certificate_of_lowerWithReasons
    {compilation : SourceCoreDataMatches.Context} {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {resolution : MatchResolution} {resultType : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {internalReason : Core.Word} {code : Core.Expr}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate}
    (expressionExtract : ∀ childFuel scope id result,
      lowerExpression childFuel source scope id reasonAt = .ok result → expressionCertificate scope id result)
    (bodyExtract : ∀ childFuel scope statements code,
      lowerBody childFuel source scope statements resultType reasonAt internalReason = .ok code →
      bodyCertificate scope statements code)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      resultType reasonAt internalReason = .ok code) :
    Certificate compilation source scope id resolution resultType internalReason expressionCertificate bodyCertificate code := by
  cases fuel with
  | zero => simp [lowerWithReasons] at accepted
  | succ fuel =>
    simp only [lowerWithReasons] at accepted
    obtain ⟨⟨node, statementType⟩, read, accepted⟩ := bind_ok accepted
    by_cases allowed : statementType = .unit ∨ statementType = resultType
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at accepted
      simp only [allowed, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      by_cases form : node.form = .matchWith resolution
      · simp only [form, ↓reduceIte] at accepted
        by_cases requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)
        · simp only [requirements, ↓reduceIte] at accepted
          by_cases hiddenOwned : resolution.hiddenScrutinee.owner = source.owner
          · simp only [hiddenOwned, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
            cases hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) with
            | true => simp [hiddenFresh] at accepted
            | false =>
              simp only [hiddenFresh, Bool.false_eq_true, ↓reduceIte] at accepted
              by_cases scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner
              · simp only [scrutineeOwned, not_true_eq_false, ↓reduceIte] at accepted
                cases scrutineeFound : source.lookupExpression? resolution.scrutinee with
                | none => simp [scrutineeFound] at accepted
                | some scrutineeNode =>
                  simp only [scrutineeFound] at accepted
                  obtain ⟨type, projection, accepted⟩ := bind_ok accepted
                  obtain ⟨scrutinee, loweredExpression, accepted⟩ := bind_ok accepted
                  obtain ⟨checked, typeAccepted, accepted⟩ := bind_ok accepted
                  have sameType : type = scrutinee.type := by
                    unfold SourceCoreBasic.ensureType at typeAccepted
                    split at typeAccepted
                    · assumption
                    · cases typeAccepted
                  obtain ⟨arms, compiledArms, accepted⟩ := bind_ok accepted
                  have armCertificates := arms_of_mapM (bodyExtract fuel) compiledArms
                  cases fallbackForm : resolution.defaultBody with
                  | none =>
                    simp only [fallbackForm, Except.ok.injEq] at accepted
                    subst code
                    exact Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
                      scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression)
                      sameType armCertificates (by rw [fallbackForm]; exact .none)
                  | some statements =>
                    simp only [fallbackForm] at accepted
                    cases compiledFallback : lowerBody fuel source ((resolution.hiddenScrutinee, type) :: scope)
                        statements resultType reasonAt internalReason with
                    | error error => simp only [compiledFallback] at accepted; cases accepted
                    | ok fallback =>
                      simp only [compiledFallback, Except.ok.injEq] at accepted
                      subst code
                      exact Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
                        scrutineeOwned scrutineeFound projection (expressionExtract _ _ _ _ loweredExpression)
                        sameType armCertificates (by rw [fallbackForm]; exact .some (bodyExtract _ _ _ _ compiledFallback))
              · simp [scrutineeOwned] at accepted
          · simp [hiddenOwned] at accepted
        · simp [requirements] at accepted
      · simp [form] at accepted
    · simp [allowed, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchDecision
/-! Ordered arm selection from the actual match compiler's static certificate.
Every tested matcher has an independent source match/non-match and a finite,
store-preserving Core execution. The selected binder bundle is authenticated at
its retained source declaration types. Nested statement execution and binder
allocation are subsequent consumers of this decision certificate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchDecision
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternCertificates DataPatternValues DataPatternLeaves
open DataPatternExecution DataPatternSuccess DataPatternTypedValues DataPatternDecision DataEquality
open DataMatchCertificates

/-- Both alternatives expose the generated matcher's exact pure execution.
No source matching judgment is supplied to the theorem. -/
theorem pattern_decides {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : DataPatternCertificates.Certificate compilation source scope site span expected pattern compiled)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value) :
    (∃ bindings values, Dynamic.PatternMatches context pattern sourceValue bindings ∧
      DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures compiled.bindings bindings values ∧
      MatcherRuns compiled value values) ∨
    (Dynamic.PatternDoesNotMatch context pattern sourceValue ∧ MatcherFails compiled value) := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, instructionsEq, sourceRep⟩ := rootInstructions_sound compilation context valid.signatures _ _ _ root
  cases Tree.decides valid tree sourceValue value represented with
  | inl success =>
    obtain ⟨bindings, values, matched, bindingRep, executes⟩ := success
    subst instructions
    have sourceMatch : Dynamic.PatternMatches context pattern sourceValue bindings := .intro sourceRep matched
    exact .inl ⟨bindings, values, sourceMatch,
      DataPatternBindings.Certificate.bindings_typed certificate valid.signatures represented sourceMatch bindingRep,
      executes⟩
  | inr failed =>
    refine .inr ⟨.intro sourceRep ?_, failed⟩
    subst instructions
    refine ⟨DataPatternCertificates.Tree.skips tree, ?_⟩
    intro bindings matched
    obtain ⟨values, _, _, executes⟩ := DataPatternSuccess.Tree.success tree sourceValue value bindings []
      (TypedValueRep.erase represented) matched
    have impossible := (evaluation_deterministic (failed [value] [] (.var 0) (.var rfl))
      (executes [value] [] (.var 0) (.var rfl))).1
    cases impossible

/-- The first matching arm wins. The default carries its own static body
certificate, and no-branch has precisely the compiler's fallthrough code. -/
inductive Decision (compilation : Compilation) (context : SourceSemantics.Context)
    (scope : Scope) (bodyCertificate : BodyCertificate) (resultType : Ty)
    (sourceValue : Dynamic.Value) (value : Value) :
    List TypedMatchCase → List (Pattern × Expr) → Option (List StatementId) → Expr →
      Dynamic.MatchCaseSelection → Prop where
  | head {arm rest pattern body arms fallback fallbackCode bindings values}
      (matched : Dynamic.PatternMatches context arm.pattern sourceValue bindings)
      (bindingsRepresented : DataPatternBindings.BindingsRep compilation.checked.catalog compilation.signatures
        pattern.bindings bindings values)
      (runs : MatcherRuns pattern value values)
      (bodyCertified : bodyCertificate (armScope scope pattern) arm.body body) :
      Decision compilation context scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode (.arm arm.body bindings)
  | tail {arm rest pattern body arms fallback fallbackCode selection}
      (notMatched : Dynamic.PatternDoesNotMatch context arm.pattern sourceValue)
      (fails : MatcherFails pattern value)
      (next : Decision compilation context scope bodyCertificate resultType sourceValue value
        rest arms fallback fallbackCode selection) :
      Decision compilation context scope bodyCertificate resultType sourceValue value
        (arm :: rest) ((pattern, body) :: arms) fallback fallbackCode selection
  | default {statements code} (bodyCertified : bodyCertificate scope statements code) :
      Decision compilation context scope bodyCertificate resultType sourceValue value [] [] (some statements)
        code (.default statements)
  | noBranch :
      Decision compilation context scope bodyCertificate resultType sourceValue value [] [] none
        (LocalLoop.fallthrough resultType) .noBranch

theorem Decision.source {compilation : Compilation} {context : SourceSemantics.Context}
    {scope : Scope} {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection) :
    Dynamic.MatchCasesSelect context sourceValue cases fallback selection := by
  induction decision with
  | head matched => exact .head matched
  | tail notMatched _ _ ih => exact .tail notMatched ih
  | default => exact .default
  | noBranch => exact .noBranch

/-- The source arm selection and each pure matcher execution are consequences
of the actual compiler certificates, source evidence validity, and represented
input. Child statement evaluation is not assumed or concluded here. -/
theorem Arms.decides {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {resultType : Ty} {fallback : Option (List StatementId)} {fallbackCode : Expr}
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    (fallbackCertificate : Fallback bodyCertificate scope resultType fallback fallbackCode)
    (valid : ContextValid compilation context) {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures expected sourceValue value) :
    ∃ selection, Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection := by
  induction certificates with
  | nil =>
    cases fallbackCertificate with
    | none => exact ⟨_, .noBranch⟩
    | some certified => exact ⟨_, .default certified⟩
  | cons certificate typed bodyCertified tail ih =>
    cases pattern_decides certificate valid represented with
    | inl matched =>
      obtain ⟨bindings, values, matched, representedBindings, runs⟩ := matched
      exact ⟨_, .head matched representedBindings runs bodyCertified⟩
    | inr failed =>
      obtain ⟨selection, next⟩ := ih
      exact ⟨selection, .tail failed.1 failed.2 next⟩
/-- A certified whole match always has an independent ordered source arm
selection for a represented scrutinee. Execution of that arm is a separate
statement correspondence obligation. -/
theorem Certificate.source_selects {compilation : Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : DataMatchCertificates.Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (valid : ContextValid compilation context) {node : ExpressionNode}
    (found : source.lookupExpression? resolution.scrutinee = some node)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep compilation.checked.catalog compilation.signatures node.type sourceValue value) :
    ∃ selection, Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection expression sameType arms fallback =>
    have same := Option.some.inj (found.symm.trans scrutineeFound)
    subst node
    obtain ⟨selection, decision⟩ := Arms.decides arms fallback valid represented
    exact ⟨selection, decision.source⟩

end Solcore.SourceSemantics.CoreLowering.DataMatchDecision
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
/-! Source-ordered allocation of authenticated match binders into the new data
heap/environment relation. This allocation theorem constructs the independent
source BindersAllocate derivation. It does not assume execution of a selected
arm or claim that the entire generated match statement is already preserved. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternBindings

/-- The compiled binder order is exactly the independently matched binder
order, including retained binder metadata. -/
theorem BindingsRep.binders {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values) :
    bindings.map Prod.fst = sources.map Prod.fst := by
  induction represented with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg (List.cons _) ih

/-- Bindings allocate in source order, while lexical environments put each new
reference at the front. Source/Core locations use their independent heap/store
lengths; existing administrative code remains unchanged throughout. -/
theorem BindingsRep.allocate {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    {heap : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store) :
    ∃ finalEnvironment finalHeap finalCanonical finalStore finalMap finalWorld,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  induction represented generalizing mapping world scope environment canonical heap store with
  | nil =>
    exact ⟨environment, heap, canonical, store, mapping, world, .nil _ _, environments, heaps,
      .refl _, .refl _, .refl _ _⟩
  | @cons binder type sourceValue value bindings sources values projection head tail ih =>
    obtain ⟨nextEnvironment, nextHeaps⟩ := environments.bind heaps (.initialized projection head)
      (Dynamic.Heap.Allocates.append (type := binder.scheme.body) (value := some sourceValue))
    obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalStore, finalMap, finalWorld,
      allocated, finalEnvironmentRep, finalHeapRep, moreMaps, moreWorlds, moreFrame⟩ :=
      ih nextEnvironment nextHeaps
    exact ⟨finalEnvironment, finalHeap, finalCanonical, finalStore, finalMap, finalWorld,
      .cons .append allocated, finalEnvironmentRep, finalHeapRep,
      (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans moreMaps,
      (show WorldExtends world (world ++ [OptionalCell.cellType type]) from ⟨_, rfl⟩).trans moreWorlds,
      (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans moreFrame⟩

end Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchCoreAllocation
/-! Exact continuation correspondence for the binder-allocation prefix emitted
by bindArm. The proof constructs source allocation and follows the actual Core
let/case temporaries. The continuation is arbitrary: no exact closure-renaming
or first-order-store theorem is assumed for the selected arm's body. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchCoreAllocation
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternBindings DataPatternValues DataEquality CoreProof
open ReadOnly

def liftMany : Nat → Renaming → Renaming
  | 0, embedding => embedding
  | count + 1, embedding => liftMany count embedding.lift

/-- A proof-facing name for the existing fold, with a starting index so its
structural induction also covers the suffix after an allocated binder. -/
def allocationCode (bindings : List (TypedBinder × Ty)) (start : Nat) (types : List Ty)
    (outputType : Ty) (tail : Expr) : Expr :=
  (bindings.zipIdx start).foldr (fun (binding, index) continuation =>
    LocalSequence.letInitialized outputType binding.2
      (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index))) continuation) tail

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var lookup => exact .var (agrees lookup)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index foundValue found
  exact agrees found

/-- Both directions of the generated allocation prefix reach the same related
heap and continuation. The continuation's execution is not a premise: wrap and
unwrap quantify over every finite continuation evaluation. -/
theorem BindingsRep.prefix {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {κ ξ : Renaming}
    {start : Nat} {allTypes : List Ty} {allValues : List Value} {outputType : Ty} {tail : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store)
    (sourceLayout : EnvironmentsAgree κ canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (packValues allValues))
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (liftMany bindings.length κ) finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      ContinuationAgreement actual store ((allocationCode bindings start allTypes outputType tail).rename ξ)
        finalActual finalStore (tail.rename finalEmbedding) := by
  induction represented generalizing mapping world scope environment canonical logical actual heap store κ ξ start with
  | nil =>
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, .refl _ _ _⟩
  | @cons binder payload sourceValue value bindings sources values projection head rest ih =>
    have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
    have projectionPath := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
    have initializer : Evaluates actual store
        ((LanguageResult.success (SourceCoreDataExpressions.projectPacked start allTypes (.var start))).rename ξ)
        (.inRight .word value) store := .inRight ((selects_rename projectionPath actualLayout).evaluates store)
    let reference := Value.cellRef (OptionalCell.cellType payload) store.length
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind (id := binder.id) heaps (.initialized projection head)
      (Dynamic.Heap.Allocates.append (type := binder.scheme.body) (value := some sourceValue))
    have nextSourceLayout : EnvironmentsAgree κ.lift (reference :: canonical) (reference :: logical) := sourceLayout.lift reference
    have insertedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) :=
      agree_insert actualLayout value
    have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
        (reference :: logical) (reference :: value :: actual) := insertedLayout.lift reference
    have nextSelected : ∀ {index selectedValue}, values[index]? = some selectedValue →
        allValues[(start + 1) + index]? = some selectedValue := by
      intro index selectedValue found
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
    obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
      finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
      finalSourceLayout, finalActualLayout, agreement⟩ :=
      ih nextEnvironments nextHeaps nextSourceLayout nextActualLayout
        (show (reference :: logical)[start + 1]? = some (packValues allValues) from bundleSlot) nextSelected
    refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnv, finalHeapRep,
      (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
      finalSourceLayout, finalActualLayout, ?_⟩
    have allocation : Evaluates (value :: actual) store (OptionalCell.allocateInitialized payload (.var 0))
        reference (store ++ [.inRight .unit value]) := OptionalCell.allocateInitialized_evaluates (.var rfl)
    simp only [LoopStatements.rename_insert_lift] at agreement
    simp only [allocationCode, List.zipIdx_cons, List.foldr_cons, LoopRenaming.letInitialized]
    apply ContinuationAgreement.trans ?_ agreement
    exact (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE allocation)
private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is exactly the successful branch emitted by `attempt`, including its
two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem bindArm_prefix {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {scrutinee : Value} {outputType : Ty} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((bindArm bindings outputType (body.weakenAt bindings.length)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using DataPatternExecution.BindingsRep.length represented.erase
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, agreement⟩ :=
    BindingsRep.prefix represented (tail := (body.weakenAt bindings.length).weakenAt bindings.length)
      environments heaps sourceLayout actualLayout (start := 0) rfl length
      (fun {_ _} found => by simpa using found)
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, ?_⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement

end Solcore.SourceSemantics.CoreLowering.DataMatchCoreAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix
/-! The emitted ordered match branches reach exactly the selected arm/default
continuation, allocating only the successful arm's binders. This is a complete
prefix correspondence (wrap and unwrap), not a supplied child evaluation. The
selected body's own statement correspondence is a separate structural proof. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution
open DataMatchCertificates DataMatchDecision CoreProof ReadOnly

/-- Source-side state and syntax exposed at the selected continuation. Internal
Core scopes remain explicit; source environments contain only real binders. -/
inductive SelectedBody (bodyCertificate : BodyCertificate) (scope : Scope)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (resultType : Ty) :
    Dynamic.MatchCaseSelection → Scope → Dynamic.Environment → Dynamic.Heap → Expr → Prop where
  | arm {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
      {compiledBindings : List (TypedBinder × Ty)} {finalEnvironment finalHeap body}
      (binders : compiledBindings.map Prod.fst = bindings.map Prod.fst)
      (allocated : Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) (bindings.map Prod.snd)
        finalEnvironment finalHeap)
      (certified : bodyCertificate
        (compiledBindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) statements body) :
      SelectedBody bodyCertificate scope environment heap resultType (.arm statements bindings)
        (compiledBindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalHeap body
  | default {statements body} (certified : bodyCertificate scope statements body) :
      SelectedBody bodyCertificate scope environment heap resultType (.default statements)
        scope environment heap body
  | noBranch : SelectedBody bodyCertificate scope environment heap resultType .noBranch
      scope environment heap (LocalLoop.fallthrough resultType)

private theorem case_right {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  constructor
  · intro result finalStore body; exact .caseRight evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_right evaluated
    exact body.sound

private theorem case_left {environment : Environment} {before middle : Store}
    {scrutinee left right : Expr} {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationAgreement environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  constructor
  · intro result finalStore body; exact .caseLeft evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.case_left evaluated
    exact body.sound

/-- The entire attempted-arm fold has no other finite result than execution
of its selected, related continuation. The initial store may contain arbitrary
typed administrative functions, and the body itself is unrestricted syntax. -/
theorem Decision.prefix {compilation : DataPatternCertificates.Compilation} {context : SourceSemantics.Context}
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {resultType : Ty}
    {sourceValue : Dynamic.Value} {value : Value} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    {fallback : Option (List StatementId)} {fallbackCode : Expr} {selection : Dynamic.MatchCaseSelection}
    (decision : Decision compilation context scope bodyCertificate resultType sourceValue value
      cases arms fallback fallbackCode selection)
    (certificates : Arms compilation source site scope expected bodyCertificate cases arms)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents compilation.checked.catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents compilation.checked.catalog compilation.signatures mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (value :: canonical) actual) :
    ∃ finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding body,
      SelectedBody bodyCertificate scope environment heap resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents compilation.checked.catalog finalMap finalWorld administrativeContext
        finalScope finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents compilation.checked.catalog compilation.signatures finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((arms.foldr (fun (pattern, body) next => attempt pattern (LocalLoop.controlType resultType) body next)
          (fallbackCode.weakenAt 0)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  induction decision generalizing actual ξ with
  | @head arm rest pattern body arms fallback fallbackCode bindings values matched bindingsRepresented runs certified =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have matchedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inRight .unit (packValues values)) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact runs actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        DataMatchCoreAllocation.bindArm_prefix bindingsRepresented environments heaps (actualLayout.lift (packValues values))
      exact ⟨_, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, .arm (DataMatchAllocation.BindingsRep.binders bindingsRepresented) allocated certified,
        finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, (case_right matchedCore).trans agreement⟩
  | @tail arm rest pattern body arms fallback fallbackCode selection notMatched fails next ih =>
    cases certificates with
    | cons certificate matcherTyped bodyCertified tail =>
      have failedCore : Evaluates actual store ((Expr.apply pattern.matcher (.var 0)).rename ξ)
          (.inLeft (bundleType pattern.bindingTypes) .unit) store := by
        rw [Expr.rename, closed_rename matcherTyped ξ]
        exact fails actual store (.var (ξ 0)) (.var (actualLayout (index := 0) rfl))
      have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ)
          (value :: canonical) (.unit :: actual) := by
        intro index foundValue found
        exact actualLayout found
      obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, agreement⟩ :=
        ih tail nextLayout
      refine ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
        finalEmbedding, body, choice, finalEnv, finalHeapRep, maps, worlds, frame, finalLayout, ?_⟩
      simp only [LoopStatements.rename_insert] at agreement
      simp only [List.foldr_cons, attempt, Expr.rename, LoopRenaming.weakenZero]
      exact (case_left failedCore).trans agreement
  | default certified =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .default certified, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _
  | noBranch =>
    refine ⟨scope, environment, heap, canonical, actual, store, mapping, world,
      Renaming.comp ξ (Renaming.insertion 0), _, .noBranch, environments, heaps,
      .refl _, .refl _, .refl _ _, ?_, ?_⟩
    · intro index foundValue found
      exact actualLayout (index := index + 1) found
    · simp only [List.foldr_nil, ← Expr.rename_insertion, Expr.rename_comp]
      exact .refl _ _ _

end Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
/-! The lexical context of a selected arm comes from independent source static
pattern/body typing. Binder identities can be recovered without assuming source
value typing or a source body execution. The hidden Core local is never added
to this declarative context. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
open Frontend Frontend.SourceInference

private theorem instruction_binders {context : Context}
    {instructions rest : List MatchPatternInstruction} {type : TypeSystem.Ty}
    {requirements : List RequirementId} {binders : List TypedBinder}
    (typed : PatternInstructionHasType context instructions type requirements binders rest) :
    ∀ {value bindings sourceRest}, Dynamic.PatternInstructionMatches context value instructions bindings sourceRest →
      sourceRest = rest ∧ bindings.map Prod.fst = binders := by
  induction typed using PatternInstructionHasType.rec
    (motive_2 := fun instructions types _ binders rest _ =>
      ∀ {values bindings sourceRest}, values.length = types.length →
        Dynamic.PatternInstructionsMatch context values instructions bindings sourceRest →
        sourceRest = rest ∧ bindings.map Prod.fst = binders) with
  | wildcard => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | integerLiteral => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | binder => intro value bindings sourceRest matched; cases matched; exact ⟨rfl, rfl⟩
  | constructor valid arity typed ih =>
    intro value bindings sourceRest matched
    cases matched with
    | constructor agreement length children => exact ih (length.trans arity) children
  | tuple arity typed ih =>
    intro value bindings sourceRest matched
    cases matched with
    | tuple packed length children => exact ih (length.trans arity) children
  | nil =>
    rename_i values bindings sourceRest length matched
    have empty : values = [] := by simpa using length
    subst values
    cases matched
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i values bindings sourceRest length matched
    cases values with
    | nil => simp at length
    | cons value values =>
      cases matched with
      | cons first rest =>
        obtain ⟨same, firstBinders⟩ := headIH first
        subst same
        obtain ⟨same, restBinders⟩ := tailIH (Nat.succ.inj length) rest
        exact ⟨same, by simp [List.map_append, firstBinders, restBinders]⟩

theorem PatternMatches.binders {context : Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    {value : Dynamic.Value} {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : TypedMatchPatternHasType context pattern type binders arity)
    (matched : Dynamic.PatternMatches context pattern value bindings) : bindings.map Prod.fst = binders := by
  cases matched with
  | intro source instruction =>
    have same := Dynamic.MatchPatternSourceRepresents.rootArity_eq typed.source_represents source
    subst same
    exact (instruction_binders typed.resolution_type instruction).2

/-- Static source typing supplies the selected body's actual source context.
This is a source-static premise, not a lowering certificate or a body runtime
premise. It can be obtained from declaratively typed function statements. -/
theorem MatchCasesSelect.arm_scope
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase} {caseFacts : List BodyFacts}
    {fallback : Option (List StatementId)} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : MatchCasesHaveType source control context scrutineeType cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    ∃ armContext finalContext facts,
      BindersExtend source.owner context (bindings.map Prod.fst) armContext ∧
      StatementsHaveType source control armContext body finalContext facts ∧ facts ∈ caseFacts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        exact ⟨_, _, _, PatternMatches.binders patternTyped matched ▸ extended, bodyTyped, by simp⟩
  | tail notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨armContext, finalContext, facts, extended, bodyTyped, member⟩ := arm_scope tail selected
      exact ⟨armContext, finalContext, facts, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length
decreasing_by simp_all

end Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes
end
