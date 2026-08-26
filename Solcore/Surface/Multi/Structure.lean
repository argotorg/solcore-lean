import Solcore.Surface.Multi.Diagnostic
import Solcore.Surface.Multi.Measure

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace Structure

/-- Convert the local nonempty-list carrier to an ordinary list. -/
def nonemptyToList {α : Type} (values : NonemptyList α) : List α :=
  values.head :: values.tail

/-- Emit one diagnostic for every occurrence whose key appeared earlier. -/
def duplicateDiagnostics {α κ : Type} [DecidableEq κ]
    (key : α → κ) (diagnostic : α → StructuralDiagnostic) :
    List α → List StructuralDiagnostic :=
  go []
where
  go (seen : List κ) : List α → List StructuralDiagnostic
    | [] => []
    | value :: rest =>
        let keyValue := key value
        let later := go (keyValue :: seen) rest
        if keyValue ∈ seen then diagnostic value :: later else later

/-- Strict source order used to select the least wildcard marker. -/
def sourceSpanBefore (left right : SourceSpan) : Bool :=
  match SourceId.compare left.source right.source with
  | .lt => true
  | .gt => false
  | .eq =>
      if left.startByte < right.startByte then true
      else if right.startByte < left.startByte then false
      else left.endByte < right.endByte

/-- Select the least span from a nonempty candidate suffix. -/
def leastSourceSpan? : List SourceSpan → Option SourceSpan
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun least candidate =>
        if sourceSpanBefore candidate least then candidate else least) first)

/-- Return the marker span when an import selector entry is a wildcard. -/
def importWildcardSpan? (entry : ImportSelectorEntry) : Option SourceSpan :=
  match entry.payload with
  | .wildcard marker => some marker.span
  | .named _ _ => none

private def exportWildcardSpan? (entry : ExportEntry) : Option SourceSpan :=
  match entry.payload with
  | .wildcard marker => some marker.span
  | .item _ | .allFrom _ _ => none

private def remoteExportWildcardSpan?
    (entry : RemoteExportEntry) : Option SourceSpan :=
  match entry.payload with
  | .wildcard marker => some marker.span
  | .item _ => none

/-- Emit the diagnostic for the least wildcard in a mixed selector list. -/
def mixedWildcardDiagnostic?
    (entryCount : Nat) (spans : List SourceSpan)
    (makeDiagnostic : SourceSpan → StructuralDiagnostic) :
    List StructuralDiagnostic :=
  if entryCount = 1 then []
  else
    match leastSourceSpan? spans with
    | none => []
    | some span => [makeDiagnostic span]

/-- Project named import entries to their source and effective local names. -/
def namedImportEntries
    (entries : List ImportSelectorEntry) :
    List (IdentifierOccurrence × IdentifierOccurrence) :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard _ => none
    | .named source alias => some (source, alias.getD source)

/-- Collect diagnostics local to an import selection. -/
def importSelectionDiagnostics
    (selection : ImportSelection) : List StructuralDiagnostic :=
  let entries := selection.payload.entries
  let named := namedImportEntries entries
  let empty :=
    if entries.isEmpty then
      [.emptyImportSelection selection.span]
    else
      []
  let mixed := mixedWildcardDiagnostic? entries.length
    (entries.filterMap importWildcardSpan?)
    StructuralDiagnostic.mixedImportWildcard
  let duplicateSources := duplicateDiagnostics
    (fun entry => entry.1.payload)
    (fun entry => .duplicateImportSourceName entry.1.span entry.1.payload)
    named
  let duplicateLocals := duplicateDiagnostics
    (fun entry => entry.2.payload)
    (fun entry => .duplicateImportLocalName entry.2.span entry.2.payload)
    named
  empty ++ mixed ++ duplicateSources ++ duplicateLocals

/-- Collect diagnostics local to an import hiding clause. -/
def hidingDiagnostics
    (clause : HidingClause) : List StructuralDiagnostic :=
  let empty :=
    if clause.payload.names.isEmpty then
      [.emptyHidingClause clause.span]
    else
      []
  let duplicates := duplicateDiagnostics
    (fun name => name.payload)
    (fun name => .duplicateHiddenName name.span name.payload)
    clause.payload.names
  empty ++ duplicates

/-- Collect every diagnostic local to one import declaration. -/
def importDiagnostics (declaration : ImportDecl) : List StructuralDiagnostic :=
  match declaration.payload.mode with
  | .module _ => []
  | .items selection hidingClause =>
      importSelectionDiagnostics selection ++
        match hidingClause with
        | none => []
        | some clause => hidingDiagnostics clause

private def constructorSelectionDiagnostics
    (selection : Option ConstructorSelection) : List StructuralDiagnostic :=
  match selection with
  | none => []
  | some located =>
      match located.payload with
      | .all _ => []
      | .named constructors =>
          duplicateDiagnostics
            (fun name => name.payload)
            (fun name => .duplicateExportConstructor name.span name.payload)
            (nonemptyToList constructors)

private def exportItemDiagnostics
    (item : ExportItem) : List StructuralDiagnostic :=
  constructorSelectionDiagnostics item.payload.constructors

private def localExportItems (entries : List ExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ | .allFrom _ _ => none

private def localExportReferences
    (entries : List ExportEntry) : List ModuleReference :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .allFrom reference _ => some reference
    | .wildcard _ | .item _ => none

private def localExportDiagnostics
    (selection : LocalExportList) : List StructuralDiagnostic :=
  let entries := selection.payload.entries
  let items := localExportItems entries
  let references := localExportReferences entries
  let empty :=
    if entries.isEmpty then [.emptyLocalExportList selection.span] else []
  let mixed := mixedWildcardDiagnostic? entries.length
    (entries.filterMap exportWildcardSpan?)
    StructuralDiagnostic.mixedExportWildcard
  let duplicateNames := duplicateDiagnostics
    (fun item => item.payload.name.payload)
    (fun item => .duplicateExportName
      item.payload.name.span item.payload.name.payload)
    items
  let duplicateReferences := duplicateDiagnostics
    ModuleReference.eraseLocations
    (fun reference => .duplicateExportModuleReference
      reference.span reference.eraseLocations)
    references
  empty ++ mixed ++ duplicateNames ++ duplicateReferences ++
    items.flatMap exportItemDiagnostics

private def remoteExportItems
    (entries : List RemoteExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ => none

private def remoteExportDiagnostics
    (selection : RemoteExportSelection) : List StructuralDiagnostic :=
  match selection.payload with
  | .dotWildcard _ => []
  | .braced entries =>
      let items := remoteExportItems entries
      let empty :=
        if entries.isEmpty then [.emptyRemoteExportList selection.span] else []
      let mixed := mixedWildcardDiagnostic? entries.length
        (entries.filterMap remoteExportWildcardSpan?)
        StructuralDiagnostic.mixedExportWildcard
      let duplicateNames := duplicateDiagnostics
        (fun item => item.payload.name.payload)
        (fun item => .duplicateExportName
          item.payload.name.span item.payload.name.payload)
        items
      empty ++ mixed ++ duplicateNames ++ items.flatMap exportItemDiagnostics

/-- Collect every diagnostic local to one export declaration. -/
def exportDiagnostics (declaration : ExportDecl) : List StructuralDiagnostic :=
  match declaration.payload with
  | .module _ _ => []
  | .local selection => localExportDiagnostics selection
  | .from _ selection => remoteExportDiagnostics selection

/-- Collect the empty-target and duplicate-target pragma diagnostics. -/
def pragmaDiagnostics (declaration : PragmaDecl) : List StructuralDiagnostic :=
  let empty :=
    if declaration.payload.kind.payload = .noGenericInstanceFor &&
        declaration.payload.targets.isEmpty then
      [.emptyGenericPragmaTargets declaration.payload.kind.span]
    else
      []
  let duplicates := duplicateDiagnostics
    (fun target => target.payload)
    (fun target => .duplicatePragmaTarget target.span target.payload)
    declaration.payload.targets
  empty ++ duplicates

private def missingParameterTypeDiagnostics
    (context : ParameterContext) (parameters : List Parameter) :
    List StructuralDiagnostic :=
  parameters.filterMap fun parameter =>
    match parameter.payload.type with
    | some _ => none
    | none => some (.requiredParameterTypeMissing parameter.payload.name.span context)

private def disallowedSignatureModifierDiagnostics
    (context : ModifierContext) (signature : FunctionSignature) :
    List StructuralDiagnostic :=
  let publicDiagnostic :=
    match signature.payload.public with
    | none => []
    | some marker =>
        [.modifierNotAllowed marker.span context marker.payload]
  let payableDiagnostic :=
    match signature.payload.payable with
    | none => []
    | some marker =>
        [.modifierNotAllowed marker.span context marker.payload]
  publicDiagnostic ++ payableDiagnostic

mutual

private def expressionDiagnosticsFuel : Nat → Expression →
    List StructuralDiagnostic
  | 0, _ => []
  | fuel + 1, expression =>
      match expression.payload with
      | .name _ | .proxy _ _ | .literal _ => []
      | .call callee arguments =>
          expressionDiagnosticsFuel fuel callee ++
            arguments.flatMap (expressionDiagnosticsFuel fuel)
      | .select receiver _ => expressionDiagnosticsFuel fuel receiver
      | .dotConstructor _ _ arguments =>
          match arguments with
          | none => []
          | some values => values.flatMap (expressionDiagnosticsFuel fuel)
      | .lambda _ _ body => bodyDiagnosticsFuel fuel 0 body
      | .annotation inner _ => expressionDiagnosticsFuel fuel inner
      | .keywordConditional condition thenBranch elseBranch
      | .ternaryConditional condition thenBranch elseBranch =>
          expressionDiagnosticsFuel fuel condition ++
            expressionDiagnosticsFuel fuel thenBranch ++
            expressionDiagnosticsFuel fuel elseBranch
      | .index receiver index =>
          expressionDiagnosticsFuel fuel receiver ++
            expressionDiagnosticsFuel fuel index
      | .prefix _ operand => expressionDiagnosticsFuel fuel operand
      | .infix _ left right =>
          expressionDiagnosticsFuel fuel left ++
            expressionDiagnosticsFuel fuel right
      | .tuple elements =>
          elements.flatMap (expressionDiagnosticsFuel fuel)
      | .group inner => expressionDiagnosticsFuel fuel inner

private def patternDiagnosticsFuel : Nat → Pattern → List StructuralDiagnostic
  | 0, _ => []
  | fuel + 1, pattern =>
      match pattern.payload with
      | .named _ arguments | .dotConstructor _ _ arguments =>
          match arguments with
          | none => []
          | some values =>
              (nonemptyToList values).flatMap (patternDiagnosticsFuel fuel)
      | .wildcard _ | .literal _ => []
      | .comptime _ expression => expressionDiagnosticsFuel fuel expression
      | .tuple elements => elements.flatMap (patternDiagnosticsFuel fuel)
      | .group inner => patternDiagnosticsFuel fuel inner

private def bodyDiagnosticsFuel : Nat → Nat → Body → List StructuralDiagnostic
  | 0, _, _ => []
  | fuel + 1, loopDepth, body =>
      body.payload.statements.flatMap
        (statementDiagnosticsFuel fuel loopDepth)

private def statementDiagnosticsFuel : Nat → Nat → Statement →
    List StructuralDiagnostic
  | 0, _, _ => []
  | fuel + 1, loopDepth, statement =>
      match statement.payload with
      | .assignment _ left right =>
          expressionDiagnosticsFuel fuel left ++
            expressionDiagnosticsFuel fuel right
      | .letBinding binding =>
          match binding.payload.initializer with
          | none => []
          | some expression => expressionDiagnosticsFuel fuel expression
      | .block body => bodyDiagnosticsFuel fuel loopDepth body
      | .expression expression _ =>
          expressionDiagnosticsFuel fuel expression
      | .return value _ =>
          match value with
          | none => []
          | some expression => expressionDiagnosticsFuel fuel expression
      | .match scrutinees arms _ =>
          let scrutineeList := nonemptyToList scrutinees
          let expected := scrutineeList.length
          scrutineeList.flatMap (expressionDiagnosticsFuel fuel) ++
            (nonemptyToList arms).flatMap fun arm =>
              let patterns := nonemptyToList arm.payload.patterns
              let mismatch :=
                if patterns.length = expected then []
                else [.matchPatternArityMismatch
                  arm.span expected patterns.length]
              mismatch ++ patterns.flatMap (patternDiagnosticsFuel fuel) ++
                bodyDiagnosticsFuel fuel loopDepth arm.payload.body
      | .assembly _ => []
      | .ifThenElse condition thenBody elseBody =>
          expressionDiagnosticsFuel fuel condition ++
            bodyDiagnosticsFuel fuel loopDepth thenBody ++
            match elseBody with
            | none => []
            | some body => bodyDiagnosticsFuel fuel loopDepth body
      | .forLoop initializers condition post body =>
          initializers.flatMap (forInitDiagnosticsFuel fuel) ++
            expressionDiagnosticsFuel fuel condition ++
            post.flatMap (forPostDiagnosticsFuel fuel) ++
            bodyDiagnosticsFuel fuel (loopDepth + 1) body
      | .break _ =>
          if loopDepth = 0 then
            [.controlOutsideLoop statement.span .breakControl]
          else
            []
      | .continue _ =>
          if loopDepth = 0 then
            [.controlOutsideLoop statement.span .continueControl]
          else
            []

private def forInitDiagnosticsFuel : Nat → ForInitItem →
    List StructuralDiagnostic
  | 0, _ => []
  | fuel + 1, item =>
      match item.payload with
      | .letBinding binding =>
          match binding.payload.initializer with
          | none => []
          | some expression => expressionDiagnosticsFuel fuel expression
      | .assignment _ left right =>
          expressionDiagnosticsFuel fuel left ++
            expressionDiagnosticsFuel fuel right
      | .expression expression => expressionDiagnosticsFuel fuel expression

private def forPostDiagnosticsFuel : Nat → ForPostItem →
    List StructuralDiagnostic
  | 0, _ => []
  | fuel + 1, item =>
      match item.payload with
      | .assignment _ left right =>
          expressionDiagnosticsFuel fuel left ++
            expressionDiagnosticsFuel fuel right
      | .expression expression => expressionDiagnosticsFuel fuel expression

end

/-- Find structural diagnostics in an expression within a module-sized bound. -/
private def expressionDiagnostics (fuel : Nat) (expression : Expression) :
    List StructuralDiagnostic :=
  expressionDiagnosticsFuel fuel expression

/-- Find structural diagnostics in a list of expressions. -/
private def expressionListDiagnostics (fuel : Nat)
    (expressions : List Expression) : List StructuralDiagnostic :=
  expressions.flatMap (expressionDiagnostics fuel)

/-- Find structural diagnostics in an optional expression. -/
private def optionalExpressionDiagnostics (fuel : Nat)
    (expression : Option Expression) : List StructuralDiagnostic :=
  match expression with
  | none => []
  | some value => expressionDiagnostics fuel value

/-- Find nested-lambda diagnostics in a pattern. -/
private def patternDiagnostics (fuel : Nat) (pattern : Pattern) :
    List StructuralDiagnostic :=
  patternDiagnosticsFuel fuel pattern

/-- Find structural diagnostics in one statement body at the current loop depth. -/
private def bodyDiagnostics (fuel loopDepth : Nat) (body : Body) :
    List StructuralDiagnostic :=
  bodyDiagnosticsFuel fuel loopDepth body

/-- Find structural diagnostics in one statement and all of its descendants. -/
private def statementDiagnostics (fuel loopDepth : Nat) (statement : Statement) :
    List StructuralDiagnostic :=
  statementDiagnosticsFuel fuel loopDepth statement

/-- Find nested-lambda diagnostics in one `for` initializer. -/
private def forInitDiagnostics (fuel : Nat) (item : ForInitItem) :
    List StructuralDiagnostic :=
  forInitDiagnosticsFuel fuel item

/-- Find nested-lambda diagnostics in one `for` post item. -/
private def forPostDiagnostics (fuel : Nat) (item : ForPostItem) :
    List StructuralDiagnostic :=
  forPostDiagnosticsFuel fuel item

private def functionDiagnostics
    (fuel : Nat)
    (modifierContext : Option ModifierContext)
    (parameterContext : ParameterContext)
    (declaration : FunctionDecl) : List StructuralDiagnostic :=
  let modifiers :=
    match modifierContext with
    | none => []
    | some context =>
        disallowedSignatureModifierDiagnostics context declaration.payload.signature
  modifiers ++
    missingParameterTypeDiagnostics parameterContext
      declaration.payload.signature.payload.parameters ++
    bodyDiagnostics fuel 0 declaration.payload.body

private def classMethodDiagnostics
    (declaration : ClassMethodDecl) : List StructuralDiagnostic :=
  disallowedSignatureModifierDiagnostics .classMethod
      declaration.payload.signature ++
    missingParameterTypeDiagnostics .classMethod
      declaration.payload.signature.payload.parameters

private def typeExprIsGroupedUnitFuel : Nat → TypeExpr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      match expression.payload with
      | .tuple [] => true
      | .group inner => typeExprIsGroupedUnitFuel fuel inner
      | _ => false

private def typeExprIsGroupedUnit (fuel : Nat) (expression : TypeExpr) : Bool :=
  typeExprIsGroupedUnitFuel fuel expression

private def fallbackDiagnostics
    (fuel : Nat)
    (declaration : FallbackDecl) : List StructuralDiagnostic :=
  let publicDiagnostic :=
    match declaration.payload.public with
    | none => []
    | some marker =>
        [.modifierNotAllowed marker.span .fallback marker.payload]
  let parameters :=
    if declaration.payload.parameters.isEmpty then []
    else [.fallbackHasParameters declaration.payload.marker.span
      declaration.payload.parameters.length]
  let returnType :=
    match declaration.payload.returnType with
    | none => []
    | some expression =>
        if typeExprIsGroupedUnit fuel expression then []
        else [.fallbackHasNonUnitReturn expression.span]
  publicDiagnostic ++ parameters ++ returnType ++
    bodyDiagnostics fuel 0 declaration.payload.body

private def constructorDiagnostics
    (fuel : Nat)
    (declaration : ContractConstructorDecl) : List StructuralDiagnostic :=
  let publicDiagnostic :=
    match declaration.payload.public with
    | none => []
    | some marker =>
        [.modifierNotAllowed marker.span .contractConstructor marker.payload]
  publicDiagnostic ++
    missingParameterTypeDiagnostics .contractConstructor
      declaration.payload.parameters ++
    bodyDiagnostics fuel 0 declaration.payload.body

private def contractMemberDiagnostics
    (fuel : Nat)
    (member : ContractMember) : List StructuralDiagnostic :=
  match member.payload with
  | .dataDecl _ | .typeAlias _ => []
  | .field declaration =>
      optionalExpressionDiagnostics fuel declaration.payload.initializer
  | .function declaration =>
      functionDiagnostics fuel none .contractFunction declaration
  | .fallback declaration => fallbackDiagnostics fuel declaration
  | .constructor declaration => constructorDiagnostics fuel declaration

private def contractDiagnostics
    (fuel : Nat)
    (declaration : ContractDecl) : List StructuralDiagnostic :=
  declaration.payload.members.flatMap (contractMemberDiagnostics fuel)

/-- Collect all structural candidates rooted at one top-level item. -/
private def topItemDiagnostics (fuel : Nat) (item : TopItem) :
    List StructuralDiagnostic :=
  match item.payload with
  | .importDecl declaration => importDiagnostics declaration
  | .exportDecl declaration => exportDiagnostics declaration
  | .pragmaDecl declaration => pragmaDiagnostics declaration
  | .dataDecl _ | .typeAliasDecl _ => []
  | .classDecl declaration =>
      declaration.payload.methods.flatMap classMethodDiagnostics
  | .instanceDecl declaration =>
      declaration.payload.methods.flatMap
        (functionDiagnostics fuel (some .instanceMethod) .instanceMethod)
  | .contractDecl declaration => contractDiagnostics fuel declaration
  | .functionDecl declaration =>
      functionDiagnostics fuel (some .topLevelFunction) .topLevelFunction declaration

/-- Every applicable structural diagnostic before ordering and deduplication. -/
def diagnosticCandidates (module : ParsedModuleV1) :
    List StructuralDiagnostic :=
  let fuel := astNodeMeasure module + 1
  module.payload.items.flatMap (topItemDiagnostics fuel)

private def diagnosticOccurs
    (diagnostic : StructuralDiagnostic) : List StructuralDiagnostic → Bool
  | [] => false
  | value :: rest =>
      if diagnostic = value then true else diagnosticOccurs diagnostic rest

@[simp] private theorem diagnosticOccurs_eq_true_iff
    {diagnostic : StructuralDiagnostic}
    {values : List StructuralDiagnostic} :
    diagnosticOccurs diagnostic values = true ↔ diagnostic ∈ values := by
  induction values with
  | nil => simp [diagnosticOccurs]
  | cons value rest induction =>
      simp [diagnosticOccurs, induction]

private def deduplicateDiagnostics :
    List StructuralDiagnostic → List StructuralDiagnostic
  | [] => []
  | diagnostic :: rest =>
      if diagnosticOccurs diagnostic rest then
        deduplicateDiagnostics rest
      else
        diagnostic :: deduplicateDiagnostics rest

@[simp] private theorem mem_deduplicateDiagnostics
    {diagnostic : StructuralDiagnostic}
    {values : List StructuralDiagnostic} :
    diagnostic ∈ deduplicateDiagnostics values ↔ diagnostic ∈ values := by
  induction values with
  | nil => simp [deduplicateDiagnostics]
  | cons head rest induction =>
      rw [deduplicateDiagnostics]
      split <;> simp_all

private theorem deduplicateDiagnostics_nodup
    (values : List StructuralDiagnostic) :
    (deduplicateDiagnostics values).Nodup := by
  induction values with
  | nil => simp [deduplicateDiagnostics]
  | cons diagnostic rest induction =>
      rw [deduplicateDiagnostics]
      split
      · exact induction
      · rename_i absent
        rw [List.nodup_cons]
        constructor
        · intro member
          apply absent
          exact diagnosticOccurs_eq_true_iff.mpr
            (mem_deduplicateDiagnostics.mp member)
        · exact induction

/-- Canonical diagnostics in stable code, source, span, and payload order. -/
def diagnostics (module : ParsedModuleV1) : List StructuralDiagnostic :=
  (deduplicateDiagnostics (diagnosticCandidates module)).mergeSort
    StructuralDiagnostic.le

@[simp] theorem mem_diagnostics
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ diagnostics module ↔
      diagnostic ∈ diagnosticCandidates module := by
  simp [diagnostics]

/-- Canonical structural diagnostics contain no repeated value. -/
theorem diagnostics_nodup (module : ParsedModuleV1) :
    (diagnostics module).Nodup := by
  unfold diagnostics
  exact (List.mergeSort_perm
    (deduplicateDiagnostics (diagnosticCandidates module))
      StructuralDiagnostic.le).nodup_iff.mpr
        (deduplicateDiagnostics_nodup (diagnosticCandidates module))

/-- Canonical structural diagnostics follow the closed diagnostic order. -/
theorem diagnostics_sorted (module : ParsedModuleV1) :
    (diagnostics module).Pairwise
      (fun left right => StructuralDiagnostic.le left right) := by
  unfold diagnostics
  apply List.pairwise_mergeSort
  · intro first second third firstSecond secondThird
    exact StructuralDiagnostic.le_trans firstSecond secondThird
  · intro left right
    rcases StructuralDiagnostic.le_total left right with forward | backward
    · simp [forward]
    · simp [backward]

@[simp] theorem diagnostics_eq_nil_iff (module : ParsedModuleV1) :
    diagnostics module = [] ↔ diagnosticCandidates module = [] := by
  constructor
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro diagnostic member
    have canonicalMember : diagnostic ∈ diagnostics module :=
      mem_diagnostics.mpr member
    simp [empty] at canonicalMember
  · intro empty
    simp [diagnostics, empty, deduplicateDiagnostics]

/-- Run the pure structural phase and report every canonical diagnostic. -/
def validateStructure
    (module : ParsedModuleV1) :
    Except (NonemptyList StructuralDiagnostic) Unit :=
  match diagnostics module with
  | [] => .ok ()
  | first :: rest => .error { head := first, tail := rest }

@[simp] theorem validateStructure_eq_ok_iff (module : ParsedModuleV1) :
    validateStructure module = .ok () ↔ diagnostics module = [] := by
  unfold validateStructure
  cases diagnostics module <;> simp

theorem validateStructure_eq_error_iff
    (module : ParsedModuleV1)
    (reported : NonemptyList StructuralDiagnostic) :
    validateStructure module = .error reported ↔
      diagnostics module = reported.head :: reported.tail := by
  cases reported with
  | mk head tail =>
      unfold validateStructure
      cases selected : diagnostics module with
      | nil => simp
      | cons first rest => simp

end Structure

export Structure (validateStructure)

end Solcore.Surface.Multi
