import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites

/-! Syntax weakening keeps the same prepared occurrences, keys and tokens.
The compiler certificates and original Source are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
open Core Frontend SourceInference
open GenericImperativeMatch
open PreparedBranchingCatalogSites
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
private theorem lexical_weaken {context mode statements expected}
    (tree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected) :
    GenericLexicalStatements.Syntax source (fun _ => True) context mode statements expected := by
  induction tree with
  | nil => apply GenericLexicalStatements.Syntax.nil <;> first | assumption | exact True.intro
  | returnUnit => apply GenericLexicalStatements.Syntax.returnUnit <;> first | assumption | exact True.intro
  | returnValue => apply GenericLexicalStatements.Syntax.returnValue <;> first | assumption | exact True.intro
  | tail => apply GenericLexicalStatements.Syntax.tail <;> first | assumption | exact True.intro
  | uninitialized => apply GenericLexicalStatements.Syntax.uninitialized <;> first | assumption | exact True.intro
  | initialized => apply GenericLexicalStatements.Syntax.initialized <;> first | assumption | exact True.intro
  | discard => apply GenericLexicalStatements.Syntax.discard <;> first | assumption | exact True.intro
  | block => apply GenericLexicalStatements.Syntax.block <;> first | assumption | exact True.intro
  | ifThen => apply GenericLexicalStatements.Syntax.ifThen <;> first | assumption | exact True.intro
  | terminalBlock => apply GenericLexicalStatements.Syntax.terminalBlock <;> first | assumption | exact True.intro
  | terminalIf => apply GenericLexicalStatements.Syntax.terminalIf <;> first | assumption | exact True.intro

private theorem weaken_all {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope position expected type code,
      CatalogSites invalidProjection missingDefault registry faults tree := by
  classical
  refine CatalogSites.rec (motive := fun {context scope position expected type code} _ _ =>
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope position expected type code, CatalogSites invalidProjection missingDefault registry faults tree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body
    exact ⟨_, CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := lexical_weaken syntaxTree) (body := body)⟩
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨innerNew, innerSites⟩ := innerErrorsIH
    exact ⟨_, CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := innerNew) (remaining := remainingNew) (innerErrors := innerSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨thenTreeNew, thenTreeSites⟩ := thenTreeErrorsIH
    obtain ⟨elseTreeNew, elseTreeSites⟩ := elseTreeErrorsIH
    exact ⟨_, CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTreeNew) (elseTree := elseTreeNew) (remaining := remainingNew) (thenTreeErrors := thenTreeSites) (elseTreeErrors := elseTreeSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node rest expected type found form
    exact ⟨_, CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)⟩
  · intro context scope mode id node rest expected type found form
    exact ⟨_, CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)⟩
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨loopBodyNew, loopBodySites⟩ := loopBodyErrorsIH
    exact ⟨_, CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBodyNew) (nativeTyped := nativeTyped) (remaining := remainingNew) (loopBodyErrors := loopBodySites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.bitNotProjected (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨initialNew, initialSites⟩ := initialErrorsIH
    exact ⟨_, CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initialNew) (remaining := remainingNew) (initialErrors := initialSites) (remainingErrors := remainingSites)⟩
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH
    obtain ⟨loopBodyNew, loopBodySites⟩ := loopErrorsIH
    exact ⟨_, CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBodyNew) (postTree := postTree) (nativeTyped := nativeTyped) (loopErrors := loopBodySites) (postErrors := postErrors)⟩
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerBitNotProjected (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    let childrenNew := fun request member childContext valid => (childErrorsIH request member childContext valid).choose
    have childrenSites := fun request member childContext valid => (childErrorsIH request member childContext valid).choose_spec
    exact ⟨_, CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := childrenNew) (remaining := remainingNew) (catalog := catalog) (patternContext := patternContext) (childErrors := childrenSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH
    obtain ⟨innerNew, innerSites⟩ := innerErrorsIH
    exact ⟨_, CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := innerNew) (stops := stops) (issued := issued) (innerErrors := innerSites)⟩
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH
    obtain ⟨thenTreeNew, thenTreeSites⟩ := thenErrorsIH
    obtain ⟨elseTreeNew, elseTreeSites⟩ := elseErrorsIH
    exact ⟨_, CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTreeNew) (elseTree := elseTreeNew) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenErrors := thenTreeSites) (elseErrors := elseTreeSites)⟩
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH
    let childrenNew := fun request member childContext valid => (childErrorsIH request member childContext valid).choose
    have childrenSites := fun request member childContext valid => (childErrorsIH request member childContext valid).choose_spec
    exact ⟨_, CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := childrenNew) (stops := stops) (issued := issued) (catalog := catalog) (patternContext := patternContext) (childErrors := childrenSites)⟩

theorem weaken {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope mode statements expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code}
    (_unique : NodeOccurrencesUnique source)
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope (.statements mode statements) expected type code,
      CatalogSites invalidProjection missingDefault registry faults tree :=
  weaken_all sites

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
