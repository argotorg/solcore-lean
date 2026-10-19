import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree

/-! The original bare assignment grammar projects prepared catalogs to the
legacy uniform diagnostic receipt. Projected branches remain excluded here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
open Core Frontend SourceInference
open PreparedBranchingCatalogSites
open CallableIndexedOwnedPreparedStagedLegacyBranchingTree
variable {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem assignment {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {resolution : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions resolution operator rhs}
    (site : AssignmentSite invalidProjection missingDefault registry faults head)
    (bare : resolution.target.projections = []) : head.ReachableErrors registry faults := by
  cases site with
  | existing errors => exact errors
  | projected _ _ nonempty _ _ => exact False.elim (nonempty bare)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem header {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    {context scope items code}
    {tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    (sites : HeaderSites invalidProjection missingDefault registry faults tree)
    (shape : ItemShape items) : tree.ErrorsFor .reachable registry faults := by
  revert shape
  refine HeaderSites.rec (motive := fun {context scope items code} tree _ =>
    ItemShape items → tree.ErrorsFor .reachable registry faults) ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope code next shape
    exact GenericForHeader.Tree.ErrorsFor.nil (context := context) (scope := scope) (code := code) (next := next)
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (ih shape.let_tail)
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.initialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (ih shape.let_tail)
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.discard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (found := found) (value := value) (remaining := remaining) (ih shape.discard_tail)
  · intro context scope assignment operator rhs rest body head remaining remainingErrors receipt ih shape
    exact GenericForHeader.Tree.ErrorsFor.assign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (head := head) (remaining := remaining) (ih shape.assign_tail.2.2) (PreparedBranchingLegacyCatalogSites.assignment receipt shape.assign_tail.2.1)
  · intro context scope assignment rest body head remaining remainingErrors receipt ih shape
    exact GenericForHeader.Tree.ErrorsFor.bitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (head := head) (remaining := remaining) (ih shape.bitNot_tail.2.2) receipt
  · intro context scope assignment rest body head remaining remainingErrors receipt ih shape
    exact False.elim (head.projected shape.bitNot_tail.2.1)

open GenericImperativeMatch

theorem body {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : CatalogSites invalidProjection missingDefault registry faults tree)
    (shape : PositionShape source position) : tree.CatalogSites .reachable registry faults := by
  revert shape
  refine CatalogSites.rec (motive := fun {context scope position expected type code} tree _ =>
    PositionShape source position → tree.CatalogSites .reachable registry faults)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body shape
    exact Tree.CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH (shape.tail_of_let found form))
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH (shape.tail_of_let found form))
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (remainingErrorsIH (shape.discard_tail found form notTail).2)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (innerErrorsIH (shape.block_children found form).1) (remainingErrorsIH (shape.block_children found form).2)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (thenTreeErrorsIH (shape.branches found form).1) (elseTreeErrorsIH (shape.branches found form).2.1) (remainingErrorsIH (shape.branches found form).2.2)
  · intro context scope mode id node rest expected type found form shape
    exact Tree.CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node rest expected type found form shape
    exact Tree.CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (loopBodyErrorsIH (shape.loop found form).1) (remainingErrorsIH (shape.loop found form).2)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (remainingErrorsIH (shape.assign_tail found form).2.2) (PreparedBranchingLegacyCatalogSites.assignment headErrors (shape.assign_tail found form).2.1)
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (remainingErrorsIH (shape.bitNot_tail found form).2.2) headErrors
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact False.elim (head.projected (shape.bitNot_tail found form).2.1)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH shape
    have parts := shape.for_children found form
    exact Tree.CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (initialErrorsIH ⟨parts.1, parts.2.1, parts.2.2.1⟩) (remainingErrorsIH parts.2.2.2)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH shape
    exact Tree.CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (loopErrorsIH shape.2.2) (header postErrors shape.2.1)
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH ⟨shape.1.let_tail, shape.2⟩)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH ⟨shape.1.let_tail, shape.2⟩)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (remainingErrorsIH ⟨shape.1.discard_tail, shape.2⟩)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (remainingErrorsIH ⟨shape.1.assign_tail.2.2, shape.2⟩) (PreparedBranchingLegacyCatalogSites.assignment headErrors shape.1.assign_tail.2.1)
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (remainingErrorsIH ⟨shape.1.bitNot_tail.2.2, shape.2⟩) headErrors
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact False.elim (head.projected shape.1.bitNot_tail.2.1)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) catalog patternContext (fun request member childContext valid => childErrorsIH request member childContext valid (shape.match_request found form valid.forget)) (remainingErrorsIH (shape.match_children found form).2.2)
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH shape
    exact Tree.CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (innerErrorsIH (shape.block_children found form).1)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH shape
    exact Tree.CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenErrorsIH (shape.branches found form).1) (elseErrorsIH (shape.branches found form).2.1)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH shape
    exact Tree.CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) catalog patternContext (fun request member childContext valid => childErrorsIH request member childContext valid (shape.match_request found form valid.forget))

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
