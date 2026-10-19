import Solcore.Test.SourceCoreMixedOperatorsFixture
import Solcore.Test.SourceCoreMixedImperativeTyping

/-! The builtin-value regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedOperators
