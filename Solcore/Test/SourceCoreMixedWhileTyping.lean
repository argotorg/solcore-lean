import Solcore.Test.SourceCoreMixedWhileFixture
import Solcore.Test.SourceCoreMixedImperativeTyping

/-! The loop regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedWhile
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreMixedWhile
