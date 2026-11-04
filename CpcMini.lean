-- This module serves as the root of the `CpcMini` library.
-- Import modules here that should be built as part of the library.
module

public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtEval
import all CpcMini.SmtEval
public import CpcMini.SmtTranslate
import all CpcMini.SmtTranslate
public import CpcMini.TranslationChecks
import all CpcMini.TranslationChecks

-- The proofs under `CpcMini/Proofs/` are deliberately not imported here: the
-- `cpcmini` CI group builds them directly.

public section
