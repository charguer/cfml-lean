import Lean

namespace Cfml

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Xlet

end Cfml
