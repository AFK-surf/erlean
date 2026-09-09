import Erlean.Core.Match

namespace Erlean.Core.Checks

-- Kernel-checked regression cases exercise rejection and nested data boundaries.

example : scopeCheck [] (.var 7) = false := by simp [scopeCheck]

example : scopeCheck [] (.letE [0] (.lit (.integer 1)) (.var 0)) = true := by
  simp [scopeCheck, freshBinders]

example : scopeCheck [] (.letE [0, 0] (.values []) (.var 0)) = false := by
  simp [scopeCheck, freshBinders]

example : scopeCheck [0] (.letE [0] (.lit .nil) (.var 0)) = false := by
  simp [scopeCheck, freshBinders]

example : scopeCheck [] (.letE [0] (.var 0) (.var 0)) = false := by simp [scopeCheck]

example : scopeCheck [] (.caseE (.lit .nil)
    [([.cons (.var 0) (.var 1)], .lit (.atom "true"), .var 1)]) = true := by
  simp [scopeCheck, scopeCheckClauses, Pattern.binders, freshBinders]

example : scopeCheck [] (.caseE (.lit .nil)
    [([.cons (.var 0) (.var 0)], .lit (.atom "true"), .var 0)]) = false := by
  simp [scopeCheck, scopeCheckClauses, Pattern.binders, freshBinders]

example : scopeCheck [] (.caseE (.lit .nil)
    [([.var 0], .var 1, .var 0)]) = false := by
  simp [scopeCheck, scopeCheckClauses, Pattern.binders, freshBinders]

example : matchPattern (.tuple [.lit (.atom "ok"), .var 4])
    (.tuple [.atom "ok", .integer 42]) = some [(4, .integer 42)] := by
  simp [matchPattern, matchPatterns, BEq.beq, Value.equal]

example : matchPattern (.tuple [.wild]) (.tuple [.nil, .nil]) = none := by
  simp [matchPatterns]

example : matchPattern (.cons (.var 0) (.var 1))
    (.cons (.integer 3) (.atom "improper_tail")) =
    some [(0, .integer 3), (1, .atom "improper_tail")] := by
  simp [matchPattern]

example : matchPatterns [.wild] [] = none := by simp [matchPatterns]

example : matchPattern (.alias 0 (.cons (.var 1) .wild))
    (.cons (.integer 7) .nil) = some [(0, .cons (.integer 7) .nil), (1, .integer 7)] := by
  simp [matchPattern]

example : scopeCheck [] (.caseE (.lit .nil)
    [([.alias 0 (.var 0)], .lit (.atom "true"), .var 0)]) = false := by
  simp [scopeCheck, scopeCheckClauses, Pattern.binders, freshBinders]

example : Module.check ⟨"example", [("missing", 0)], []⟩ = false := by decide

example : Module.check ⟨"example", [("identity", 1)],
    [⟨"identity", [0], .var 0⟩]⟩ = true := by
  simp [Module.check, FunctionDef.scopeCheck, scopeCheck]

example : Module.check ⟨"example", [],
    [⟨"identity", [0], .var 0⟩, ⟨"identity", [1], .var 1⟩]⟩ = false := by decide

end Erlean.Core.Checks
