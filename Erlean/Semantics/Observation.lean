import Erlean.Semantics.Machine

namespace Erlean.Semantics

/-- Internal exception information may be transported by compiler-generated Core,
    but is not an Erlang term that an external observer can receive. -/
def observeOutcome : Outcome → Outcome
  | .returned values =>
    if Core.Value.publicList values then .returned values
    else .fault (.unsupported "Escaping internal exception information")
  | .raised exception =>
    if exception.reason.isPublic then .raised exception
    else .fault (.unsupported "Internal exception information in an observable reason")
  | .fault fault => .fault fault

theorem observe_returned (values : Core.Values) (h : Core.Value.publicList values = true) :
    observeOutcome (.returned values) = .returned values := by simp [observeOutcome, h]

end Erlean.Semantics
