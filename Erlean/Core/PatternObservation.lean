import Erlean.Core.Match

namespace Erlean.Core

mutual
/-- Check only the fields that literal equality would inspect. An outer shape
    mismatch does not observe opaque information nested inside the value. -/
def literalObservationAllowed (expected value : Value) : Bool :=
  match expected, value with
  | .exceptionInfo _, _ | _, .exceptionInfo _ => false
  | .floatBits _, .floatBits _ => false
  | .function _ _ _, .function _ _ _ | .closure _ _ _ _, .closure _ _ _ _ => false
  | .cons head tail, .cons first rest =>
    literalObservationAllowed head first &&
      (!(head == first) || literalObservationAllowed tail rest)
  | .tuple expected, .tuple values => literalListObservationAllowed expected values
  | .map expected, .map values =>
      (Value.map expected).exactComparable && (Value.map values).exactComparable
  | _, _ => true
termination_by sizeOf expected

def literalListObservationAllowed (expected values : List Value) : Bool :=
  match expected, values with
  | head :: tail, first :: rest =>
    literalObservationAllowed head first &&
      (!(head == first) || literalListObservationAllowed tail rest)
  | _, _ => true
termination_by sizeOf expected
end

mutual
/-- Variable and wildcard patterns may transport opaque information. Constructor
    discrimination and literal comparison must not inspect that information. -/
def patternObservationAllowed (pattern : Pattern) (value : Value) : Bool :=
  match pattern, value with
  | .wild, _ | .var _, _ => true
  | .alias _ pattern, value => patternObservationAllowed pattern value
  | .lit expected, value => literalObservationAllowed expected value
  | .cons _ _, .exceptionInfo _ | .tuple _, .exceptionInfo _ | .bytes _, .exceptionInfo _
  | .map _ _, .exceptionInfo _ => false
  | .cons head tail, .cons first rest =>
    patternObservationAllowed head first &&
      ((matchPattern head first).isNone || patternObservationAllowed tail rest)
  | .tuple patterns, .tuple values => patternsObservationAllowed patterns values
  | .map keys patterns, .map entries =>
    Value.mapOrdered entries &&
      match selectMapValues keys entries with
      | some values => patternsObservationAllowed patterns values
      | none => true
  | .bytes patterns, .bitstring bits =>
    match decodeByteValues patterns.length bits with
    | some values => patternsObservationAllowed patterns values
    | none => true
  | _, _ => true
termination_by sizeOf pattern

def patternsObservationAllowed (patterns : List Pattern) (values : Values) : Bool :=
  match patterns, values with
  | pattern :: rest, value :: remaining =>
    patternObservationAllowed pattern value &&
      ((matchPattern pattern value).isNone || patternsObservationAllowed rest remaining)
  | _, _ => true
termination_by sizeOf patterns
end

end Erlean.Core
