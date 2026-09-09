import Erlean.Examples.Dijkstra.Imported
import Erlean.Examples.Dijkstra.Certificate
import Erlean.Examples.Sequential.Reverse

namespace Erlean.Examples.Dijkstra

open Core Semantics Logic

def world : CodeWorld := [importedDijkstraModule]

def encodeNat (n : Nat) : Value := .integer n

def encodeEntry (entry : Nat × Nat) : Value :=
  .tuple [encodeNat entry.1, encodeNat entry.2]

def encodeQueue (queue : List (Nat × Nat)) : Value :=
  encodeList (queue.map encodeEntry)

def encodeEdge (edge : DijkstraCertificate.Edge) : Value :=
  .tuple [encodeNat edge.source, encodeNat edge.target, encodeNat edge.weight]

def encodeGraph (graph : DijkstraCertificate.Graph) : Value :=
  encodeList (graph.map encodeEdge)

def encodeBool (value : Bool) : Value := .atom (if value then "true" else "false")

/-- Every index is checked against the actual imported function list. -/
def distancesFunction : FunctionDef := importedDijkstraModule.functions[0]
def nonnegativeFunction : FunctionDef := importedDijkstraModule.functions[1]
def validEdgesFunction : FunctionDef := importedDijkstraModule.functions[2]
def searchFunction : FunctionDef := importedDijkstraModule.functions[3]
def settledFunction : FunctionDef := importedDijkstraModule.functions[4]
def expandFunction : FunctionDef := importedDijkstraModule.functions[5]
def insertFunction : FunctionDef := importedDijkstraModule.functions[6]
def reverseFunction : FunctionDef := importedDijkstraModule.functions[7]

/-- Entry after local invocation has resolved the actual imported function. -/
def callState (fn : FunctionDef) (args : Values) (stack : List Frame) : LocalState :=
  { control := .eval fn.body
    context := ⟨"dijkstra", fn.params.zip args⟩
    stack := stack }

/-- A finite return prefix leaves the caller's arbitrary stack untouched. -/
def Returns (start : LocalState) (result : Value) : Prop :=
  ∃ fuel context, runLocal fuel world start = .exhausted
    { control := .ret [result], context := context, stack := start.stack }

def settledState (vertex : Nat) (queue : List (Nat × Nat))
    (stack : List Frame) : LocalState :=
  callState settledFunction [encodeNat vertex, encodeQueue queue] stack

def insertState (vertex distance : Nat) (queue : List (Nat × Nat))
    (stack : List Frame) : LocalState :=
  callState insertFunction [encodeNat vertex, encodeNat distance, encodeQueue queue] stack

def reverseState (xs acc : Value) (stack : List Frame) : LocalState :=
  callState reverseFunction [xs, acc] stack

end Erlean.Examples.Dijkstra
