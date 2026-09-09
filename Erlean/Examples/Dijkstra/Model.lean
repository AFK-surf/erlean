import Erlean.Examples.Dijkstra.Certificate

namespace Erlean.Examples.DijkstraAlgorithm

open DijkstraCertificate (Edge Graph Walk)

abbrev Entry := Nat × Nat
abbrev Distances := List Entry

def seen (vertex : Nat) (settled : Distances) : Bool :=
  settled.any (fun entry => entry.1 == vertex)

def insert (vertex distance : Nat) : Distances → Distances
  | [] => [(vertex, distance)]
  | entry :: rest =>
    if distance ≤ entry.2 then (vertex, distance) :: entry :: rest
    else entry :: insert vertex distance rest

/-- Each edge is removed exactly when its source is first settled. -/
def expand (vertex distance : Nat) (remaining : Graph) (queue : Distances) : Distances × Graph :=
  match remaining with
  | [] => (queue, [])
  | edge :: rest =>
    if edge.source = vertex then
      expand vertex distance rest (insert edge.target (distance + edge.weight) queue)
    else
      let result := expand vertex distance rest queue
      (result.1, edge :: result.2)

/-- Fuel counts queue removals, including stale entries. The graph-size bound
    is justified by DijkstraAlgorithm's universal correctness proof. -/
def search (fuel : Nat) (queue : Distances) (remaining : Graph)
    (settled : Distances) : Option Distances :=
  match queue with
  | [] => some settled
  | entry :: rest =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if seen entry.1 settled then search fuel rest remaining settled
      else
        let expanded := expand entry.1 entry.2 remaining rest
        search fuel expanded.1 expanded.2 (entry :: settled)

def distances (source : Nat) (graph : Graph) : Option Distances :=
  (search (graph.length + 1) [(source, 0)] graph []).map List.reverse

def lookup : Distances → Nat → Option Nat
  | [], _ => none
  | entry :: rest, vertex =>
    if entry.1 = vertex then some entry.2 else lookup rest vertex

def ResultCorrect (graph : Graph) (source : Nat) (result : Distances) : Prop :=
  (∀ vertex distance, lookup result vertex = some distance →
    Walk graph source vertex distance ∧
      ∀ cost, Walk graph source vertex cost → distance ≤ cost) ∧
  (∀ vertex, lookup result vertex = none → ∀ cost, ¬ Walk graph source vertex cost)

def Ordered : Distances → Prop
  | [] => True
  | head :: rest => (∀ entry ∈ rest, head.2 ≤ entry.2) ∧ Ordered rest

end Erlean.Examples.DijkstraAlgorithm
