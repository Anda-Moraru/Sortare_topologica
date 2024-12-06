type Node = nat

class Graph {
  var n : nat

  predicate isValid()
    reads this
  {
     (forall i :: 0 <= i < n ==> i in adj.Keys) &&
    (forall i :: 0 <= i < n ==>(forall k :: k in adj[i] ==> 0 <= k < n))
  }
  var adj: map<Node, seq<Node>>

  constructor() {
    adj := map[]; 
  }

  method AddNode(n: Node)
    requires n !in adj.Keys
    ensures n in adj.Keys
    modifies this
  {
    adj := adj[n := []];
  }

  method AddEdge(u: Node, v: Node)
  requires u in adj.Keys && v in adj.Keys
  ensures u in adj.Keys 
  ensures v in adj[u] 
  ensures adj[u] == old(adj[u]) + [v] 
  modifies this
{
  var oldNeighbors := adj[u];
  adj := adj[u := oldNeighbors + [v]];
}



}
