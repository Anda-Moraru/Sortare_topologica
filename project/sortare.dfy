
datatype Graph<T> = Graph(V: set<T>, E: set<(T, T)>)

predicate isValid<T>(G: Graph<T>) {
  forall e :: e in G.E ==> e.0 in G.V && e.1 in G.V
}

predicate acyclic<T>(G: Graph<T>) {
  !exists v :: v in G.V && existsPath(G, v, v)
}

predicate existsPath<T>(G: Graph<T>, u: T, v: T)
  decreases G.E
{
  (u, v) in G.E ||
  exists e :: e in G.E && e.0 == u &&
              existsPath(Graph(G.V, G.E - {e}), e.1, v)
}

function  removeVertex<T>(v: T, G: Graph<T>): Graph<T> {
  Graph(G.V - {v}, set e | e in G.E && e.0 != v && e.1 != v)
}

method AddNode<T>(v: T, G: Graph<T>) returns (newGraph: Graph<T>)
  requires v !in G.V
  ensures newGraph.V == G.V + {v}
  ensures newGraph.E == G.E
{
  newGraph := Graph(G.V + {v}, G.E);
}

method AddEdge<T>(u: T, v: T, G: Graph<T>) returns (newGraph: Graph<T>)
  requires u in G.V && v in G.V
  requires (u, v) !in G.E
  ensures newGraph.V == G.V
  ensures newGraph.E == G.E + {(u, v)}
{
  newGraph := Graph(G.V, G.E + {(u, v)});
}


method getIncidenceDegree<T>(v: T, G: Graph<T>) returns (incidenceDegree: int)
  requires isValid(G)
  requires v in G.V
{
  incidenceDegree := 0;
  var Ecopy := G.E;
  while(Ecopy != {})
    decreases Ecopy
  {
    var e :| e in Ecopy;
    if (e.1 == v)
    {
      incidenceDegree := incidenceDegree + 1;
    }
    Ecopy := Ecopy - { e };
  }

}

method getAllIncidenceDegrees<T>(G: Graph<T>) returns (degreeMap: map<T, int>)
  requires isValid(G)
{
  degreeMap := map[];
  var Vcopy := G.V;
  while( Vcopy != {})
    decreases Vcopy
  {
    var v :| v in Vcopy;
    var x := getIncidenceDegree(v, G);
    degreeMap := degreeMap[v := x];
    Vcopy := Vcopy - { v };
  }
}



method topsort<T>(G: Graph<T>) returns (s: seq<T>)
  requires isValid(G) && acyclic(G)
{
  s := [];
  var remaining_G := G;

  while remaining_G.V != {}
    invariant remaining_G == Graph( set v | v in G.V && v !in s,
                                    set e | e in G.E && e.0 !in s && e.1 !in s)
    invariant multiset(s) == multiset(G.V - remaining_G.V)
    invariant forall i, j :: 0 <= i <= j < |s| ==> (s[j], s[i]) !in G.E
    decreases remaining_G.V
  {

    var remaining_G_V := remaining_G.V;
    var v :| v in remaining_G.V;
    var x := getIncidenceDegree(v, remaining_G);

    while (remaining_G_V != {} && x != 0)
      decreases remaining_G_V
    {
      remaining_G_V := remaining_G_V - {v};
      var v :| v in remaining_G.V;
      var x := getIncidenceDegree(v, remaining_G);

    }

    var test1 := getIncidenceDegree(v, remaining_G);
    assert test1 == 0;
    s := s + [v];
    remaining_G := removeVertex(v, remaining_G);
  }
}