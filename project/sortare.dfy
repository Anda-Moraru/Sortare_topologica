
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

predicate hasIncomingEdges<T>(G: Graph<T>, v : T)
  requires v in G.V
{
  exists u :: u in G.V && ( u ,v ) in G.E
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
    invariant forall i :: 0 <= i < | s |
                          ==> forall v :: v in remaining_G.V ==> ( v , s [ i ] ) !in G.E
    decreases remaining_G.V
  {

    
    lemmaAcyclicSubgraph(remaining_G, G);
    lemmaAcyclicIncindenceDegree(remaining_G);
    var v :| v in remaining_G.V && ! hasIncomingEdges(remaining_G, v);

    s := s + [v];
    remaining_G := removeVertex(v, remaining_G);
  }
}


lemma lemmaAcyclicIncindenceDegree<T>(G: Graph<T>)
  requires isValid(G) && G.V != {} && acyclic (G)
  ensures exists v :: v in G.V && !hasIncomingEdges(G, v)

{

  if forall v :: v in G.V ==> hasIncomingEdges(G, v) {
    var p := generatePath(G, |G.V| + 1);
    lemmaPathAcyclic(G, p);
    assert !acyclic(G);
  }
}

predicate  validPath<T>(p: seq<T>, G: Graph<T>) {
  forall i :: 0 <= i < |p| ==> p[i] in G.V && (i < |p| - 1 ==> (p[i], p[i+1]) in G.E)
}


lemma generatePath<T>(G: Graph<T>, n: nat) returns (p: seq<T>)
  requires isValid(G) && G.V != {}
  requires forall v :: v in G.V ==> hasIncomingEdges(G, v)
  ensures |p| == n && validPath(p, G)
{
  p := [];
  while |p| < n
    invariant |p| <= n && validPath(p, G)
  {
    var u :| u in G.V && (p == [] || (u, p[0]) in G.E);
    p := [u] + p;
  }
}

lemma lemmaPathAcyclic<T>(G: Graph<T>, p: seq<T>)
  requires isValid(G) && validPath(p, G) && |p| > |G.V|
  ensures !acyclic(G)
{
  if uniqueElements(p) {
    lemmaSeqLength(p, G.V);
  } else {
    var i, j :| 0 <= i < j < |p| && p[i] == p[j];
    var p' := p[i..j+1];

    lemmaComplexPath(G, p');
  }
}

predicate uniqueElements<T(==)>(s: seq<T>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function elements<T>(s: seq<T>): set<T> {
  set x | x in s
}

lemma lemmaSeqLength<T>(p: seq<T>, s: set<T>)
  requires uniqueElements(p) && elements(p) <= s
  ensures |p| <= |s|
{
  if p != [] {
    lemmaSeqLength(p[1..], s - {p[0]});
  }
}


lemma lemmaComplexPath<T>(G: Graph<T>, p: seq<T>)
  requires G.V != {} && validPath(p, G) && |p| > 1
  ensures existsPath(G, p[0], p[|p| - 1])
  decreases p
{
  if i :| 1 <= i < |p| - 1 && p[i] == p[0] {
    lemmaComplexPath(G, p[i..]);
  } else if |p| > 2 {
    lemmaComplexPath(Graph(G.V, G.E - {(p[0], p[1])}), p[1..]);
  }
}

////////////////////////////////////////////////////

lemma lemmaAcyclicSubgraph<T>(G': Graph<T>, G: Graph<T>)
  requires isValid(G) && isValid(G') && acyclic(G) && isSubGraph(G', G)
  ensures acyclic(G')
{
  if !acyclic(G') {
    var v :| v in G'.V && existsPath(G', v, v);
    lemmaExistsPath(G', G, v, v);

    assert !acyclic(G);
  }
}


predicate isSubGraph<T>(G: Graph<T>, G': Graph<T>) {
  G.E <= G'.E && G.V <= G'.V
}

lemma lemmaExistsPath<T>(G': Graph<T>, G: Graph<T>, u: T, v: T)
  requires isValid(G) && isValid(G') && isSubGraph(G', G) && existsPath(G', u, v)
  ensures existsPath(G, u, v)
  decreases G'.E
{
  if (u, v) !in G'.E {
    var e :| e in G'.E && e.0 == u && existsPath(Graph(G'.V, G'.E - {e}), e.1, v);

    lemmaExistsPath(Graph(G'.V, G'.E - {e}), Graph(G.V, G.E - {e}), e.1, v);
  }

}

