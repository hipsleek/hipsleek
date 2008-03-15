class Node {
    private static int nnid = 0;

    private Node[] edges = null;
    private int numEdges = 0;
    private int nid;
    Node parent;
    private boolean visited = false;

    /*: public static ghost specvar root :: obj;
        public static ghost specvar processed :: objset = "{}";

	public ghost specvar reachable :: objset = "{}";

	public ghost specvar init :: bool = "False";

	public specvar neighbors :: objset;
	private vardefs "neighbors == 
	 {x. x ~= null & (EX i. 0 <= i & i < numEdges & x = edges.[i])}";

	private invariant EdgesNonNullInv: "init --> edges ~= null"

	private invariant NumEdgesLBInv: "0 <= numEdges"
	private invariant NumEdgesUBInv: 
	"init --> numEdges <= edges..Array.length"

	private invariant NeighborsNonNullInv:
	"init --> (ALL i. (0 <= i & i < numEdges) --> edges.[i] ~= null)"

	private invariant NeighborsInitInv:
	"init --> (ALL i. (0 <= i & i < numEdges) --> edges.[i]..Node.init)"

	private invariant ReachableInv: "visited --> (root : reachable)"
	private invariant ProcessedInv: "visited = (this : processed)"

	private invariant NVReachableInv: "~visited --> reachable = {}"
	
	private invariant NVParentInv: 
	"~visited & this ~= null --> (ALL x. x..Node.parent ~= this)"

	private invariant ReachableBCInv:
	"visited & parent = null --> reachable = { this }"

	private invariant ReachableICInv:
	"visited & parent ~= null --> 
	reachable = parent..Node.reachable Un { this }"

	private invariant NotInitInv: "~init --> reachable = {}";

	private invariant RootInv:
	"visited & parent = null --> root = this"
    */
    
    public Node(int maxEdges)
    /*: requires "0 < maxEdges & ~init"
        modifies "Node.reachable", "Node.neighbors", "Node.init"
        ensures  "neighbors = {} & reachable = {} & init"
    */
    {
	Node [] es = new Node[maxEdges];
	edges = es;
	numEdges = 0;
	nid = nnid;
	nnid = nnid + 1;
	visited = false;
	//: "init" := "True";
	//: "reachable" := "{}";
    }

    public boolean addEdge(Node n)
    /*: requires "init & n ~= null & n..Node.init"
        modifies "Node.neighbors", "Array.arrayState"
        ensures  "(result --> neighbors = (old neighbors) Un { n }) &
	          (~result --> neighbors = (old neighbors))"
     */
    {
	/*: noteThat OldNeighborsDef:
	  "neighbors = 
	  {x. x ~= null & (EX i. 0 <= i & i < numEdges & x = edges.[i])}";
	*/
	if (numEdges < edges.length) {

	    edges[numEdges] = n;
	    numEdges = numEdges + 1;

	    //: noteThat NNonNull: "n ~= null";
	    //: noteThat ThisNumEdgesLB: "0 <= (old numEdges)"
	    /*: noteThat NewNeighborsDef:
	      "neighbors = 
	      {x. x ~= null & (EX i. 0 <= i & i < numEdges & x = edges.[i])}";
	    */
	    /*: noteThat NeighborsChanged: 
	      "neighbors = (old neighbors) Un { n }"
	      from NeighborsChanged, NeighborsDef, NNonNull, ThisNumEdgesLB;
	    */
	    /*: noteThat NumEdgesLBLemma: "theinv NumEdgesLBInv"
	      from NumEdgesLBLemma, NumEdgesLBInv;
	    */
	    /*: noteThat NumEdgesUBLemma: "theinv NumEdgesUBInv"
	      from NumEdgesUBLemma, NumEdgesUBInv, TrueBranch;
	    */
	    return true;
	}
	return false;
    }

    public void compute()
    /*: requires "init & reachable = {} & root = null & processed = {}"
        modifies "Node.reachable", "Node.root", "Node.parent", "Node.processed"
        ensures  "this : processed &
	          (ALL x y. x : processed & y : x..Node.neighbors -->
		  y : processed)"
    */
    {
	makeRoot();

	int i = 0;
 
	while /*: inv "0 <= i & reachable = { this } & theinvs &
		       this : processed &
		       (ALL j. 0 <= j & j < i --> edges.[j] : processed) &
		       (ALL x y. x ~: reachable & x : processed & 
		       y : x..Node.neighbors --> y : processed)"
	       */
	    (i < numEdges()) {

	    /*: noteThat RootReachable:
	      "reachable = { this }";
	     */
	    /*: noteThat LoopPost:
	      "(ALL x y. x ~: reachable & x : processed & 
	      y : x..Node.neighbors --> y : processed)"
	    */
	    /*: noteThat SpanPre:
	      "ALL x y. x ~: reachable & x : processed & 
	      y : x..Node.neighbors --> y : processed"
	      from SpanPre, RootReachable, LoopPost;
	    */
	    edge(i).span(this);
	    i = i + 1;
	}
	/*: noteThat ReachablePost: 
	  "reachable = { this }";
	*/
	/*: noteThat ThisNeighborsProcessed:
	  "ALL y. y : neighbors --> y : processed";
	*/
	/*: noteThat OtherNeighborsProcessed:
	  "ALL x y. x ~: reachable & x : processed & y : x..Node.neighbors -->
	  y : processed";
	*/
	/*: noteThat AllNeighborsProcessed:
	  "ALL x y. x : processed & y : x..Node.neighbors --> y : processed"
	  from AllNeighborsProcessed, ThisNeighborsProcessed, 
	  OtherNeighborsProcessed, ReachablePost;
	*/
    }

    private void makeRoot()
    /*: requires "init & root = null & reachable = {} & processed = {} & 
                  theinvs"
        modifies "Node.reachable", "Node.root", "Node.processed",
	         "Node.visited", "Node.parent"
        ensures  "visited & parent = null & root = this & 
	          reachable = { this } & processed = { this } & theinvs"
    */
    {
	visited = true;
	parent = null;
	//: "Node.root" := "this";
	//: "reachable" := "{ this }";
	//: "processed" := "processed Un { this }";
    }

    private boolean visit(Node p)
    /*: requires "init & p ~= null & root : p..Node.reachable & theinvs &
                  (ALL x y. x ~: p..Node.reachable & x : processed &
		  y : x..Node.neighbors --> y : processed)"
        modifies "Node.reachable", "Node.processed", 
	         "Node.visited", "Node.parent"
        ensures  "visited & root : reachable &
	          (result --> reachable = p..Node.reachable Un { this }) & 
	          theinvs &
	          (ALL x. fieldRead (old Node.reachable) x ~= {} -->
		  x..Node.reachable = fieldRead (old Node.reachable) x) &
		  (ALL x. x ~= this -->
		  (fieldRead (old Node.visited) x) = x..Node.visited) &
		  processed = (old processed) Un { this } &
		  (result --> (ALL x y. x ~: reachable & x : processed & 
		  y : x..Node.neighbors --> y : processed)) &
		  (~result --> (ALL x y. x ~: p..Node.reachable & 
		  x : processed & y : x..Node.neighbors --> y : processed)) &
		  root = old root & Object.alloc = (old Object.alloc)"
    */
    {
	/*: noteThat NeighborsPre:
	  "(ALL x y. x ~: p..Node.reachable & x : processed & 
	  y : x..Node.neighbors --> y : processed)";
	*/
	if (!visited) {
	    visited = true;
	    parent = p;
	    //: "reachable" := "p..Node.reachable Un { this }";
	    //: "processed" := "processed Un { this }";

	    /*: noteThat NeighborsProcessed:
	      "(ALL x y. x ~: reachable & x : processed & 
	      y : x..Node.neighbors --> y : processed)"
	      from NeighborsPre, NeighborsProcessed;
	    */

	    return true;
	}
	return false;
    }

    private void span(Node p)
    /*: requires "init & p ~= null & root : p..Node.reachable & theinvs &
                  (ALL x y. x ~: p..Node.reachable & x : processed &
		  y : x..Node.neighbors --> y : processed)"
        modifies "Node.reachable", "Node.processed",
	         "Node.visited", "Node.parent"
        ensures  "visited & root : reachable & this : processed & theinvs &
	          (ALL x. fieldRead (old Node.reachable) x ~= {} -->
		  x..Node.reachable = fieldRead (old Node.reachable) x) &
		  (ALL x. fieldRead (old Node.visited) x --> x..Node.visited) &
		  (ALL x. x : (old Node.processed) --> x : Node.processed) &
		  (ALL x y. x ~: p..Node.reachable & x : processed & 
		  y : x..Node.neighbors --> y : processed)"
    */
    {
	if (!visit(p)) {
	    /*: noteThat SpanPost:
	      "(ALL x y. x ~: p..Node.reachable & x : processed & 
	      y : x..Node.neighbors --> y : processed)"
	      from SpanPost, visit_Post, TrueBranch;
	    */
	    return;
	}

	int i = 0;

	/*: noteThat SpanPre:
	  "ALL x y. x ~: reachable & x : processed & 
	  y : x..Node.neighbors --> y : processed"
	  from SpanPre, visit_Post, FalseBranch;
	*/
 
	while /*: inv "0 <= i & root : reachable & theinvs & 
		       this..Node.visited & this : processed &
		       (ALL x. fieldRead (old Node.reachable) x ~= {} -->
		       x..Node.reachable = fieldRead (old Node.reachable) x) &
		       (ALL x. fieldRead (old Node.visited) x --> 
		       x..Node.visited) &
		       (ALL x. x : (old Node.processed) --> 
		       x : Node.processed) &
		       (ALL j. 0 <= j & j < i --> edges.[j] : processed) &
		       (ALL x y. x ~: reachable & x : processed & 
		       y : x..Node.neighbors --> y : processed) &
		       (reachable = p..Node.reachable Un { this })"
	       */
	    (i < numEdges()) {
	    edge(i).span(this);
	    i = i + 1;
	}
	/*: noteThat ReachablePost: 
	  "reachable = p..Node.reachable Un { this }";
	*/
	/*: noteThat ThisNeighborsProcessed:
	  "ALL y. y : neighbors --> y : processed";
	*/
	/*: noteThat OtherNeighborsProcessed:
	  "ALL x y. x ~: reachable & x : processed & y : x..Node.neighbors -->
	  y : processed";
	*/
	/*: noteThat AllNeighborsProcessed:
	  "ALL x y. x ~: p..Node.reachable & x : processed &
	  y : x..Node.neighbors --> y : processed"
	  from AllNeighborsProcessed, ThisNeighborsProcessed, 
	  OtherNeighborsProcessed, ReachablePost;
	*/
    }

    private int numEdges()
    /*: requires "init & theinvs"
        ensures  "result = numEdges & theinvs"
    */
    {
	return numEdges;
    }

    private Node edge(int i)
    /*: requires "init & 0 <= i & i < numEdges & theinvs"
        ensures "result = edges.[i] & theinvs"
    */
    {
	return edges[i];
    }
}