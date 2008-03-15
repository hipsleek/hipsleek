class Node {
    
    boolean isBody = true;

    Node next;

    Node subp[] = null;

    static Node nodes;
    static Node root;

    static int si;
    static int sj;

    /*: public ghost specvar llcontents :: objset = "{}";
        public ghost specvar init :: bool = "False";
	public ghost specvar children :: objset = "{}";
	public ghost specvar subtree :: objset = "{}";

	public static specvar bodies :: objset;
        private vardefs "bodies == nodes..Node.llcontents";

	public static specvar treecontents :: objset;
	vardefs "treecontents == root..Node.subtree";

        invariant LLContentsDefBCInv: 
	"init & this ~= null & next = null --> llcontents = { this }";

	invariant LLContentsDefRCInv:
	"init & this ~= null & next ~= null --> 
	(llcontents = next..Node.llcontents Un { this } & 
	this ~: next..Node.llcontents)";

	invariant LLContentsDefNullInv:
	"Node.llcontents null = {}";

	invariant NodesPropInv: 
	"nodes ~= null --> 
	nodes : Object.alloc & nodes : Node & 
	nodes..Node.init & nodes..Node.isBody";

	invariant LLContentsPropInv: 
	"ALL x. x : bodies --> 
	x : Node & x : Object.alloc & x..Node.init & x..Node.isBody";

	invariant LLContentsBodiesRecInv:
	"ALL x. this : bodies & x : llcontents --> x : bodies";

	invariant ChildrenDefBCInv:
	"isBody --> children = {}";

	invariant ChildrenDefRCInv:
	"~isBody --> children = 
	{ c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }";

	invariant SubtreeDefBCInv:
	"isBody & init --> subtree = { this }";

	invariant SubtreeDefRCInv:
	"~isBody & init --> 
	subtree = { s. (EX c. c : children & s : c..Node.subtree) }";

	invariant SubtreeDefNullInv:
	"Node.subtree null = {}";

	invariant CellBodyInv: "isBody = (subp = null)";
      
	invariant SubpBoundsInv: "subp ~= null --> subp..Array.length = 8";

	invariant SubpInjInv: 
	"ALL m n. m..Node.subp = n..Node.subp & m..Node.subp ~= null --> m = n";

	invariant LLContentsBCInv:
	"init & next = null --> llcontents = { this }";

	invariant LLContentsRCInv:
	"(init & next ~= null) --> 
	((llcontents = { this } Un next..Node.llcontents) & 
	(this ~: next..Node.llcontents))";

	invariant NextInitInv:
	"ALL x y. x = y..Node.next & x ~= null --> 
	x..Node.init & x : Object.alloc";

	invariant IndexInBounds: "0 <= si & si < 8 & 0 <= sj & sj < 8";

	invariant SubpElemsInv: 
	"ALL x y i. x = y..Node.subp.[i] & x ~= null --> 
	x : Node & x ~= y & x..Node.init & x ~= root";

	invariant ChildrenInjInv:
	"ALL x y z. y : Object.alloc & y : Node & z : Object.alloc & z : Node &
	x : y..Node.children & x : z..Node.children --> y = z";

	invariant ChildrenAdvInjInv:
	"ALL x y z i j. 
	x = y..Node.subp.[i] & x = z..Node.subp.[j] & x ~= null --> 
	y = z & i = j";

	invariant RootInitInv: "root ~= null --> root..Node.init";
    */

    public static Node makeCell()
    /*: modifies "Node.subtree", "Node.children", "Node.llcontents", 
                 "Node.init", "Node.subp", "Node.isBody"
        ensures "~result..Node.isBody & result..Node.init &
	         (ALL i. 0 <= i & i < 8 --> result..Node.subp.[i] = null) &
		 root = (old root) &
		 (ALL x. x : (old Object.alloc) --> 
		 x..Node.subtree = (fieldRead (old Node.subtree) x)) &
		 (ALL x. x : (old Object.alloc) -->
		 x..Node.children = (fieldRead (old Node.children) x)) &
		 (ALL x. x : (old Object.alloc) -->
		 x..Node.llcontents = (fieldRead (old Node.llcontents) x)) &
		 (ALL x. x : (old Object.alloc) -->
		 x..Node.init = (fieldRead (old Node.init) x)) &
		 (ALL x. x : (old Object.alloc) -->
		 x..Node.subp = (fieldRead (old Node.subp) x)) &
		 (ALL x. x : (old Object.alloc) -->
		 x..Node.isBody = (fieldRead (old Node.isBody) x))"
    */
    {
	Node n = new Node();
	n.isBody = false;
	n.subp = new Node[8];
	n.next = null;

	//: "n..Node.init" := "True";
	//: "n..Node.llcontents" := "{ n }";
	//: "n..Node.children" := "{}";
	//: "n..Node.subtree" := "{}";

	return n;
    }
    
    private Node getNext()
    /*: ensures "result = next & 
                 nodes = (old nodes) & 
		 Array.arrayState = (old Array.arrayState) &
		 Node.subp = (old Node.subp) &
		 Object.alloc = (old Object.alloc)"
     */
    {
	return next;
    }

    public static void makeTree()
    /*: requires "treecontents = {} & 
                  (ALL x y i. (x : bodies --> y..Node.subp.[i] ~= x))"
        modifies "Array.arrayState", "Node.children", "Node.subtree", 
	         "Node.treecontents", "Node.root", "Node.subp",
		 "Node.llcontents", "Node.init", "Node.isBody"
        ensures "treecontents = bodies"
    */
    {
	//: ghost specvar p :: obj = "null";
	Node n = nodes;

	while 
	    /*: inv "(comment ''StartLoop'' (p = null --> treecontents = {})) &
		     (comment ''PNRel'' (p = null) = (n = nodes)) &
	             (n ~= null --> n : bodies) &
	             (comment ''NProps'' 
		     (n ~= null --> 
		     n : Node & n : Object.alloc & 
		     n..Node.init & n..Node.isBody)) &
		     (comment ''SubpLInv''
		     (ALL x y i. x : n..Node.llcontents --> 
		     y..Node.subp.[i] ~= x)) &
	             (comment ''ElemProps'' 
		     (ALL x. x : n..Node.llcontents --> 
		     (x : Node & x : Object.alloc & x..Node.isBody & 
		     x..Node.init & x ~: treecontents))) &
		     (p ~= null --> p ~= n) &
		     (p ~= null --> n = p..Node.next) &
	             (comment ''ProcessedLoop'' (p ~= null --> 
		      treecontents = (bodies \<setminus> n..Node.llcontents))) &
		     (bodies = old bodies) & (nodes = old nodes) &
		     theinvs"
	    */
	    (n != null) {
	    
	    n.addToTree();

	    //: p := "n";
	    n = n.getNext();
	}
    }

    private void setRoot()
    /*: modifies "root", "treecontents"
        ensures "root = this & treecontents = subtree & 
	         Object.alloc = (old Object.alloc)"
    */
    {
	root = this;
    }

    private void addToTree()
    /*: requires "init & isBody & (this ~: treecontents) & 
                  (comment ''NotPointedToPre''
		  (ALL x i. x..Node.subp.[i] ~= this)) &
                  theinvs"
        modifies "treecontents", "root", "Node.subtree", "Node.children",
	         "Array.arrayState", "Node.llcontents", "Node.init",
		 "Node.isBody", "Node.subp"
        ensures  "treecontents = (old treecontents) Un { this } & 
	          theinvs &
		  (comment ''NotPointedToPost''
		  (ALL x. 
		  (x : (old Object.alloc) & x ~= null & 
		  x ~= this & x ~= (old root) &
		  (ALL y i. 
		  (arrayRead (old Array.arrayState) 
		  (fieldRead (old Node.subp) y) i) ~= x)) -->
		  (ALL z j. z..Node.subp.[j] ~= x))) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.llcontents = (fieldRead (old Node.llcontents) x)) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.init = (fieldRead (old Node.init) x)) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.isBody = (fieldRead (old Node.isBody) x))"
    */
    {
	if (root == null) {
	    root = this;
	    return;
	}

	if (root.isBody) {
	    Node m = root;
	    root = new Node();
	    root.subp = new Node[8];
	    root.isBody = false;
	    root.next = null;

	    //: "root..Node.init" := "True";
	    //: "root..Node.llcontents" := "{ root }";
	    //: "root..Node.children" := "{}";
	    //: "root..Node.subtree" := "{}";

	    root.subp[si] = m;
	    //: "root..Node.children" := "root..Node.children Un { m }";
	    //: "root..Node.subtree" := "m..Node.subtree Un { this }";
	} else {
	    //: "root..Node.subtree" := "root..Node.subtree Un { this }";
	}
	root.loadTree(this);
    }	


    private void loadTree(Node toLoad)
    /*: requires "init & ~isBody & (toLoad ~= null) & (toLoad ~= root) &
                  (toLoad..Node.isBody) & (toLoad..Node.init) &
		  (ALL x i. x..Node.subp.[i] ~= toLoad) &
                  (theinv LLContentsDefBCInv) &
		  (theinv LLContentsDefRCInv) &
		  (theinv LLContentsDefNullInv) &
		  (theinv NodesPropInv) &
		  (theinv LLContentsPropInv) &
		  (theinv LLContentsBodiesRecInv) &
		  (theinv ChildrenDefBCInv) &
		  (theinv ChildrenDefRCInv) &
		  (theinv SubtreeDefBCInv) &
		  (comment ''SubtreeDefRCOther''
		  (ALL x. x : Object.alloc & x : Node & x ~= this & 
		   ~x..Node.isBody & x..Node.init --> 
		   x..Node.subtree = 
		  { s. (EX c. (c : x..Node.children & s : c..Node.subtree))})) &
		  (comment ''SubtreeDefRCThis''
		  (subtree = 
		  { s. (EX c. (c : children & s : c..Node.subtree))} Un 
		  { toLoad })) &
		  (theinv SubtreeDefNullInv) &
		  (theinv CellBodyInv) &
		  (theinv SubpBoundsInv) &
		  (theinv SubpInjInv) &
		  (theinv LLContentsBCInv) &
		  (theinv LLContentsRCInv) &
		  (theinv NextInitInv) &
		  (theinv IndexInBounds) &
		  (theinv SubpElemsInv) &
		  (theinv ChildrenInjInv) &
		  (theinv ChildrenAdvInjInv) &
		  (theinv RootInitInv)"
	 modifies "Node.children", "Array.arrayState", "Node.subtree",
	          "Node.subp", "Node.isBody", "Node.llcontents", "Node.init"
	 ensures  "theinvs &
		  (nodes = old nodes) & (bodies = old bodies) &
		  (treecontents = old treecontents) &
		  (comment ''NotPointedToPost''
		  (ALL x. (x : (old Object.alloc) & x ~= null & x ~= toLoad &
		  (ALL y i. (arrayRead (old Array.arrayState) 
		  (fieldRead (old Node.subp) y) i) ~= x)) -->
		  (ALL z j. z..Node.subp.[j] ~= x))) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.llcontents = (fieldRead (old Node.llcontents) x)) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.init = (fieldRead (old Node.init) x)) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.isBody = (fieldRead (old Node.isBody) x)) &
		  (ALL x. x : (old Object.alloc) -->
		  x..Node.subp = (fieldRead (old Node.subp) x))"
    */
    {
	Node n = subp[si];

	if (n == null) {
	    subp[si] = toLoad;
	    //: "children" := "children Un { toLoad }";

	    return;
	}

	if (n.isBody) {
	    /*: noteThat ThisSubpMInj: 
	      "ALL x. x : Object.alloc & x : Node & n : x..Node.children --> 
	      x = this";
	    */

	    Node m = new Node();
	    m.subp = new Node[8];
	    m.isBody = false;
	    m.next = null;

	    //: "m..Node.init" := "True";
	    //: "m..Node.llcontents" := "{ m }";
	    //: "m..Node.children" := "{}";
	    //: "m..Node.subtree" := "{}";

	    //: noteThat NNotM: "subp.[si] ~= m";
	    //: noteThat ThisNotM: "this ~= m";
	    //: noteThat MNotEq: "m..Node.subp.[si] ~= m";

	    //: noteThat NInThis: "n : children";
	    //: noteThat MNotChild: "m ~: children";

	    //: noteThat SubpNotNode: "m..Node.subp ~: Node";
	    //: noteThat MNotInArray: "ALL x i. x.[i] ~= m";
	    /*: noteThat MNotAnyChild: "ALL x. x : (old Object.alloc) &
	      x : Node --> m ~: x..Node.children"
	      from MNotAnyChild, ChildrenDefRCInv, ChildrenDefBCInv,
	      MNotInArray;
	    */

	    m.subp[sj] = n;
	    //: "m..Node.children" := "m..Node.children Un { n }";
	    //: "m..Node.subtree" := "n..Node.subtree Un { toLoad }";

	    //: noteThat MProps: "m ~= null & this ~= m";
	    //: noteThat ThisMInj: "subp ~= m..Node.subp";
	    /*: noteThat OldThisChildren: "children = 
	      { c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }";
	    */
	    //: noteThat MNotInSubp: "ALL i. subp.[i] ~= m";
	    //: noteThat NInj: "ALL i. subp.[i] = n --> i = si";
	    //: noteThat OldSubp: "subp.[si] = n & n ~= null";

	    subp[si] = m;
	    //: "children" := "(children \<setminus> { n }) Un { m }";

	    /*: noteThat NewThisChildren: "children = 
	      { c. (EX i. 0 <= i & i < 8 & c = subp.[i] & c ~= null) }"
	      from NewThisChildren, OldThisChildren, MProps, ThisMInj,
	      IndexInBounds, MNotInSubp, OldSubp, NInj;
	    */
	    /*: noteThat MChildren: "m..Node.children = 
	      { c. (EX i. 0 <= i & i < 8 & c = m..Node.subp.[i] & c ~= null) }";
	    */
	    /*: noteThat SubpInj: 
	      "ALL x. x ~= m --> x..Node.subp ~= m..Node.subp";
	     */
	    //: noteThat ThisNonNull: "this..Node.subp ~= null";
	    /*: noteThat OtherChildren: "ALL x. x ~= this & x ~= m & 
	      x : Object.alloc & x : Node & ~x..Node.isBody --> 
	      x..Node.children = 
	      { c. (EX i. 0 <= i & i < 8 & c = x..Node.subp.[i] & c ~= null) }"
	      from OtherChildren, ChildrenDefRCInv, SubpNotNode, ThisMInj,
	      SubpInj, MProps, ThisNonNull;
	    */
	    /*: noteThat ChildrenLemma: "theinv ChildrenDefRCInv"
	      from NewThisChildren, OtherChildren, MChildren, ChildrenLemma;
	    */

	    /*: noteThat SubtreeThis:
	      "subtree =
	      { s. (EX c. (c : children & s : c..Node.subtree))}"
	      from SubtreeThis, SubtreeDefRCThis, MNotEq, NInThis, MNotChild,
	      NNotM, ThisNotM;
	    */
	    /*: noteThat SubtreeOther: 
	      "ALL x. x : Object.alloc & x : Node & x ~= m & x ~= this &
	      ~x..Node.isBody & x..Node.init --> 
	      x..Node.subtree = 
	      { s. (EX c. (c : x..Node.children & s : c..Node.subtree))}"
	      from SubtreeOther, SubtreeDefRCOther, SubpNotNode, MNotAnyChild,
	      NNotM;
	    */
	    /*: noteThat SubtreeExceptN: 
	      "ALL x. x : Object.alloc & x : Node & x ~= m &
	      ~x..Node.isBody & x..Node.init --> 
	      x..Node.subtree = 
	      { s. (EX c. (c : x..Node.children & s : c..Node.subtree))}"
	      from SubtreeOther, SubtreeThis, SubtreeExceptN;
	    */
	    /*: noteThat ChildrenInjLemma: "theinv ChildrenInjInv"
	      from ChildrenInjLemma, ChildrenInjInv, ThisNotM, NNotM,
	      ThisSubpMInj, MNotAnyChild, SubpNotNode;
	    */
	    /*: noteThat NotPointedToBefore:
	    "(ALL x. (x : (old Object.alloc) & x ~= null &
	    (ALL y i. (arrayRead (old Array.arrayState) 
	    (fieldRead (old Node.subp) y) i) ~= x)) -->
	    (ALL z j. z..Node.subp.[j] ~= x))";
	    */
	    m.loadTree(toLoad);
	    
	    /*: noteThat NotPointedToAfter:
	    "(ALL x. (x : (old Object.alloc) & x ~= null & x ~= toLoad &
	    (ALL y i. (arrayRead (old Array.arrayState) 
	    (fieldRead (old Node.subp) y) i) ~= x)) -->
	    (ALL z j. z..Node.subp.[j] ~= x))"
	    from NotPointedToBefore, NotPointedToAfter, NotPointedToPost, 
	    ThisNotM, ThisMInj;
	    */
	} else {
	    //: "n..Node.subtree" := "n..Node.subtree Un { toLoad }"
	    //: noteThat joca: "theinv ChildrenAdvInjInv";
	    n.loadTree(toLoad);
	}	    
    }
}
