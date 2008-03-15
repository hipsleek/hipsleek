class Node {
    public /*: claimedby CircularList */ Node next;
    public /*: claimedby CircularList */ Node prev;
}

class CircularList
{
    private static Node first;
    private static Node last;
  
   /*:
     private static ghost specvar next1 :: "obj => obj" = "(% x. null)";

     public static specvar content :: objset;
     vardefs "content == {x. x ~= null & (first,x) : {(v,w). v..next1=w}^*}";

     private static specvar isLast :: "obj => bool";
     vardefs "isLast == (% x. (first,x) : {(v,w). v..next1=w}^* & 
                              x ~=null & x..next1 = null)";
     invariant lastIsLast: "first ~= null --> isLast last";

     invariant firstIsolated: "first ~= null --> (ALL n. n..next1 ~= first)";
     
     invariant isTree: "tree [next1]";

     invariant nextDef: "ALL x y. next x = y --> 
         ((x = last --> y = first) & 
	  (x : content & x ~= last --> y = x..next1) &
	  (x ~: content --> y=null))"

     invariant prevDef: "ALL x y. prev x = y --> 
         ((x ~: content --> y = null) &
	  (x = first & first ~= null --> y = last) & 
	  (x : content & x ~= first --> y..next1 = x))"

     invariant nextNeverNull: "ALL x. x : content --> x..next ~= null";
     invariant prevNeverNull: "ALL x. x : content --> x..prev ~= null";

     invariant next1isolated: "ALL n. n ~= null & n ~: content --> isolated n";
     private static specvar isolated :: "obj => bool";
     vardefs "isolated == (%n. n..next1 = null & (ALL x. x ~= null --> x..next1 ~= n))";
   */

    public static void add(Node n)
    /*: requires "n ~: content & n ~= null & n..next = null & (ALL x. x..next ~= n)"
        modifies content
        ensures "content = old content Un {n}"
    */
    {
	if (first==null) {
	    first = n;
	    n.next = n;
	    n.prev = n;
	    last = n;
	    //: "n..next1" := "null";
	} else {
	    if (first.next==first) {
		last = n;
	    }
	    n.next = first.next;
	    first.next.prev = n;
	    //: "n..next1" := "first..next1";
	    first.next = n;
	    n.prev = first;
	    //: "first..next1" := "n";	    
	}
	//: noteThat inserted: "content = old content Un {n}";
    }

    public static void remove(Node n)
    /*: requires "n : content"
        modifies content
        ensures "comment ''removePost'' (content = old content - {n})"
    */
    {
	//: noteThat "first ~= null";
	//: noteThat "n ~= null";
	if (first.next==first) {
	    //: noteThat lone: "n = first";
	    first = null;
	    n.next = null;
	    n.prev = null;	    
	} else {
	    Node nxt = n.next;
	    Node prv = n.prev;
	    prv.next = nxt;
	    nxt.prev = prv;
	    n.next = null;
	    n.prev = null;
	    //: "n..next1" := "null";
	    if (n==first) {
		first = nxt;
	    } else {
		if (n==last) {
		    //: "prv..next1" := "null";
		    //: "last" := "prv";
		} else {
		    //: "prv..next1" := "nxt";
		}
	    }
	}
    }
}
