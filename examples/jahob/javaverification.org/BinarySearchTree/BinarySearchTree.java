public final class Node {
   public /*: claimedby BinarySearchTree */ Node left;
   public /*: claimedby BinarySearchTree */ Node right;
   public /*: claimedby BinarySearchTree */ Node parent;
   public /*: claimedby BinarySearchTree */ int v;

   /*: public specvar subtree :: objset;
       public vardefs "subtree ==
        {n0. n0 ~= null & 
	 (rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) this n0)}";
   */
}

public class BinarySearchTree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == root..Node.subtree";
   
       invariant TreeInv: "tree [Node.left, Node.right]";
   
       invariant RootInv: "root = null | 
                           (ALL n. n..Node.left ~= root & n..Node.right ~= root)";
   
       invariant ContentInv: 
        "ALL x. x ~: content & x ~= null --> 
                    (x..Node.left = null & 
                     x..Node.right = null &
                     (ALL y. y..Node.left ~= x & y..Node.right ~= x))";

       invariant ParentInv:
         "ALL x y. Node.parent x = y -->
           ((x ~: content | x = root) --> y = null) &
 	   (x : content & x ~= root --> y ~= null &
                                        (y..Node.left = x | y..Node.right = x))";
       invariant LeftOrderingInv:
         "ALL x y. y : x..Node.left..Node.subtree --> y..Node.v < x..Node.v";

       invariant RightOrderingInv:
         "ALL x y. y : x..Node.right..Node.subtree --> y..Node.v >= x..Node.v";
   */

   public static void add(Node e)
      /*: 
	requires "e ~= null & e ~: content"
	modifies content, "Node.subtree"
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while /*: inv "((p = null & n = null) --> root = null) &
	             (p = null --> n = root) &
		     (p ~= null --> p : content) &
		     (n ~= null --> n : content) &
		     (p ~= null & wentLeft --> p..Node.left = n) &
		     (p ~= null & ~wentLeft --> p..Node.right = n) &
		     (comment ''WentLeftLInv''
		     (p ~= null & wentLeft --> e..Node.v < p..Node.v)) &
		     (comment ''WentRightLInv''
		     (p ~= null & ~wentLeft --> e..Node.v >= p..Node.v)) &
		     (comment ''LOrderLInv''
		     (ALL x. p : x..Node.left..Node.subtree & p ~= null & 
		             p ~= x --> e..Node.v < x..Node.v)) &
		     (comment ''ROrderLInv''
		     (ALL x. p : x..Node.right..Node.subtree & p ~= null &
		             p ~= x --> e..Node.v >= x..Node.v))"
	     */
	  (n != null) {
	  /*: noteThat LSubtree:
	    "ALL x. n : x..Node.left..Node.subtree & p ~= null & p ~= x -->
	            p : x..Node.left..Node.subtree";
	   */
	  /*: noteThat RSubtree:
	    "ALL x. n : x..Node.right..Node.subtree & p ~= null & p ~= x -->
	            p : x..Node.right..Node.subtree";
	   */
	  /*: noteThat RootNotInLeft:
	    "p = null --> (ALL x. n ~: x..Node.left..Node.subtree)";
	  */
	  /*: noteThat RootNotInRight:
	    "p = null --> (ALL x. n ~: x..Node.right..Node.subtree)";
	  */
	  /*: noteThat WentLeftSubtree:
	    "wentLeft --> n ~: p..Node.right..Node.subtree";
	  */
	  /*: noteThat WentRightSubtree:
	    "~wentLeft --> n ~: p..Node.left..Node.subtree";
	  */
	 p = n;
	 if (e.v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 e.parent = p;
	 //: noteThat PNonNull: "p ~= null";
	 //: noteThat PEDiff: "e ~= p";
	 //: noteThat SingletonSubtree: "e..Node.subtree = { e }";

	 if (wentLeft) {
            p.left = e;
	    //: noteThat WentLeft: "e..Node.v < p..Node.v";
	    //: noteThat ENotInROfP: "e ~: p..Node.right..Node.subtree";
	 } else {
            p.right = e;
	    //: noteThat WentRight: "e..Node.v >= p..Node.v";
	    //: noteThat ENotInLOfP: "e ~: p..Node.left..Node.subtree";	    
	 }
	 /*: noteThat SubtreeRelL0:
	   "ALL x y. y : x..Node.left..Node.subtree -->
	   (y : (fieldRead (old Node.subtree) (x..Node.left)) | y = e)";
	 */
	 /*: noteThat SubtreeRelL1:
	   "ALL x. e : x..Node.left..Node.subtree & x ~= p -->
	   p : fieldRead (old Node.subtree) (x..Node.left)";
	 */
	 /*: noteThat SubtreeRelR0:
	   "ALL x y. y : x..Node.right..Node.subtree -->
	   (y : (fieldRead (old Node.subtree) (x..Node.right)) | y = e)";
	 */
	 /*: noteThat SubtreeRelR1:
	   "ALL x. e : x..Node.right..Node.subtree & x ~= p -->
	   p : fieldRead (old Node.subtree) (x..Node.right)";
	 */
      }
   }

   public static boolean contains(Node n)
   /*: requires "n ~= null"
       ensures "result = (n : content)"
    */
   {
       Node curr = root;

       while /*: inv "(curr ~= null --> curr : content) &
	              (comment ''InContentLInv''
		      (n : content) = (n : curr..Node.subtree))"
	      */
	   (curr != null) {
	   if (curr == n) {
	       return true;
	   } else {
	       /*: noteThat SubtreeDef:
		 "(n : curr..Node.subtree) = 
		 ((n = curr) | (n : curr..Node.left..Node.subtree) | 
		 (n : curr..Node.right..Node.subtree))";
	       */
	       if (n.v < curr.v) {
		   curr = curr.left;
	       } else {
		   curr = curr.right;
	       }
	   }
       }
       return false;
   }

   public static Node extractMax()
   /*: modifies content, "Node.subtree"
       ensures "(result = null --> (ALL x. (x ~: content))) &
                (result ~= null --> content = old content - {result}) &
		(result ~= null -->
		(ALL x. x : old content --> result..Node.v >= x..Node.v))"
    */
   {
       //: private static ghost specvar smaller :: objset;
       Node curr = root;

       //: smaller := "{}";
       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root) &
		      (content = smaller Un curr..Node.subtree) &
		      (comment ''SmallerLInv''
		      (ALL x. x : smaller --> curr..Node.v >= x..Node.v))"
	     */
	   (curr != null && curr.right != null) {
	   //: smaller := "smaller Un {curr} Un curr..Node.left..Node.subtree";
	   /*: noteThat SubtreeRRel: 
	     "curr..Node.right : curr..Node.right..Node.subtree";
	   */
	   curr = curr.right;
	   /*: noteThat SmallerLemma:
	     "ALL x. x : smaller --> curr..Node.v >= x..Node.v"
	     from SmallerLemma, SmallerLInv, SubtreeRRel, LeftOrderingInv,
	     RightOrderingInv;
	   */
       }

       /*: noteThat CurrEq: "curr..Node.v >= curr..Node.v";
	*/
       /*: noteThat CurrRight: "ALL x. x ~: curr..Node.right..Node.subtree";
	*/
       /*: noteThat SubtreeDef:
	 "curr ~= null --> 
	 curr..Node.subtree = { curr } Un curr..Node.left..Node.subtree Un
	 curr..Node.right..Node.subtree";
	*/
       /*: noteThat Smallest:
	 "curr ~= null --> (ALL x. x : content --> curr..Node.v >= x..Node.v)";
       */

       if (curr != null) {
	   remove_int(curr);
	   //: noteThat NodeUnchanged: "Node.v = old Node.v";
	   /*: noteThat OrderingEnd:
	     "ALL x. x : old content --> curr..Node.v >= x..Node.v"
	     from Smallest, TrueBranch, OrderingEnd, NodeUnchanged;
	   */
       }

       return curr;
   }

   public static Node extractMin()
   /*: modifies content, "Node.subtree"
       ensures "(result = null --> (ALL x. (x ~: content))) &
                (result ~= null --> content = old content - {result}) &
		(result ~= null -->
		(ALL x. x : old content --> result..Node.v <= x..Node.v))"
    */
   {
       //: private static ghost specvar bigger :: objset;
       Node curr = root;

       //: bigger := "{}";
       while /*: inv "(curr ~= null --> curr : content) &
	              (curr = null --> curr = root) &
		      (content = bigger Un curr..Node.subtree) &
		      (comment ''BiggerLInv''
		      (ALL x. x : bigger --> curr..Node.v <= x..Node.v))"
	      */
	   (curr != null && curr.left != null) {
	   //: bigger := "bigger Un {curr} Un curr..Node.right..Node.subtree";
	   /*: noteThat SubtreeLRel:
	     "curr..Node.left : curr..Node.left..Node.subtree";
	   */
	   curr = curr.left;
	   /*: noteThat BiggerLemma:
	     "ALL x. x : bigger --> curr..Node.v <= x..Node.v"
	     from BiggerLemma, BiggerLInv, SubtreeLRel, RightOrderingInv,
	     LeftOrderingInv;
	   */
       }
       //: noteThat CurrEq: "curr..Node.v <= curr..Node.v";
       //: noteThat CurrLeft: "ALL x. x ~: curr..Node.left..Node.subtree";
       /*: noteThat SubtreeDef:
	 "curr ~= null --> 
	 curr..Node.subtree = { curr } Un curr..Node.left..Node.subtree Un
	 curr..Node.right..Node.subtree";
	*/
       /*: noteThat Biggest:
	 "curr ~= null --> (ALL x. x : content --> curr..Node.v <= x..Node.v)";
       */

       if (curr != null) {
	   remove_int(curr);
	   //: noteThat NodeUnchanged: "Node.v = old Node.v";
	   /*: noteThat OrderingEnd:
	     "ALL x. x : old content --> curr..Node.v <= x..Node.v"
	     from Biggest, TrueBranch, OrderingEnd, NodeUnchanged;
	   */
       }

       return curr;
   }

   private static Node removeMin(Node n)
   /*: requires "theinvs & n ~= null & n : content & n..Node.right ~= null"
       modifies content, "Node.left", "Node.right", "Node.parent", 
                "Node.subtree"
       ensures "theinvs & content = old content - {result} & 
                result : old content & result ~= n &
		(ALL y. y : n..Node.left..Node.subtree --> 
		y..Node.v < result..Node.v) &
		(ALL y. y : n..Node.right..Node.subtree -->
		result..Node.v <= y..Node.v) &
		(ALL x. n : x..Node.left..Node.subtree -->
		result..Node.v < x..Node.v) &
		(ALL x. n : x..Node.right..Node.subtree -->
		x..Node.v <= result..Node.v) &
		Node.v = (old Node.v)"
   */
   {
       //: private static ghost specvar bigger :: objset;
       Node e = n.right;
       
       //: bigger := "{}";
       while /*: inv "e ~= null & e : content &
	              (rtrancl_pt 
		      (% x y. x..Node.left = y) (n..Node.right) e) &
		      (n..Node.right..Node.subtree = 
		      bigger Un e..Node.subtree) &
		      (comment ''BiggerLInv''
		      (ALL x. x : bigger --> e..Node.v < x..Node.v)) &
		      (e : n..Node.right..Node.subtree)"
	     */
	   (e.left != null) {
	   //: bigger := "bigger Un {e} Un e..Node.right..Node.subtree";
	   /*: noteThat SubtreeRRel:
	     "e..Node.left : e..Node.left..Node.subtree";
	   */
	   e = e.left;
	   /*: noteThat BiggerLemma:
	     "ALL x. x : bigger --> e..Node.v < x..Node.v"
	     from BiggerLemma, BiggerLInv, SubtreeRRel, LeftOrderingInv,
	     RightOrderingInv;
	   */
       }

       //: noteThat ELeft: "ALL x. x ~: e..Node.left..Node.subtree";
       /*: noteThat SubtreeDef:
	 "e ~= null --> 
	 e..Node.subtree = { e } Un e..Node.left..Node.subtree Un
	 e..Node.right..Node.subtree";
       */

       if (e.parent.left == e) {
	   e.parent.left = e.right;
       } else {
	   //: noteThat "e..Node.parent..Node.right = e";
	   e.parent.right = e.right;
       }

       if (e.right != null) {
	   e.right.parent = e.parent;
       }

       e.parent = null;
       e.right = null;

       /*: noteThat SubtreeChange: "ALL x y. y : x..Node.subtree & 
	 x ~= e & y ~= e --> y : (fieldRead (old Node.subtree) x)";
	*/
       //: noteThat EIsolated: "ALL x. x ~= e --> e ~: x..Node.subtree";
       //: noteThat ENoChildren: "e..Node.subtree = { e }";
       /*: noteThat ENRel:
	 "ALL x. n : x..Node.left..Node.subtree -->
	 e : (fieldRead (old Node.subtree) (fieldRead (old Node.left) x))";
       */
       return e;
   }

   private static Node removeMax(Node n)
   /*: requires "theinvs & n ~= null & n : content & n..Node.left ~= null"
       modifies content, "Node.left", "Node.right", "Node.parent", 
                "Node.subtree"
       ensures "theinvs & content = old content - {result} & 
                result : old content & result ~= n &
		(ALL x. x : n..Node.left..Node.subtree --> 
		x..Node.v <= result..Node.v) &
		(ALL x. x : n..Node.right..Node.subtree -->
		x..Node.v >= result..Node.v)"
   */
   {
       //: private static ghost specvar smaller :: objset;
       Node e = n.left;
       
       //: smaller := "{}";
       while /*: inv "e ~= null & e : content &
	              (rtrancl_pt 
		      (% x y. x..Node.right = y) (n..Node.left) e) &
		      (n..Node.left..Node.subtree = 
		      smaller Un e..Node.subtree) &
		      (comment ''SmallerLInv''
		      (ALL x. x : smaller --> e..Node.v >= x..Node.v)) &
		      (e : n..Node.left..Node.subtree)"
	     */
	   (e.right != null) {
	   //: smaller := "smaller Un {e} Un e..Node.left..Node.subtree";
	   /*: noteThat SubtreeRRel: 
	     "e..Node.right : e..Node.right..Node.subtree";
	   */
	   e = e.right;
	   /*: noteThat SmallerLemma:
	     "ALL x. x : smaller --> e..Node.v >= x..Node.v"
	     from SmallerLemma, SmallerLInv, SubtreeRRel, LeftOrderingInv,
	     RightOrderingInv;
	   */
       }

       //: noteThat ERight: "ALL x. x ~: e..Node.right..Node.subtree";
       /*: noteThat SubtreeDef:
	 "e ~= null --> 
	 e..Node.subtree = { e } Un e..Node.left..Node.subtree Un
	 e..Node.right..Node.subtree";
	*/

       if (e.parent.right == e) {
	   e.parent.right = e.left;
       } else {
	   e.parent.left = e.left;
       }

       if (e.left != null) {
	   e.left.parent = e.parent;
       }

       e.parent = null;
       e.left = null;

       /*: noteThat SubtreeChange: "ALL x y. y : x..Node.subtree & 
	 x ~= e & y ~= e --> y : (fieldRead (old Node.subtree) x)";
	*/
       //: noteThat EIsolated: "ALL x. x ~= e --> e ~: x..Node.subtree";
       //: noteThat ENoChildren: "e..Node.subtree = { e }";

       return e;
   }

   private static void swap(Node toRemove, Node toAdd)
   /*: requires "toRemove ~= null & toRemove : content & 
                 toAdd ~= null & toAdd ~: content &
		 (comment ''LOPreS''
		 (ALL x. x : toRemove..Node.left..Node.subtree -->
		 x..Node.v < toAdd..Node.v)) &
		 (comment ''ROPreS''
		 (ALL x. x : toRemove..Node.right..Node.subtree -->
		 toAdd..Node.v <= x..Node.v)) &
		 (comment ''LOPreR''
		 (ALL x. toRemove : x..Node.left..Node.subtree -->
		 toAdd..Node.v < x..Node.v)) &
		 (comment ''ROPreR''
		 (ALL x. toRemove : x..Node.right..Node.subtree -->
		 x..Node.v <= toAdd..Node.v)) & theinvs"
       modifies content, root, "Node.subtree", "Node.parent", "Node.right",
                "Node.left"
       ensures "content = old content - {toRemove} Un {toAdd} &
                Node.v = (old Node.v) & theinvs"
   */
  {
       //: noteThat toAddIsolatedL: "ALL x. x..Node.left ~= toAdd";
       //: noteThat toAddIsolatedR: "ALL x. x..Node.right ~= toAdd";

       if (toRemove.parent == null) {
	   //: noteThat "root = toRemove";
	   root = toAdd;
       } else {
	   //: noteThat HasParent: "toRemove..Node.parent ~= null";
	   if (toRemove.parent.left == toRemove) {
	       /*: noteThat toRemoveID:
		 "toRemove..Node.parent..Node.left = toRemove";
	       */
	       toRemove.parent.left = toAdd;
	   } else {
	       /*: noteThat toRemoveID:
		 "toRemove..Node.parent..Node.right = toRemove";
	       */
	       toRemove.parent.right = toAdd;
	   }
       }

       toAdd.parent = toRemove.parent;
       toRemove.parent = null;
	   
       toAdd.left = toRemove.left;
       toRemove.left = null;

       toAdd.right = toRemove.right;
       toRemove.right = null;

       if (toAdd.left != null) {
	   toAdd.left.parent = toAdd;
       }

       if (toAdd.right != null) {
	   toAdd.right.parent = toAdd;
       }

       /*: noteThat toRemoveSubtree:
	 "toRemove..Node.subtree = { toRemove }";
       */
       /*: noteThat LORemovedR: 
	 "ALL y. y : toRemove..Node.left..Node.subtree --> 
	 y..Node.v < toRemove..Node.v";
       */
       /*: noteThat RORemovedR:
	 "ALL y. y : toRemove..Node.right..Node.subtree -->
	 toRemove..Node.v <= y..Node.v";
       */
       /*: noteThat LORemovedS:
	 "ALL x. toRemove : x..Node.left..Node.subtree -->
	 toRemove..Node.v < x..Node.v";
       */
       /*: noteThat RORemovedS:
	 "ALL x. toRemove : x..Node.right..Node.subtree -->
	 x..Node.v <= toRemove..Node.v";
       */
       /*: noteThat SubtreeChange: 
	 "ALL x y. y : x..Node.subtree & x ~= toAdd & y ~= toAdd --> 
	 y : (fieldRead (old Node.subtree) x)";
       */
       /*: noteThat SubtreeSwapL:
	 "toAdd..Node.left..Node.subtree = 
	 (fieldRead (old Node.subtree) (fieldRead (old Node.left) toRemove))";
       */
       /*: noteThat SubtreeSwapR:
	 "toAdd..Node.right..Node.subtree = 
	 (fieldRead (old Node.subtree) (fieldRead (old Node.right) toRemove))";
       */
       /*: noteThat SubtreeSwapPL:
	 "ALL x. toAdd : x..Node.left..Node.subtree -->
	 toRemove : 
	 (fieldRead (old Node.subtree) (fieldRead (old Node.left) x))"
       */
       /*: noteThat SubtreeSwapPR:
	 "ALL x. toAdd : x..Node.right..Node.subtree -->
	 toRemove : 
	 (fieldRead (old Node.subtree) (fieldRead (old Node.right) x))";
       */
       /*: noteThat LOSwappedR:
	 "ALL y. y : toAdd..Node.left..Node.subtree -->
	 y..Node.v < toAdd..Node.v";
       */
       /*: noteThat LOSwappedS:
	 "ALL x. toAdd : x..Node.left..Node.subtree -->
	 toAdd..Node.v < x..Node.v"
	 from LOSwappedS, HasParent, LOPreR, SubtreeSwapPL;
       */
       //: noteThat NEq: "toAdd ~= toRemove";
       /*: noteThat SwappedSubtree:
	 "ALL x. x : toAdd..Node.subtree & x ~= toAdd -->
	 x : fieldRead (old Node.subtree) toRemove";
       */
       /*: noteThat LOPart:
	 "ALL x y. y : x..Node.left..Node.subtree & x ~= toAdd & y ~= toAdd &
	 x ~= toRemove & y ~= toRemove --> y..Node.v < x..Node.v"
	 from LOPart, LeftOrderingInv, SubtreeChange, NEq, toAddIsolatedL,
	 toRemoveID, SwappedSubtree;
       */
       /*: noteThat LOEnd: "theinv LeftOrderingInv"
	 from LOEnd, LOPart, LORemovedR, LOSwappedR, LORemovedS, LOSwappedS, 
	 NEq;
       */
       /*: noteThat ROSwappedR:
	 "ALL y. y : toAdd..Node.right..Node.subtree -->
	 toAdd..Node.v <= y..Node.v";
       */
       /*: noteThat ROSwappedS:
	 "ALL x. toAdd : x..Node.right..Node.subtree -->
	 x..Node.v <= toAdd..Node.v";
       */
       /*: noteThat ROPart:
	 "ALL x y. y : x..Node.right..Node.subtree & x ~= toAdd & y ~= toAdd &
	 x ~= toRemove & y ~= toRemove --> x..Node.v <= y..Node.v"
	 from ROPart, RightOrderingInv, SubtreeChange, NEq, toAddIsolatedR,
	 toRemoveID, SwappedSubtree;
       */
       /*: noteThat ROEnd: "theinv RightOrderingInv"
	 from ROEnd, ROPart, RORemovedR, ROSwappedR, RORemovedS, ROSwappedS, 
	 NEq;
       */
   }

   public static void remove(Node e)
   /*: requires "e ~= null & e : content"
       modifies content, "Node.subtree", "Node.parent", "Node.right", 
                "Node.left"
       ensures "(content = old content - {e}) & Node.v = (old Node.v)"
    */ 
   {
       remove_int(e);
   }
   
   private static void remove_int(Node e)
   /*: requires "e ~= null & e : content & theinvs"
       modifies content, "Node.subtree", root, "Node.parent", "Node.right",
                "Node.left"
       ensures "(content = old content - {e}) & Node.v = (old Node.v) & theinvs"
    */
   {
       if (e.left == null) {
	   if (e.right == null) {
	       // e has no children
	       if (e.parent == null) {
		   // e is the root node
		   root = null;
	       } else if (e.parent.left == e) {
		   // e is a left child
		   e.parent.left = null;
	       } else {
		   // e is a right child
		   e.parent.right = null;
	       }
	   } else {
	       // e has a right child but no left child
	       if (e.parent == null) {
		   // e is the root node
		   root = e.right;
	       } else {
		   if (e.parent.left == e) {
		       // e is a left child
		       e.parent.left = e.right;
		   } else {
		       // e is a right child
		       e.parent.right = e.right;
		   }
	       }
	       e.right.parent = e.parent;
	       e.right = null;
	   }
           e.parent = null;
	   //: noteThat LOESubtree: "e..Node.subtree = { e }";
	   //: noteThat EIsolated: "ALL x. x ~= e --> e ~: x..Node.subtree";
	   //: noteThat ENotLeft: "ALL x. x..Node.left ~= e";
	   //: noteThat ENotRight: "ALL x. x..Node.right ~= e";
	   //: noteThat ENoParent: "e..Node.parent = null";
	   /*: noteThat SubtreeChangeL:
	     "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
	     y : (fieldRead (old Node.subtree) (fieldRead (old Node.left) x))";
	    */
	   /*: noteThat LOPart: 
	     "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
	     y..Node.v < x..Node.v";
	   */
	   /*: noteThat LOEnd: "theinv LeftOrderingInv"
	     from LOEnd, LOPart, EIsolated, ENotLeft, ENoParent;
	   */
	   /*: noteThat SubtreeChangeR:
	     "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
	     y : 
	     (fieldRead (old Node.subtree) (fieldRead (old Node.right) x))";
	    */
	   /*: noteThat ROPart:
	     "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
	     x..Node.v <= y..Node.v";
	   */
	   /*: noteThat ROEnd: "theinv RightOrderingInv"
	     from ROEnd, ROPart, EIsolated, ENotRight, ENoParent;
	   */
	   //: noteThat LOESubtree: "e..Node.subtree = { e }";
	   //: noteThat EIsolated: "ALL x. x ~= e --> e ~: x..Node.subtree";
	   //: noteThat ENotLeft: "ALL x. x..Node.left ~= e";
	   //: noteThat ENotRight: "ALL x. x..Node.right ~= e";
	   //: noteThat ENoParent: "e..Node.parent = null";
	   /*: noteThat SubtreeChangeL:
	     "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
	     y : (fieldRead (old Node.subtree) (fieldRead (old Node.left) x))";
	    */
	   /*: noteThat LOPart: 
	     "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
	     y..Node.v < x..Node.v";
	   */
	   /*: noteThat LOEnd: "theinv LeftOrderingInv"
	     from LOEnd, LOPart, EIsolated, ENotLeft, ENoParent;
	   */
	   /*: noteThat SubtreeChangeR:
	     "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
	     y : 
	     (fieldRead (old Node.subtree) (fieldRead (old Node.right) x))";
	    */
	   /*: noteThat ROPart:
	     "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
	     x..Node.v <= y..Node.v";
	   */
	   /*: noteThat ROEnd: "theinv RightOrderingInv"
	     from ROEnd, ROPart, EIsolated, ENotRight, ENoParent;
	   */
       } else {
	   if (e.right == null) {
	       // e has a left child but no right child
	       if (e.parent == null) {
		   // e is the root node
		   root = e.left;
	       } else {
		   if (e.parent.left == e) {
		       // e is a left child
		       e.parent.left = e.left;
		   } else {
		       // e is a right child
		       e.parent.right = e.left;
		   }
	       }
	       e.left.parent = e.parent;
	       e.left = null;
               e.parent = null;
	       //: noteThat LOESubtree: "e..Node.subtree = { e }";
	       /*: noteThat EIsolated: 
		 "ALL x. x ~= e --> e ~: x..Node.subtree";
	       */
	       //: noteThat ENotLeft: "ALL x. x..Node.left ~= e";
	       //: noteThat ENotRight: "ALL x. x..Node.right ~= e";
	       //: noteThat ENoParent: "e..Node.parent = null";
	       /*: noteThat SubtreeChangeL:
		 "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
		 y : 
		 (fieldRead (old Node.subtree) (fieldRead (old Node.left) x))";
	       */
	       /*: noteThat LOPart: 
		 "ALL x y. y : x..Node.left..Node.subtree & y ~= e -->
		 y..Node.v < x..Node.v";
	       */
	       /*: noteThat LOEnd: "theinv LeftOrderingInv"
		 from LOEnd, LOPart, EIsolated, ENotLeft, ENoParent;
	       */
	       /*: noteThat SubtreeChangeR:
		 "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
		 y : (fieldRead (old Node.subtree) 
		 (fieldRead (old Node.right) x))";
	       */
	       /*: noteThat ROPart:
		 "ALL x y. y : x..Node.right..Node.subtree & y ~= e -->
		 x..Node.v <= y..Node.v";
	       */
	       /*: noteThat ROEnd: "theinv RightOrderingInv"
		 from ROEnd, ROPart, EIsolated, ENotRight, ENoParent;
	       */
	   } else {
	       // e has both a left and a right child
               Node r = removeMin(e);
               swap(e, r);
	   }
       }
   }
}
 
