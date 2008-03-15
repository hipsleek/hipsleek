public /*: claimedby Hashtable */ class Node {
    public /*: claimedby Hashtable */ Object key;
    public /*: claimedby Hashtable */ Object value;
    public /*: claimedby Hashtable */ Node next;
    /*: 
      public ghost specvar con :: "(obj * obj) set" = "({} :: (obj * obj) set)";
    */
}

class Hashtable {
    private static Node[] table = null;

    /*: 
     public static ghost specvar content :: "(obj * obj) set" = "{}";
     public static ghost specvar init :: "bool" = "False :: bool";

     private static ghost specvar h :: "(obj => int => int)";

     invariant ContentDefInv:
     "init --> 
      content = 
      {(k, v). (k, v) : table.[(h k (table..Array.length))]..Node.con}";

     public ensured invariant ContentAlloc:
     "ALL x y. 
      (x, y) : content --> (x : Object.alloc & y : Object.alloc)";

     invariant TableNotNull: "init --> table ~= null";
     invariant TableHidden: "init --> table : hidden";
     invariant AllocInv: "table : Object.alloc";

     invariant NodeHidden: 
     "init -->(ALL x. x : Object.alloc & x : Node --> x : hidden)";

     invariant HashInv:
     "init --> (ALL k. 0 <= (h k (table..Array.length)) & 
               (h k (table..Array.length)) < table..Array.length)";

     invariant ElementAllocInv:
       "ALL i. 
         0 <= i & i < table..Array.length --> table.[i] : Object.alloc";

     invariant FirstInjInv:
       "init --> 
        (ALL i x y. y = x..Node.next & y ~= null & 0 <= i &
	i < table..Array.length --> y ~= table.[i])";

     invariant NextInjInv:
       "ALL x1 x2 y. 
         y ~= null & y = x1..Node.next & y = x2..Node.next --> x1 = x2";

     invariant ElementInjInv:
       "init --> (ALL i j.
	  ((0 <= i & i < table..Array.length & 
	    0 <= j & j < table..Array.length & 
	    table.[i] ~= null & table.[i] = table.[j]) --> i = j))";

     invariant ElementTypeInv:
       "ALL i. 0 <= i & i < table..Array.length --> table.[i] : Node";

     public ensured invariant SetInv:
       "ALL k v0 v1. (k, v0) : content & (k, v1) : content --> v0 = v1";

     public ensured invariant NonNullInv:
       "ALL k v. (k, v) : content --> k ~= null & v ~= null";

     invariant Coherence: "init --> 
       (ALL i k v. 0 <= i & i < table..Array.length --> 
       (k,v) : table.[i]..Node.con --> h k (table..Array.length) = i)";

     invariant ConAlloc:
       "ALL z x y. z : Node & z : Object.alloc & (x, y) : z..Node.con -->
        x : Object.alloc & y : Object.alloc";

     invariant ConNull:
       "ALL x. x : Node & x : Object.alloc & x = null --> x..Node.con = {}";

     invariant ConDef:
       "ALL x. x : Node & x : Object.alloc & x ~= null -->
          x..Node.con = 
	  {(x..Node.key, x..Node.value)} Un x..Node.next..Node.con &
	  (ALL v. (x..Node.key, v) ~: x..Node.next..Node.con)";

     invariant ConNonNull:
       "ALL z x y. z : Node & z : Object.alloc & z ~= null & 
       (x, y) : z..Node.con --> x ~= null & y ~= null";

    */

    public static void init(int n)
    /*: 
      modifies content, init
      ensures "init & content = {}"
    */
    {
	int i = 0;
	//: "init" := "False";
	table = new /*: hidden */ Node[n];
	
	while /*: inv "(ALL j. 0 <= j & j < i --> table.[j] = null) &
		       (ALL a i. (a : Object.alloc & a : Array & a ~: hidden) -->
		        (a.[i] = (arrayRead (old Array.arrayState) a i))) &
		       null..Node.con = {}";
	       */
	    (i < n) {
	    table[i] = null;
	}
	//: "content" := "{}";
	//: "init" := "True";

	//: assume "theinv HashInv";
    }

    private static int compute_hash(Object o1)
    /*: requires "o1 ~= null & init & theinvs"
        ensures "result = h o1 (table..Array.length) & 0 <= result & 
	         result < table..Array.length &
		 Object.alloc = (old Object.alloc) & theinvs"
    */
    {
	int result = o1.hashCode() % table.length;
	//: assume "result = h o1 (table..Array.length)";
	//: assume "Object.alloc = (old Object.alloc)";
	return result;
    }

    public static boolean containsKey(Object k0)
    /*: requires "init"
        ensures "result = (EX v. ((k0, v) : content))"
     */
    {
        return containsKey0(k0);
    }

    private static boolean containsKey0(Object k0)
    /*: requires "init & theinvs"
        ensures "result = (EX v. ((k0, v) : content)) & theinvs"
    */
    {
	int hc = compute_hash(k0);
	boolean res = bucketContainsKey(hc, k0);
	return res;
    }
    
    private static boolean bucketContainsKey(int bucket_id, Object k0)
    /*: requires "init & theinvs & 0 <= bucket_id & 
                  bucket_id < table..Array.length"
	ensures "result = (EX v. ((k0, v) : table.[bucket_id]..Node.con)) & 
	         theinvs"
     */
    {
        Node current = table[bucket_id];
        while /*: inv "current : Node & current : Object.alloc & theinvs &
		       (EX v. (k0, v) : table.[bucket_id]..Node.con) = 
		       (EX v. (k0, v) : current..Node.con)"
	       */
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public static Object remove(Object k0)
    /*: requires "init & k0 ~= null & (EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content \<setminus> {(k0, result)} &
	         (k0, result) : old content"
    */
    {
	/*: private ghost specvar v0 :: obj;
	 */
	//: havoc v0;
	//: assume "(k0, v0) : content";
	int hc = compute_hash(k0);
	Node f = table[hc];
	//: noteThat KeyInBucket: "(k0, v0) : table.[hc]..Node.con";
	//: noteThat HProps: "hc = h k0 (table..Array.length)";
	//: noteThat FProps: "f : Node & f : old Object.alloc";
	/*: noteThat FNonNull: "f ~= null" 
	  from FProps, KeyInBucket, ConNull, FNonNull;
	*/
	//: noteThat Init: "init";
	if (f.key == k0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..Node.con" := "{(f..Node.key, f..Node.value)}";
	    table[hc] = second;
	    //: "content" := "old content \<setminus> {(k0, v0)}";

	    //: noteThat HCProps: "0 <= hc & hc < table..Array.length";
	    /*: noteThat Acyclic:
	      "fieldRead (old Node.next) 
	      (arrayRead (old Array.arrayState) table hc) ~=
	      (arrayRead (old Array.arrayState) table hc)"
	      from Init, FNonNull, HCProps, FirstInjInv, Acyclic;
	    */
	    //: noteThat KFound: "f..Node.key = k0";
	    //: noteThat VFound: "f..Node.value = v0";
	    /*: noteThat NewContentDef: "theinv ContentDefInv"
	      from ContentDefInv, Acyclic, ConDef, ElementInjInv, FProps, 
	      FNonNull, KFound, VFound, HashInv, HCProps, HProps, 
	      NewContentDef;
	    */

	    //: noteThat AllocUnchanged: "Object.alloc = old Object.alloc";
	    /*: noteThat FNotRefByNext: "ALL x. x..Node.next ~= f"
	      from FNotRefByNext, FirstInjInv, Init, FNonNull, HCProps;
	    */
	    //: noteThat NullNode: "null : Node";
	    //: noteThat NullAlloc: "null : Object.alloc";
	    /*: noteThat NewConDef: "theinv ConDef"
	      from ConDef, AllocUnchanged, ConNull, ElementAllocInv,
	      ElementTypeInv, FNotRefByNext, HCProps, NullNode, NullAlloc,
	      NewConDef;
	     */

	    //: noteThat NextNull: "(old Node.next) null = null";
	    /*: noteThat NewCoherence: "theinv Coherence"
	      from Coherence, Acyclic, ConDef, ConNull, NextNull, 
	      ElementAllocInv, ElementTypeInv, NewCoherence;
	     */

	    /*: noteThat FirstInjLemma: "theinv FirstInjInv"
	      from FirstInjInv, NextInjInv;
	    */
	    /*: noteThat ElementInjLemma: "theinv ElementInjInv"
	      from ElementInjInv, FirstInjInvProcedurePrecondition;
	    */
	    return f.value;
	} else {
	    Node prev = f;
	    /*: "prev..Node.con" := 
	        "prev..Node.con \<setminus> {(k0, v0)}";
	    */
	    //: "content" := "old content \<setminus> {(k0, v0)}";
	    Node current = prev.next;
	    while /*: inv "
		    prev : Node & prev : Object.alloc & prev ~= null &
		    prev..Node.con = 
		     fieldRead (old Node.con) prev \<setminus> {(k0, v0)} &
		    current : Node & current : Object.alloc & current ~= null &
		    prev..Node.next = current & prev ~= current &
		    content = old content \<setminus> {(k0, v0)} &
		    (k0, v0) : current..Node.con &
		    comment ''ConDefInv''
		    (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
		    n..Node.con = {(n..Node.key, n..Node.value)} Un n..Node.next..Node.con &
		    (ALL v. (n..Node.key, v) ~: n..Node.next..Node.con)) &
		    (ALL n. n..Node.con = old (n..Node.con) |
		    n..Node.con = old (n..Node.con) \<setminus> {(k0, v0)}) &
		    null..Node.con = {} &
		    comment ''FConInv'' (f..Node.con = 
		    (fieldRead (old Node.con) f) \<setminus> {(k0, v0)})"
		  */
		(current.key != k0)
                {
                    /*: "current..Node.con" := 
		      "current..Node.con \<setminus> {(k0, v0)}"; */
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..Node.con" := "{(current..Node.key, current..Node.value)}";

	    //: noteThat "theinv FirstInjInv";

	    //: noteThat NullNotCurrent: "null ~= current";
	    //: noteThat ConOfNull: "null..Node.con = {}";
	    /*: noteThat NextNotCurr:
	      "ALL x. x ~= prev --> fieldRead (old Node.next) x ~= current";
	    */
	    /*: noteThat UpdatedConDef:
	      "(ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
	       n..Node.con = 
	       {(n..Node.key, n..Node.value)} Un n..Node.next..Node.con &
	       (ALL v. (n..Node.key, v) ~: n..Node.next..Node.con))"
	       from ConDefInv, NullNotCurrent, ConOfNull, NextNotCurr,
	       UpdatedConDef;
	    */

	    //: noteThat NextOfNull: "fieldRead (old Node.next) null = null";
	    //: noteThat PrevNotCurr: "prev ~= current";
	    /*: noteThat CurrNextNotCurr: 
	      "fieldRead (old Node.next) current ~= current";
	     */
	    /*: noteThat KeyNotInRest:
	      "(k0, v0) ~: fieldRead (old Node.con) 
	                    (fieldRead (old Node.next) current)";
	     */
	    //: noteThat PrevNotKey: "prev..Node.key ~= k0";
	    /*: noteThat OldCurrConDef: 
	      "fieldRead (old Node.con) current = 
	      {(k0, v0)} Un 
	      (fieldRead (old Node.con) (fieldRead (old Node.next) current))";
	     */
	    /*: noteThat OldPrevConIs:
	      "fieldRead (old Node.con) prev =
	      {(prev..Node.key, prev..Node.value)} Un
	      (fieldRead (old Node.con) current)";
	     */
	    /*: noteThat PrevConUpdate:
	      "prev..Node.con = 
	      (fieldRead (old Node.con) prev) \<setminus> {(k0, v0)}";
	    */
	    /*: noteThat ConEitherOr:
	      "(fieldRead Node.con (fieldRead (old Node.next) current) =
	       fieldRead (old Node.con) (fieldRead (old Node.next) current)) |
	       (fieldRead Node.con (fieldRead (old Node.next) current) =
	       ((fieldRead (old Node.con) (fieldRead (old Node.next) current))
	       \<setminus> {(k0, v0)}))";
	    */
	    /*: noteThat PrevConADef:
	      "prev..Node.con = 
	       {(prev..Node.key, prev..Node.value)} Un 
	       prev..Node.next..Node.con"
	       from NullNotCurrent, NextOfNull, PrevNotCurr, CurrNextNotCurr,
	       KeyNotInRest, PrevNotKey, OldCurrConDef, OldPrevConIs, 
	       PrevConUpdate, ConEitherOr, PrevConADef;
	    */
	    /*: noteThat PrevKeyNotInRest:
	      "ALL v. (prev..Node.key, v) ~: 
	      fieldRead (old Node.con) (fieldRead (old Node.next) current)";
	     */
	    /*: noteThat PrevConBDef:
	      "(ALL v. (prev..Node.key, v) ~: prev..Node.next..Node.con)"
	      from PrevNotCurr, CurrNextNotCurr, ConEitherOr, KeyNotInRest,
	      PrevKeyNotInRest, PrevConBDef;
	    */
	    /*: noteThat PrevConDef:
	      "prev..Node.con = 
	       {(prev..Node.key, prev..Node.value)} Un 
	        prev..Node.next..Node.con &
	       (ALL v. (prev..Node.key, v) ~: prev..Node.next..Node.con)"
	       from PrevConADef, PrevConBDef, PrevConDef;
	     */
	    /*: noteThat NewConDef: "theinv ConDef"
	      from UpdatedConDef, PrevConDef, NewConDef;
	     */

	    /*: noteThat CurrentNext:
	      "current = fieldRead (old Node.next) prev";
	    */
	    //: noteThat CurrentNotNull: "current ~= null";
	    /*: noteThat NotFirstAlt: 
	      "ALL k. current ~= table.[(h k (table..Array.length))]"
	      from FirstInjInv, CurrentNext, CurrentNotNull, Init, HashInv,
	      NotFirstAlt;
	     */
	    /*: noteThat ConLInv: "ALL n. n ~= current --> 
	           (n..Node.con = old (n..Node.con) |
	            n..Node.con = old (n..Node.con) \<setminus> {(k0, v0)})"
	     */
	    //: noteThat KCurrent: "current..Node.key = k0";
	    //: noteThat VCurrent: "current..Node.value = v0";
	    //: noteThat NotFirstThisBucket: "table.[hc] ~= current";
	    /*: noteThat FConLemma: 
	      "f..Node.con = 
	       (fieldRead (old Node.con) f) \<setminus> {(k0, v0)}"
	       from FConInv, NotFirstThisBucket, FConLemma;
	     */
	    /*: noteThat OtherBucketsK: 
	          "ALL k. h k (table..Array.length) ~= hc --> 
		    k ~= current..Node.key";
	    */
	    /*: noteThat FBContentDef: "theinv ContentDefInv"
	      from ContentDefInv, KCurrent, VCurrent, ConLInv, NotFirstAlt, 
	      HashInv, FConLemma, HProps, OtherBucketsK, FBContentDef;
	    */
	    return current.value;
	}
    }

    public static void add(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & 
                  ~(EX v. (k0, v) : content)"
        modifies content
        ensures "content = old content Un {(k0, v0)}"
    */
    {
	int hc = compute_hash(k0);
	Node n = new /*: hidden */ Node();
	n.key = k0;
	n.value = v0;
	Node first = table[hc];
	n.next = first;
	//: "n..Node.con" := "{(k0, v0)} Un first..Node.con";
	table[hc] = n;
	//: "content" := "(old content) Un {(k0, v0)}";

	//: noteThat Init: "init";
	//: noteThat AllocChange: "Object.alloc = old Object.alloc Un {n}";
	//: noteThat HCBounds: "0 <= hc & hc < table..Array.length";

	//: noteThat AllocChange: "Object.alloc = old Object.alloc Un {n}";
	//: noteThat HProp: "hc = h k0 (table..Array.length)";

	//: noteThat NewNotAlloc: "n ~: old Object.alloc";
	/*: noteThat NewNotRefArray:
	  "ALL i. 0 <= i & i < table..Array.length -->
	  (arrayRead (old Array.arrayState) table i) ~= n"
	  from ElementAllocInv, NewNotAlloc, NewNotRefArray;
	 */
	/*: noteThat NewContentDef: "theinv ContentDefInv"
	  from ContentDefInv, HProp, NewNotRefArray, HashInv, NewContentDef;
	*/

	//: noteThat NewOldNEq: "n ~= first";
	/*: noteThat NewNotRefByNext: "ALL x. x..Node.next ~= n"
	  from NewOldNEq, NewNotAlloc, unalloc_lonely, NewNotRefByNext;
	*/
	/*: noteThat OldNotRefByNext: 
	  "ALL x. first ~= null --> old (x..Node.next) ~= first"
	  from FirstInjInv, Init, HCBounds, OldNotRefByNext;
	 */
	/*: noteThat OldNotRefInTable: 
	  "ALL i. 0 <= i & i < table..Array.length & first ~= null --> 
	  table.[i] ~= first"
	  from Init, HCBounds, ElementInjInv, NewOldNEq, OldNotRefInTable;
	 */
	/*: noteThat NewFirstInj: "theinv FirstInjInv"
	  from FirstInjInv, NewNotRefByNext, OldNotRefByNext, 
	  OldNotRefInTable, HCBounds, NewFirstInj;
	 */

	/*: noteThat NewNextInj: "theinv NextInjInv"
	  from NextInjInv, OldNotRefByNext, NewNextInj;
	 */

	//: noteThat NotInContent: "ALL v. (k0, v) ~: old content";
	/*: noteThat NewConDef: "theinv ConDef" 
	  from Init, NotInContent, ContentDefInv, ConDef, AllocChange, 
	  NewNotRefByNext, HProp, NewConDef;
	 */
    }

    public static Object replace(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null & (EX v. (k0, v) : content)"
        modifies content, "Array.arrayState"
	ensures "content = old content - {(k0, result)} Un {(k0, v0)} &
                 (k0, result) : old content"
    */
    {
	Object v1 = remove(k0);
	add(k0, v0);
	return v1;
    }

    public static Object put(Object k0, Object v0)
    /*: requires "init & k0 ~= null & v0 ~= null"
        modifies content, "Array.arrayState"
	ensures "(result = null --> content = old content Un {(k0, v0)}) &
	         (result ~= null -->
		   content = old content - {(k0, result)} Un {(k0, v0)})"
     */
    {
	if (containsKey0(k0)) {
	    return replace(k0, v0);
	} else {
	    add(k0, v0);
	    return null;
	}
    }

    public static Object get(Object k0)
    /*: requires "init & k0 ~= null"
        ensures "(result ~= null --> (k0, result) : content) &
	         (result = null --> ~(EX v. (k0, v) : content)) &
		 Object.alloc = old Object.alloc"
	         
    */
    {
	int hc = compute_hash(k0);
	Node current = table[hc];
        while /*: inv "current : Node & current : Object.alloc &
                       (ALL v. ((k0, v) : content) = ((k0, v) : current..Node.con))" */
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public static boolean isEmpty()
    /*: requires "init"
        ensures "result = (content = {})";
    */
    {
	int i = 0;
	while /*: inv "0 <= i &
		       (ALL j. 0 <= j & j < i --> table.[j]..Node.con = {})" */
	    (i < table.length) {
	    if (table[i] != null) {
		return false;
	    }
	}
	return true;
    }

}
