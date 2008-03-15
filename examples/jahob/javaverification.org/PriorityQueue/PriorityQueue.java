class PriorityQueueElement
{
    public Object ob;
    public int key;
}

public class PriorityQueue
{
    private static PriorityQueueElement[] queue;
    private static int length;

    /*:
      public static specvar init :: bool;
      public static specvar spqueue :: "obj set";
      public static specvar smaxlen :: int;
      public static specvar slength :: int;
      public static ghost specvar insubtree :: "(int * int) set" = "{}";

      vardefs "init == queue ~= null";
      vardefs "spqueue == 
                 { p. EX i. 0 <= i & i < length & p = queue.[i] }";
		   
      vardefs "smaxlen == queue..Array.length";
      vardefs "slength == length";
      
      invariant LengthLowerInv: "init --> 0 <= length";
      invariant LengthUpperInv: "init --> length <= queue..Array.length";
      invariant NonNullInv: "init -->
                   (ALL i. 0 <= i & i < length --> queue.[i] ~= null)";
      invariant NullInv: "init -->
                   (ALL i. length <= i & i < queue..Array.length -->
		           queue.[i] = null)";
      invariant DistinctInv:
        "init --> 
	  (ALL i j. (0 <= i & i < length & 0 <= j & j < length &
	    queue.[i] = queue.[j]) --> i = j)"

      invariant OrderedInv:
        "init -->
	  (ALL i j. 
	    (0 <= i & i < length & 0 <= j & j < length & 
	      ((j = i + i + 1) | (j = i + i + 2)) -->
	      queue.[i]..PriorityQueueElement.key >=
	      queue.[j]..PriorityQueueElement.key))";
    */

    public static void init(int len)
    /*: requires "~init & 0 <= len"
        modifies init, spqueue, smaxlen, slength, "Array.arrayState"
	ensures "init & spqueue = {} & smaxlen = len & slength = 0"
    */
    {
	queue = new PriorityQueueElement[len];
	
	int i = 0;

	while /*: inv "ALL j. 0 <= j & j < i --> queue.[i] = null" */
	    (i < queue.length) {
	    queue[i] = null;
	}
	length = 0;
    }

    public static int currLength()
    /*: requires "init"
        ensures "result = slength"
    */
    {
	return length;
    }
    
    public static int maxLength()
    /*: requires "init"
        ensures "result = smaxlen"
    */
    {
	return queue.length;
    }
    
    public static boolean isEmpty()
    /*: requires "init"
        ensures "result = (slength = 0)"
    */
    {
	return (length == 0);
    }

    public static boolean isFull()
    /*: requires "init"
        ensures "result = (slength = smaxlen)"
    */
    {
	return (length == queue.length);
    }
   
    private static int parent(int i)
    /*: requires "i > 0"
        ensures "result >= 0 & result < i & 
	         (i = result + result + 1 | i = result + result +2)"
     */
    {
	return (i-1)/2;
    }

    private static int left(int i)
    /*: requires "0 <= i"
        ensures "result >= 0 & result > i & result = 2 * i + 1"
     */
    {
	return (2*i + 1);
    }

    private static int right(int i)
    /*: requires "0 <= i"
        ensures "result >= 0 & result > i & result = 2 * i + 2"
     */
    {
	return (2*i + 2);
    }

    public static void insert(PriorityQueueElement e)
    /*: requires "init & e ~= null & slength < smaxlen & e ~: spqueue"
        modifies spqueue, slength, "Array.arrayState"
	ensures "spqueue = old spqueue Un {e} & 
                 (slength = (old slength) + 1)"
    */
    {
	int i = length;
	length = length + 1;

	while /*: inv "(comment ''IBounds'' (0 <= i & i < length)) & 
		       e ~: spqueue &
		       (comment ''RelToI''
		        (((i + i + 1 < length) -->
			  (queue.[(i + i + 1)]..PriorityQueueElement.key <
			   e..PriorityQueueElement.key)) &
			 ((i + i + 2 < length) -->
			  (queue.[(i + i + 2)]..PriorityQueueElement.key <
			   e..PriorityQueueElement.key)))) &
		       (comment ''ContentPostLoop''
		       (old spqueue = { p. EX j. 0 <= j & j < length &
                                          j ~= i & p = queue.[j] })) &
		       (ALL j. 0 <= j & j < length & j ~= i --> 
		               queue.[j] ~= null) & 
		       (comment ''PDBefore''
		        (ALL j k. 0 <= j & j < length & 0 <= k & k < length &
		                 queue.[j] = queue.[k] & j ~= i & k ~= i --> 
				 j = k)) &
		       theinv NullInv &
		       (comment ''OrderedSkipLoop''
		       (i = (old length) -->
		        (ALL j k. 
			 (0 <= j & j < (old length) & 0 <= k & 
			  k < (old length) &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   queue.[j]..PriorityQueueElement.key >=
			   queue.[k]..PriorityQueueElement.key)))) &
		       (comment ''OrderedPostLoop''
		       (i ~= (old length) -->
		        (ALL j k. 
		         (0 <= j & j < length & 0 <= k & k < length &
			  ((k = j + j + 1) | (k = j + j + 2)) -->
			   queue.[j]..PriorityQueueElement.key >=
			   queue.[k]..PriorityQueueElement.key))))"
	      */
	    (i > 0 && queue[parent(i)].key < e.key)
	{
	    int p = parent(i);
	    //: noteThat PBounds: "(0 <= p & p < length)";
	    //: noteThat PIRel: "(i = p + p + 1 | i = p + p + 2)";
	    queue[i] = queue[p];
	    i = p;
	    /*: noteThat ContentAfter:
	      "old spqueue = 
	       { p. EX j. 0 <= j & j < length & j ~= i & p = queue.[j] }"
	      from ContentPostLoop, IBounds, PBounds, ContentAfter;
	    */
	    /*: noteThat PDAfter:
	      "(ALL j k. 0 <= j & j < length & 0 <= k & k < length &
	                 queue.[j] = queue.[k] & j ~= i & k ~= i --> j = k)"
	      from PDBefore, PBounds, PDAfter;
	    */
	    /*: noteThat sameAfter:
	      "ALL jj kk. (0 <= jj & jj < length & 0 <= kk & kk < length & 
	      ((kk = jj + jj + 1) | (kk = jj + jj + 2)) -->
	      queue.[jj]..PriorityQueueElement.key >=
	      queue.[kk]..PriorityQueueElement.key)";
	    */	    
	}
	queue[i] = e;
	/*: noteThat ContentDef:
	  "spqueue = {p. (EX i. 0 <= i & i < length & p = queue.[i])}";
	*/
	/*: noteThat ContentFinal: "spqueue = old spqueue Un { e }"
	  from ContentPostLoop, ContentDef, IBounds, ContentFinal;
	*/
	/*: noteThat LoopExitCond: 
	  "i > 0 --> 
	  (ALL x. ((i = x + x + 1 | i = x + x + 2) --> 
	          queue.[x]..PriorityQueueElement.key >=
		  e..PriorityQueueElement.key))"
	  from parent_Postcondition, LoopCondition, LoopExitCond;
	 */
	/*: noteThat OrderedFinal: "theinv OrderedInv"
	  from OrderedSkipLoop, OrderedPostLoop, LoopExitCond, RelToI, 
	  OrderedFinal;
	*/
    }

    public static PriorityQueueElement findMax()
    /*: requires "init & slength > 0"
        ensures "result ~= null & result : spqueue &
	         (ALL x. (x : spqueue --> 
		  result..PriorityQueueElement.key >=
		  x..PriorityQueueElement.key))"
    */
    {
	//: noteThat ArrLength: "0 < length";
	/*: noteThat Ordering:
	  "(ALL i j.
	    ((0 <= i & i < length & 0 <= j & j < length &
	     ((j = i + i + 1) | (j = i + i + 2)) -->
	     queue.[i]..PriorityQueueElement.key >=
	     queue.[j]..PriorityQueueElement.key))) -->
	   (ALL k. ((0 <= k & k < length) -->
	     queue.[0]..PriorityQueueElement.key >=
	     queue.[k]..PriorityQueueElement.key))" 
	     from ArrLength, Ordering;
	*/
	return queue[0];
    }

    public static PriorityQueueElement extractMax()
    /*: requires "init & slength > 0"
        modifies "Array.arrayState", spqueue, slength
        ensures  "slength = old slength - 1 & result ~= null &
	          spqueue = old spqueue - { result } &
		  (ALL x. (x : (old spqueue) --> 
		  result..PriorityQueueElement.key >=
		  x..PriorityQueueElement.key))"
    */
    {
	PriorityQueueElement result = queue[0];
	//: noteThat ArrLength: "0 < length";
	/*: noteThat Ordering:
	  "(ALL i j.
	    ((0 <= i & i < length & 0 <= j & j < length &
	     ((j = i + i + 1) | (j = i + i + 2)) -->
	     queue.[i]..PriorityQueueElement.key >=
	     queue.[j]..PriorityQueueElement.key))) -->
	   (ALL k. ((0 <= k & k < length) -->
	     queue.[0]..PriorityQueueElement.key >=
	     queue.[k]..PriorityQueueElement.key))" 
	     from ArrLength, Ordering;
	*/
	
	length = length - 1;
	queue[0] = queue[length];
	queue[length] = null;
	//: noteThat IntQueueContent: "spqueue = old spqueue - { result }";
	if (0 < length) heapify(0);
	/*: noteThat FinalQueueContent: "spqueue = old spqueue - { result }"
	  from IntQueueContent, heapify_Postcondition, FinalQueueContent;
	*/
	return result;
    }

    private static void heapify(int i)
    /*: requires "init & (0 <= i) & (i < length) & theinv LengthLowerInv & 
                  theinv LengthUpperInv & theinv NonNullInv &
		  theinv NullInv & theinv DistinctInv &
		  (comment ''GlobalOrderingPre''
		   (ALL k j.
		    (0 <= k & k < length & k ~= i & 0 < j & j < length &
		    ((j = k + k + 1) | (j = k + k + 2)) -->
		    queue.[k]..PriorityQueueElement.key >=
		    queue.[j]..PriorityQueueElement.key))) &
		  (comment ''LocalOrderingPre''
		   (ALL x. 
		    ((0 <= x & (i = x + x + 1 | i = x + x + 2)) -->
		     (((i + i + 1 < length) --> 
		      queue.[x]..PriorityQueueElement.key >=
		      queue.[(i + i + 1)]..PriorityQueueElement.key) &
		      ((i + i + 2 < length) -->
		      queue.[x]..PriorityQueueElement.key >=
		      queue.[(i + i + 2)]..PriorityQueueElement.key)))))"
        modifies "Array.arrayState"
        ensures "init = old init & spqueue = old spqueue &
	         smaxlen = old smaxlen & slength = old slength & theinvs"
     */
    {
	int m = i;

	int l = left(i);
	if (l < length && queue[l].key > queue[i].key)
	    m = l;

	int r = right(i);
	if (r < length && queue[r].key > queue[m].key)
	    m = r;

	if (m != i)
	{
	    //: noteThat LeftDef: "l = i + i + 1";
	    //: noteThat RightDef: "r = i + i + 2";
	    /*: noteThat mLeft: 
	      "m = l --> ((queue.[l]..PriorityQueueElement.key > 
	                   queue.[i]..PriorityQueueElement.key) &
			 (r < length -->
			  (queue.[l]..PriorityQueueElement.key >=
			   queue.[r]..PriorityQueueElement.key)))";
	     */
	    /*: noteThat mRight:
	      "m = r --> ((queue.[r]..PriorityQueueElement.key >
	                   queue.[i]..PriorityQueueElement.key) &
			 (l < length -->
			  (queue.[r]..PriorityQueueElement.key >=
			   queue.[l]..PriorityQueueElement.key)))";
	     */

	    PriorityQueueElement p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;

	    //: noteThat iLB: "0 <= i";
	    //: noteThat iUB: "i < length";
	    //: noteThat mBounds: "0 <= m & m < length";
	    /*: noteThat LocalOrder:
	      "(i + i + 1 < length -->
	       (queue.[i]..PriorityQueueElement.key >=
	        queue.[(i + i + 1)]..PriorityQueueElement.key)) &
	       (i + i + 2 < length -->
	       (queue.[i]..PriorityQueueElement.key >=
	        queue.[(i + i + 2)]..PriorityQueueElement.key))"
		from LeftDef, RightDef, mRight, mLeft, iLB, LocalOrder;
	    */
	    /*: noteThat OrderingLem:
	      "(ALL k j.
		    (0 <= k & k < length & k ~= m & 0 < j & j < length &
		    ((j = k + k + 1) | (j = k + k + 2)) -->
		    queue.[k]..PriorityQueueElement.key >=
		    queue.[j]..PriorityQueueElement.key))"
	      from LeftDef, RightDef, GlobalOrderingPre, LocalOrder, iLB, iUB, 
	      mBounds, LocalOrderingPre, OrderingLem;
	    */
	    //: noteThat "spqueue = old spqueue";
	    heapify(m);
	}
    }

    /*
    public static void main(String[] args)
    {
	int size = 32;
	Random generator = new Random();
	init(size);

	System.out.println("Inserting...");
	int r = generator.nextInt(size);
	int max = r;
	while(!isFull())
        {
	    PriorityQueueElement elem;

	    if (r > max) max = r;
	    elem = new PriorityQueueElement();
	    elem.ob = new Integer(r);
	    elem.key = r;

	    insert(elem);
	    System.out.println(r);
	    elem = (PriorityQueueElement) findMax();
	    if (elem.key != max)
		System.err.println("There is a bug!");
	    r = generator.nextInt(size);
	}

	System.out.println("\nExtracting...");
	while(!isEmpty())
	{
	    PriorityQueueElement elem;
	    elem = (PriorityQueueElement)extractMax();
	    System.out.println((Integer)elem.ob);
	}
    }
    */
}
