public class ArrayList
{
    private static Object[] elementData;
    private static int size;

    /*: public static specvar init :: bool;
        public static specvar content :: "(int * obj) set";
	public static specvar csize :: int;
	public static specvar msize :: int;
	
	vardefs "init == elementData ~= null"
	vardefs "content == {(i, n). 0 <= i & i < size & n = elementData.[i]}"
	vardefs "csize == size"
	vardefs "msize == elementData..Array.length"

	invariant InitInv: 
	  "~init --> size = 0 & elementData = null & hidden = {}"
	invariant SizeInv: 
	  "init --> 0 <= size & size <= elementData..Array.length"
	invariant HiddenInv: "init --> elementData : alloc & elementData : hidden & hidden \<subseteq> alloc";

	invariant NotHiddenInv:
	  "init --> 
	    (ALL i. ((0 <= i & i < size) --> elementData.[i] ~: hidden))"

	invariant AllocInv:
	  "init -->
	    (ALL i. ((0 <= i & i < size) --> elementData.[i] : alloc))"

	invariant RangeInv1:
	  "init --> (ALL i. 0 <= i & i < size --> (EX v. (i,v) : content))";
	invariant RangeInv2:
	  "init --> (ALL i v. (i,v) : content --> 0 <= i & i < size)";
	invariant RangeInvInj:
	  "init --> (ALL i v1 v2. (i,v1) : content & (i,v2) : content --> v1=v2)"
    */

    public static void init_with(int initialCapacity)
    /*: requires "~init & 0 < initialCapacity"
        modifies init, msize
        ensures "init & content = {} & csize = 0 & msize = initialCapacity"
     */
    {
	elementData = new /*: hidden */ Object[initialCapacity];
    }

    public static void init()
    /*: requires "~init"
        modifies init, msize
        ensures "init & content = {} & csize = 0 & msize = 10"
     */
    {
	elementData = new /*: hidden */ Object[10];
    }

    public static void trimToSize()
    /*: requires "init"
        modifies msize
	ensures "msize = csize"
    */
    {
	int oldCapacity = elementData.length;
	if (size < oldCapacity) {
	    Object oldData[] = elementData;
	    elementData = new /*: hidden */ Object[size];
	    int i = 0;
	    while /*: inv "0 <= i &
		    (ALL j. (oldData.[j] =
		    arrayRead (old Array.arrayState) (old elementData) j)) &
		    (ALL j. (((0 <= j & j < i) -->
		     elementData.[j] = oldData.[j]))) &
		    (ALL a i. a ~: hidden -->
		     arrayRead (old Array.arrayState) a i = a.[i])"
		  */
		(i < size)
	    {
		elementData[i] = oldData[i];
		i = i + 1;
	    }
	}
    }

    public static void ensureCapacity(int minCapacity)
    /*: requires "init"
        modifies msize
        ensures "minCapacity <= msize & old msize <= msize"
    */
    {
	_ensureCapacity(minCapacity);
    }

    private static void _ensureCapacity(int minCapacity)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden"
        ensures "minCapacity <= msize & old msize <= msize & init = old init &
	         (ALL a j. (old a) : (old alloc) -->
		   a.[j] =
		   arrayRead (old Array.arrayState) (old a) j) &
		 (ALL j. ((0 <= j & j < size) -->
		   elementData.[j] =
		   arrayRead (old Array.arrayState) (old elementData) j)) &
	         (ALL a j. a ~: hidden -->
		   a.[j] = arrayRead (old Array.arrayState) a j) &
		 (ALL o1. (o1 : old alloc) -->
		   ((o1 : old hidden) = (o1 : hidden))) & theinvs"
    */
    {
	int oldCapacity = elementData.length;
	if (minCapacity > oldCapacity) {
	    Object oldData[] = elementData;
	    int newCapacity = (oldCapacity * 3)/2 + 1;
	    if (newCapacity < minCapacity)
		newCapacity = minCapacity;
	    elementData = new /*: hidden */ Object[newCapacity];
	    int i = 0;
	    while /*: inv "0 <= i &
		    (ALL j. ((0 <= j & j < size -->
		      oldData.[j] = 
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		    (ALL j. ((0 <= j & j < i) -->
		      elementData.[j] = oldData.[j])) &
  	            (ALL a j. a ~: hidden -->
		      a.[j] = arrayRead (old Array.arrayState) a j) &
		    (ALL a i. (old a) : (old alloc) --> 
		      a.[i] = arrayRead (old Array.arrayState) (old a) i)"
		  */
		(i < size)
	    {
		elementData[i] = oldData[i];
		i = i + 1;
	    }
	}
    }

    public static int size()
    /*: requires "init"
        ensures "result = csize"
    */
    {
	return size;
    }

    public static boolean isEmpty()
    /*: requires "init"
        ensures "result = (csize = 0)"
    */
    {
	return size == 0;
    }
    
    public static boolean contains(Object elem)
    /*: requires "init"
        ensures "(result = (EX i. (i, elem) : content))";
    */
    {
	int index = indexOf1(elem);
	//: noteThat please1: "0 <= index --> (EX i. (i,elem) : content)";
	//: noteThat please2: "index = -1 --> ~(EX i. (i,elem) : content)";
	//: noteThat possible: "0 <= index | index = -1";
	boolean res = (0 <= index);
	//: noteThat aha: "res = (EX i. (i, elem) : content)" from please1, please2, possible, aha;
	return res;
    }

    public static int indexOf(Object elem)
    /*: requires "init"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> (result, elem) : content) &
		 (result ~= -1 --> ~(EX i. i < result & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content))"
    */
    {
	return indexOf1(elem);
    }

    private static int indexOf1(Object elem)
    /*: requires "init & theinvs"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> (result, elem) : content) &
		 (result ~= -1 --> ~(EX i. i < result & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content)) & theinvs"
    */
    {
	int i = 0;
	
	while /*: inv "0 <= i &
		       (ALL j. 0 <= j & j < i --> elem ~= elementData.[j])" */
	    (i < size)
	{
	    if (elementData[i] == elem)
		return i;
	    i = i + 1;
	}
	return -1;
    }

    public static int lastIndexOf(Object elem)
    /*: requires "init"
        ensures "-1 <= result & result < csize &
	         (result ~= -1 --> 
		  ((result, elem) : content) &
		  ~(EX i. result < i & (i, elem) : content)) &
                 (result = -1 --> ~(EX i. (i, elem) : content))"
     */
    {
	int i = size - 1;
	while /*: inv "i < size &
		   (ALL j. i < j & j < size --> elem ~= elementData.[j]) &
		   (ALL x i. ((x : alloc & x : Array & x ~: hidden) -->
		    x.[i] = arrayRead (old Array.arrayState) (old x) i))" 
	      */
	    (i >= 0)
	{
	    if (elementData[i] == elem)
		return i;
	    i = i - 1;
	}
	return -1;
    }

    public static Object[] toArray()
    /*: requires "init"
        modifies arrayState
        ensures "(ALL i e. (i, e) : content --> result.[i] = e) &
	         (ALL i. 0 <= i & i < result..Array.length --> 
		  (i, result.[i]) : content)"
     */
    {
	int i = 0;
	Object[] res = new Object[size];
	
	while /*: inv "theinvs &
		comment ''C1'' (0 <= i) & comment ''C2'' (content = old content) &
		comment ''IA'' (ALL j. (0 <= j & j < i --> res.[j] = elementData.[j])) &
		comment ''IB'' (ALL x i. ((x ~: hidden & x ~= res & x : Array) -->
		  x.[i] = arrayRead (old Array.arrayState) x i)) &
		comment ''IC'' (ALL j. ((0 <= j & j < size) --> elementData.[j] ~: hidden)) &
		comment ''ID'' (ALL j. 
		  ((0 <= j & j < size) --> elementData.[j] : alloc))"
	      */
	    (i < size)
	{
	    res[i] = elementData[i];
	    i = i + 1;
	}
	return res;
    }

    public static Object get(int index)
    /*: requires "init & 0 <= index & index < csize"
        ensures "(index, result) : content"
     */
    {
	return elementData[index];
    }

    public static Object set(int index, Object element)
    /*: requires "init & 0 <= index & index < csize"
        modifies content
	ensures "(index, result) : old content & 
	  content = (old content - {(index, result)}) Un {(index, element)}"
    */
    {
	Object oldValue = elementData[index];
	elementData[index] = element;
	return oldValue;
    }

    private static boolean add1(Object o)
    /*: requires "init & theinvs"
        modifies "Array.arrayState", elementData, msize, "ArrayList.hidden", content, size, csize
	ensures "(old csize, o) : content &
	         comment ''addContentChange'' (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         comment ''csizeChange'' (csize = old csize + 1) & result &
                 old msize <= msize & csize <= msize &
	         (ALL a j. a ~: hidden -->
		   a.[j] = arrayRead (old Array.arrayState) a j) &
		 (ALL o1. (o1 : old alloc) -->
		   ((o1 : old hidden) = (o1 : hidden))) & 
		   theinvs"
    */
    {
	_ensureCapacity(size + 1);
	elementData[size] = o;
	size = size + 1;
	//: noteThat "old csize < size";
	//: noteThat "theinvs";
	return true;
    }

    public static boolean add(Object o)
    /*: requires "init"
        modifies content, csize, msize
	ensures "(old csize, o) : content &
	         (ALL j. ((0 <= j & j < old csize) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
	         csize = old csize + 1 & result &
                 old msize <= msize & csize <= msize"
    */
    {
	return add1(o);
    }

    public static void add_at(int index, Object element)
    /*: requires "comment ''addAtPre'' (init & 0 <= index & index <= csize)"
        modifies content, csize, msize
	ensures "(ALL j e.
                  (0 <= j & j < index --> ((j, e) : content) = ((j, e) : old content)) &
		  (index,element) : content &
		  (index < j & j < csize --> ((j, e) : content) = ((j - 1, e) : old content))) &
	         csize = old csize + 1 &
	         old msize <= msize &
		 csize <= msize"		
    */
	/*
              (content = {(i,e). 0 <= i & i < index & (i,e) : old content}
                      Un {(index,element)}
                      Un {(i,e). index < i & (i - 1,e) : old content})
         */
    {
	_ensureCapacity(size + 1);
	int i = size - 1;
	while /*: inv "index - 1 <= i & i <= size - 1 &
		      (ALL a j. ((a ~: hidden) -->
		       a.[j] =
		       arrayRead (old Array.arrayState) a j)) &
		      ((i = size - 1) -->
		       (ALL j. ((0 <= j & j < size) -->
		        elementData.[j] ~: hidden))) &
		      ((i < size - 1) -->
		       (ALL j. ((0 <= j & j < size + 1) -->
		        elementData.[j] ~: hidden))) &
		      ((i = size - 1) -->
		       (ALL j. ((0 <= j & j < size) --> 
		        elementData.[j] : alloc))) &
		      ((i < size - 1) -->
		       (ALL j. ((0 <= j & j < size + 1) -->
		        elementData.[j] : alloc))) &
		      ((ALL j. ((0 <= j & j <= i) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((0 <= j & j <= index & j < size) -->
		      elementData.[j] =
		      arrayRead (old Array.arrayState) (old elementData) j))) &
		      ((ALL j. ((i < j & j < size) -->
		      elementData.[j + 1] =
		      arrayRead (old Array.arrayState) (old elementData) j)))"
	    */
	    (index <= i)
	    {
		elementData[i + 1] = elementData[i];
		i = i - 1;
	    }
	elementData[index] = element;
	size = size + 1;
    }

    public static Object remove_at(int index)
    /*: requires "init & 0 <= index & index < csize"
        modifies content, csize
	ensures "(ALL j e.
                  (0 <= j & j < index --> ((j, e) : content) = ((j, e) : old content)) &
		  (index <= j & j < csize --> ((j, e) : content) = ((j + 1, e) : old content))) &
		 ((index, result) : old content) &
                 (csize = old csize - 1)";
    */
    {
	Object oldValue = elementData[index];
	fastRemove(index);
	return oldValue;
    }

    public static Object remove_at_dep(int index)
    /*: requires "init & 0 <= index & index < csize"
        modifies content, csize
	ensures "((index, result) : old content) &
	         (csize = old csize - 1) &
                 (ALL j. ((0 <= j & j < index) -->
		  ((ALL e. (j, e) : content --> (j, e) : old content) &
		   (ALL e. (j, e) : old content --> (j, e) : content)))) &
		 (ALL j. ((index <= j & j < csize) -->
                  ((ALL e. (j, e) : content --> (j + 1, e) : old content) &
		   (ALL e. (j + 1, e) : old content --> (j, e) : content))))"
    */
    {
	Object oldValue = elementData[index];
	int i = index;
	while /*: inv "index <= i & 
		(ALL j. ((0 <= j & j < index) --> 
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL j. ((index <= j & j < i) -->
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) elementData (j + 1)))) &
		(ALL j. ((i <= j & j < size) -->
		 elementData.[j] = 
		  (arrayRead (old Array.arrayState) (old elementData) j))) &
                (ALL x i. (x : Array & x ~: hidden) -->
		 x.[i] = arrayRead (old Array.arrayState) (old x) i)"
	      */
	    (i < size - 1)
	{
	    elementData[i] = elementData[i+1];
	    i = i + 1;
	}
	size = size - 1;
	elementData[size] = null;

	return oldValue;
    }

    public static boolean remove(Object o1)
    /*: requires "init"
        modifies content, csize
	ensures "(~result --> content = old content) &
      		 (result -->
		  (EX i. (((i, o1) : old content) &
		         ~(EX j. j < i & (j, o1) : old content) &
			 (ALL j e. ((0 <= j & j < i) -->
			  (((j, e) : content --> (j, e) : old content) &
			   ((j, e) : old content --> (j, e) : content)))) &
			 (ALL j e. ((i <= j & j < csize) -->
			  (((j, e) : content --> (j + 1, e) : old content) &
			   ((j + 1, e) : old content --> (j, e) : content)))))))"
    */
    {
	int index = 0;
	while /*: inv "0 <= index & size = old size & 
		       alloc = old alloc &
		      (ALL j. 0 <= j & j < index --> o1 ~= elementData.[j]) &
		      (ALL a i. 
		        a.[i] = arrayRead (old Array.arrayState) (old a) i)"
	      */
	    (index < size)
	{
	    if (elementData[index] == o1) {
		fastRemove(index);
		/*: noteThat indexExists:
		  "(((index, o1) : old content) &
		   ~(EX j. j < index & (j, o1) : old content) &
		   (ALL j e. ((0 <= j & j < index) -->
		    (((j, e) : content --> (j, e) : old content) &
		     ((j, e) : old content --> (j, e) : content)))) &
		   (ALL j e. ((index <= j & j < csize) -->
		    (((j, e) : content --> (j + 1, e) : old content) &
		     ((j + 1, e) : old content --> (j, e) : content)))))";
		*/
		/*: noteThat postCond:
		  "(EX i. (((i, o1) : old content) &
		          ~(EX j. j < i & (j, o1) : old content) &
			  (ALL j e. ((0 <= j & j < i) -->
			   (((j, e) : content --> (j, e) : old content) &
			    ((j, e) : old content --> (j, e) : content)))) &
			  (ALL j e. ((i <= j & j < csize) -->
			   (((j, e) : content --> (j + 1, e) : old content) &
			    ((j + 1, e) : old content --> (j, e) : content))))))"
		  from indexExists, postCond;
		*/
		return true;
	    }
	    index = index + 1;
	}
	return false;
    }

    private static void fastRemove(int index)
    /*: requires "init & 0 <= index & index < size & theinvs"
        modifies "Array.arrayState", size, content, csize
	ensures "(ALL j. ((0 <= j & j < index) -->
	          elementData.[j] =
		  arrayRead (old Array.arrayState) (old elementData) j)) &
		 (ALL j. ((index <= j & j < size) -->
		  elementData.[j] =
		  arrayRead (old Array.arrayState) (old elementData) (j + 1))) &
		 elementData.[size] = null &
		 (ALL a i. a ~= elementData -->
		  a.[i] = arrayRead (old Array.arrayState) (old a) i) &
		 (size = old size - 1) & theinvs"
    */
    {
	int i = index;
	while /*: inv "index <= i & 
		(ALL j. ((0 <= j & j < index) --> 
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL j. ((index <= j & j < i) -->
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) (j + 1)))) &
		(ALL j. ((i <= j & j < size) -->
		 elementData.[j] = 
		 (arrayRead (old Array.arrayState) (old elementData) j))) &
		(ALL a i. ((a ~= elementData) -->
		 a.[i] = arrayRead (old Array.arrayState) (old a) i))"
	      */
	    (i < size - 1)
	{
	    elementData[i] = elementData[i+1];
	    i = i + 1;
	}
	size = size - 1;
	elementData[size] = null;
    }

    public static void clear()
    /*: requires "init"
        modifies content, csize
	ensures "content = {} & csize = 0"
     */
    {
	int i = 0;
	
	while /*: inv "0 <= i &
		   (ALL x i. ((x : Array & x ~: hidden) -->
		    x.[i] = arrayRead (old Array.arrayState) (old x) i))"
	      */
	    (i < size)
        {
	    elementData[i] = null;
	    i = i + 1;
	}
	size = 0;
    }

    public static void pushLast(Object element)
    /*: requires "init"
        modifies content, csize, msize
	ensures "comment ''sizeInc'' (csize = old csize + 1) &
                 comment ''contentAdd'' (content = old content Un {(csize - 1,element)})"
     */
    {
	boolean res = add1(element);
	//: noteThat inserted: "(csize - 1, element) : content";
	{ //: pickAny i::int, e::obj
	    {//: assuming h1: "(i,e) : old content";
	     //: noteThat g1: "0 <= i & i < old csize";		
             //: noteThat g2: "(i,e) : content" from g2,g1, addContentChange, h1;
	    }
	    //: noteThat thus1: "(i,e) : old content --> (i,e) : content";
	    {//: assuming hh1: "(i,e) : content";
             //: noteThat gg1: "0 <= i & i < csize";
             //: noteThat gg2: "i = csize - 1 --> (i,e) : old content Un {(csize - 1,element)}";
		{//: assuming hh2: "i < csize - 1";
                 //: noteThat gg3: "(i,e) : old content" from addContentChange, hh2, gg1, hh1, csize_def, csizeChange;
		}
             //: noteThat possible: "i < csize - 1 | i = csize - 1";
             //: noteThat gg4: "(i,e) : old content Un {(csize - 1,element)}" from gg1, gg3, gg2, g2, h1, csize_def, csizeChange, possible;
	    }
	    /*: noteThat pointwise: 
                  "((i,e) : old content --> (i,e) : content) &
                   ((i,e) = (csize - 1, element) --> (i,e) : content) &
                   ((i,e) : content --> (i,e) : (old content Un {(csize - 1,element)}))" forSuch i,e;
	     */
	}
	//: noteThat tpost: "(content = old content Un {(csize - 1,element)})" from pointwise;
    }

    public static Object popLast()
    /*: requires "init & csize > 0"
        modifies content, csize
	ensures "csize = old csize - 1 &
                 content = old content - {(csize,result)}"
     */
    {
	size = size - 1;
	Object res = elementData[size];
	elementData[size] = null;
	return res;
    }
}
