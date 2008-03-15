public /*: claimedby AssociationList */ class Node {
    public Object key;
    public Object value;
    public Node next;
    //: public ghost specvar cnt :: "(obj * obj) set" = "({} :: (obj * obj) set)"
}

class AssociationList {
    private Node first;  
    /*:
    public specvar content :: "(obj * obj) set";
    vardefs "content == first..cnt";
  
    private static specvar edge :: "obj \<Rightarrow> obj \<Rightarrow> bool";
    vardefs "edge == (\<lambda> x y. (x \<in> Node \<and> y = x..next) \<or>  
                             (x \<in> AssociationList \<and> y = x..first))";

    invariant InjInv:
    "\<forall> x1 x2 y. y \<noteq> null \<and> edge x1 y \<and> edge x2 y \<longrightarrow> x1=x2";

    invariant CntNull:
    "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x = null \<longrightarrow> x..cnt = {}";
	  
    invariant CntDef:
    "\<forall> x. x \<in> Node \<and> x \<in> alloc \<and> x \<noteq> null \<longrightarrow>
	  x..cnt = {(x..key, x..value)} \<union> x..next..cnt \<and>
          (\<forall> v. (x..key, v) \<notin> x..next..cnt)";

    public ensured invariant SetInv:
    "\<forall> k v0 v1. (k, v0) \<in> content \<and> (k, v1) \<in> content \<longrightarrow> v0 = v1";
    public ensured invariant NonNullInv:
    "\<forall> k v. (k, v) \<in> content \<longrightarrow> k \<noteq> null \<and> v \<noteq> null";
    invariant CntAlloc:
    "\<forall> z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> x \<in> alloc \<and> y \<in> alloc";
    invariant CntNonNull:
    "\<forall> z x y. z \<in> Node \<and> z \<in> alloc \<and> (x, y) \<in> z..cnt \<longrightarrow> x \<noteq> null \<and> y \<noteq> null";
    */

    public AssociationList()
    /*: modifies "this..content"
        ensures "content = {}" */
    {
	first = null;
    }

    public boolean containsKey(Object k0)
    //: ensures "result = (\<exists> v. ((k0, v) \<in> content))"
    {
        return containsKey0(k0);
    }

    private boolean containsKey0(Object k0)
    /*: requires "theinvs"
        ensures "result = (\<exists> v. ((k0, v) \<in> content)) \<and> theinvs" */
    {
        Node current = first;
        while //: inv "(\<exists> v. (k0, v) \<in> content) = (\<exists> v. (k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void add(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> content)"
        modifies content
        ensures "content = old content \<union> {(k0, v0)}" */
    {
	add0(k0, v0);
    }

    private void add0(Object k0, Object v0)
    /*: requires "theinvs & k0 \<noteq> null \<and> v0 \<noteq> null \<and> \<not>(\<exists> v. (k0, v) \<in> content)"
        modifies content, "new..key", "new..value", "new..next", "new..cnt", first
        ensures "theinvs & content = old content \<union> {(k0, v0)}" */
    {
	Node n = new Node();
	n.key = k0;
	n.value = v0;
	n.next = first;
	//: "n..cnt" := "{(k0, v0)} \<union> first..cnt";
	first = n;
    }

    public Object replace(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content
	ensures "content = old content - {(k0, result)} \<union> {(k0, v0)} \<and>
                 (k0, result) \<in> old content" */
    {
	Object v1 = remove0(k0);
	add0(k0, v0);
	return v1;
    }

    public Object put(Object k0, Object v0)
    /*: requires "k0 \<noteq> null \<and> v0 \<noteq> null"
        modifies content
	ensures "(result = null \<longrightarrow> content = old content \<union> {(k0, v0)}) \<and>
	         (result \<noteq> null \<longrightarrow> 
		   content = old content - {(k0, result)} \<union> {(k0, v0)})" */
    {
	if (containsKey0(k0)) {
	    Object v1 = remove0(k0);
	    add0(k0, v0);
	    return v1;
	} else {
	    add0(k0, v0);
	    return null;
	}
    }

    public Object get(Object k0)
    /*: requires "k0 \<noteq> null"
        ensures "(result \<noteq> null \<longrightarrow> (k0, result) \<in> content) \<and>
	         (result = null \<longrightarrow> \<not>(\<exists> v. (k0, v) \<in> content))" */
    {
	Node current = first;
        while //: inv "\<forall> v. ((k0, v) \<in> content) = ((k0, v) \<in> current..cnt)"
            (current != null) {
            if (current.key == k0) {
                return current.value;
            }
            current = current.next;
        }
        return null;
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})"; */
    {
        return (first==null);
    }

    public Object remove(Object k0)
    /*: requires "k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content
        ensures "content = old content - {(k0, result)} \<and>
	         (k0, result) \<in> old content" */
    {
	return remove0(k0);
    }

    private Object remove0(Object k0)
    /*: requires "theinvs & k0 \<noteq> null \<and> (\<exists> v. (k0, v) \<in> content)"
        modifies content, first, "Node.next", "Node.cnt"
        ensures "theinvs & 
	         content = old content - {(k0, result)} \<and>
	         (k0, result) \<in> old content" */
    {
	//: pickWitness v0 :: obj suchThat "(k0, v0) \<in> content";
	Node f = first;
	if (f.key == k0) {
	    Node second = f.next;
	    f.next = null;
	    //: "f..cnt" := "{(f..key, f..value)}";
	    first = second;
	    return f.value;
	} else {
	    Node prev = first;
	    //: "prev..cnt" := "prev..cnt - {(k0, v0)}";
	    Node current = prev.next;
	    while /*: inv "prev \<noteq> null \<and>
		    prev..cnt = prev..(old cnt) - {(k0, v0)} \<and> current \<noteq> null \<and>
		    prev..next = current \<and> prev \<noteq> current \<and>
		    content = old content - {(k0, v0)} \<and>
		    (\<forall> n. n \<in> AssociationList \<and> n \<in> old alloc \<and> n \<noteq> this \<longrightarrow>
		    n..content = old (n..content)) \<and>
		    (k0, v0) \<in> current..cnt \<and>
		    comment ''CntDefInv''
		    (\<forall> n. n \<in> Node \<and> n \<in> alloc \<and> n \<noteq> null \<and> n \<noteq> prev \<longrightarrow>
		    n..cnt = {(n..key, n..value)} \<union> n..next..cnt \<and>
		    (\<forall> v. (n..key, v) \<notin> n..next..cnt)) \<and>
		    (\<forall> n. n..cnt = old (n..cnt) \<or> 
                          n..cnt = old (n..cnt) - {(k0, v0)}) \<and>
		    null..cnt = {}"
		  */
		(current.key != k0)
                {
                    //: "current..cnt" := "current..cnt - {(k0, v0)}"; 
                    prev = current;
                    current = current.next;
                }
	    Node nxt = current.next;
	    prev.next = nxt;
	    current.next = null;
	    //: "current..cnt" := "{(current..key, current..value)}";
	    return current.value;
	}
    }
}
