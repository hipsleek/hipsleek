/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).
HeapPred G4(node a, node b, node c, node d).


void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

void delete_list(ref node x)
  infer[H, G]
  requires H(x)
  ensures G(x,x');
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}

/*
 H(x)&x!=null--> x::node<_,b> * HP_1356(b,x)
 HP_1356(b,x) * x::node<_,b>&x!=null --> H(b)
 emp&x'=null & x!=null --> G(x,x')
 H(x)&x=null --> G(x,x)

normalize: 
H(x)&x!=null--> x::node<_,b> * HP_1356(b) -> H(b)

H(x)&x!=null -> x::node<_,b> * H(b)
emp&x'=null & x!=null --> G(x,x')
H(x)&x=null --> G(x,x)
H(x)->x=null
H(x) & x' = null -> G(x,x')

Final: 
H(x) -> (x = null) v (x::node<_,b> * H(b)) ==> match with linked list
H(x) & x' = null -> G(x,x')
*/


//The number of elements that conform the list's content.
relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[SIZEH,H,H1]
  requires H(x) //0<=m
  ensures  H1(x) & SIZEH(res,n);//res=m+n & m>=0
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}


/*
 H(x)&x=null --> H1(x)
 H(x)&x!=null --> x::node<val_81_1002',b> * HP_2155(b,x)
 HP_2155(b,x) * x::node<_,b>&x!=null--> H(b)
 x::node<_,_>&x!=null --> H1(x)

normalize:
Drop 2nd paramiter of HP_2155
 H(x)&x=null --> H1(x)
 H(x)&x!=null --> x::node<val_81_1002',b> * HP_2155(b)
 HP_2155(b) * x::node<_,b>&x!=null--> H(b)
 x::node<_,_>&x!=null --> H1(x)  (************************)

H(x) -> x = null
H(x) &x!=null -> x::node<_,b> * H(b)
 H(x)&x=null --> H1(x)
x::node<_,_> --> H1(x)


DEBUG:
### action =  InferHeap: ( H1(x), emp)
 ### estate =  x'::node<val_64_1082,v_node_64_1087>@M[Orig] * H1(v_node_64_1087)&x'=x & x'!=null & !(v_bool_60_1006') & x'!=null & !(v_bool_60_1006') & SIZEH(v_int_64_1005',1+n) & res=v_int_64_1005'&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  H1(x)&true&{FLOW,(22,23)=__norm}[]


(RELASS [H1], x::node<val_64_1082,v_node_64_1087>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]


*/
HeapPred T1(node a).
HeapPred T2(node a). 

relation SIZE(int a, int b).
int size(node x)
  infer[SIZE, T1, T2]
  requires T1(x) //0<=n
  ensures T2(x) & SIZE(res,n);//n>=0 & n=res
{
  int m = 0;
  return size_helper(x, m);
}

/*
T1(x) --> H(x)
H1(x) --> T2(x)
*/

void swap(ref node x, ref node y)
  infer [H1, H2, G1, G2]
  requires H1(x)*H2(y)
  ensures G1(x,x')*G2(y,y'); // m=m1 & n=n1
{
  node tmp = x;
  x = y;
  y = tmp;
}

/*
H1(x) * H2(y) --> G1(x,y) * G2(y,x)
*/

relation PUF(int a, int b).

void push_front(ref node x, int v)
  infer[H, G]
  requires H(x)
  ensures G(x,x'); //'m=n+1
{
  node tmp = new node(v,x);
  x = tmp;
}

/*
H(x) * x'::node<v,x> --> G(x,x')
*/



//pop and return first element

node pop_front(ref node x)
  infer[H,G]
  requires H(x) //& m>=1
  ensures  G(x,x'); //' m>=1 & m=n+1
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}


/*

(H(x) & x'=x--> x::node<val_164_959',b> * HP_1911(b,x,x)
HP_1911(x',x,x) * x::node<val_164_1920,next_165_963'>&v_node_166_964'=x --> G(x,x')

Normalize
H(x) & x'=x--> x::node<_,b> * HP_1911(b)
HP_1911(x') * x::node<val_164_1920,next_165_963'> --> G(x,x')

by handc  (cycle proof)

H1(tmp, x) & tmp = x

 H2(tmp, x, b) * x::node<_,b> & tmp = x

H2(tmp, x, b) * x::node<_,b> & tmp = x & x'= b

H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

relations:
H(x) -> H1(tmp,x) & tmp = x
H1(tmp,x) -> H2(tmp, x, b) * x::node<_,b>
H2(tmp, x, b) * tmp::node<_,null> -> H3(tmp, x, b, c)
H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

normalization
H(x) -> H1(tmp,x) & tmp = x
H1(tmp,x) -> H2(tmp, x, b) * x::node<_,b>
H2(tmp, x, b) --> tmp::node<_,null> * H3(tmp, x, b, c)
H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

expect:
H(x) -> H3(b) * x::node<_,b>
H3(b) * x::node<_,b> & x'= b -> G(x,x')



*/


/* return the tail of a singly linked list */
node get_next(node x)
  infer[H,G]
  requires H(x)
  ensures G(x,res);//n>=1 & n=m+1
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/*
H(x) --> x::node<_,b> * HP_1285(b,x)
HP_1285(b,x) * x::node<val_214_1294,next_215_914'> --> G(x,b)

normalize
H(x) --> x::node<_,b> * HP_1285(b)
HP_1285(b) * x::node<val_214_1294,next_215_914'> --> G(x,b)
//lost infomation

expect:
H(x) -> x::node<_,b> * H(x,b)
x::node<_,b> * H(x,b) & tem = b

x::node<_,b'> * H(x,b) & tem = b * b' = null
 
x::node<_,b'> * H(x,b) & tem = b * b' = null -> G(x,b)
normalize:

H(x) -> x::node<_,b> * H(b)
x::node<_,b'> * H(b) * b' = null -> G(x,b)





*/




/* function to set the tail of a list */
relation SN(int m, int n).
void set_next(node x, node y)
  infer[SN]
  requires x::ll<i> * y::ll<j> & x!=null
  ensures x::ll<k> & SN(k,j); // k>=1 & k=j+1
{
  x.next = y;
}

void set_null2(ref node x)
//infer[x]
  requires x::ll<i> & x!=null
  ensures x'::node<_,null>;//'
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

/* function to set null the tail of a list */
void set_null(ref node x)
//infer[x]
  requires x::ll<i> & x!=null
  ensures x'::node<_,null>;//'
{
  x.next = null;
}

/* function to get the third element of a list */
relation GNN(int m, int n).
node get_next_next(node x)
  infer[n,GNN]
  requires x::ll<n> & x!=null //2<=n
  ensures res::ll<m> & GNN(m,n); //n>=2 & n=m+2
{
  return x.next.next;
}

/* function to insert a node in a singly linked list */
relation INS(int m, int n).
void insert(node x, int a)
  infer[INS]
  requires x::ll<n> & x!=null //1<=n
  ensures x::ll<m> & INS(m,n);//m>=2 & m=n+1
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

/* function to delete the a-th node in a singly linked list */
relation DEL(int m, int n, int p).
void delete(node x, int a)
  infer[n,a,DEL]
  requires x::ll<n>//& 1<=a & a<n
  ensures x::ll<m> & DEL(m,n,a);//a>=1 & m>=a & m+1=n;//DEL(m,n,a);
{
  if (a == 1){
    x.next = x.next.next;
  }
  else	{
    delete(x.next, a-1);
  }
}

/* function to delete the a node in a singly linked list */
relation DEL2(int m, int n).
node delete2(node x, int a)
  infer[DEL2]
  requires x::ll<n> //& 0<=n
  ensures res::ll<m> & DEL2(m,n);// EXPLAIN: m>=0 & (m+1)>=n & n>=m ==> n=m | n=m+1
{
	if (x == null)
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete2(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
relation CL(int a, int b).
node create_list(int n, int v)
  infer[CL]
  requires true
  ensures res::ll<m> & CL(m,n);//m=n
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n  = n - 1;
    tmp = create_list(n, v);
    return new node (v, tmp);
  }
}

/* function to reverse a singly linked list */
relation REV(node x, int k, int m, int n).
void reverse(ref node xs, ref node ys)
  infer[REV]
  requires xs::ll<n> * ys::ll<m> //0<=m & 0<=n
  ensures ys'::ll<k> & REV(xs',k,m,n);// xs' = null & m>=0 & k>=m & k=n+m
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

/* function to divide a list into 2 lists, the first one containing a elements and the second the rest */
relation SPLIT(int a, int b, int c, int d).
node split1(ref node x, int a)
  infer[SPLIT,n,a]
  requires x::ll<n> // 1<=a & a<=n
  ensures x'::ll<n1> * res::ll<n2> & SPLIT(n,a,n1,n2); //' n2>=0 & n>=(1+n2) & n=n1+n2 & n=a+n2
{
	node tmp;
	if (a == 1)
	{
		tmp = x.next; 
		x.next = null;
		return tmp;
	}
	else
	{
		a = a - 1;
		node tmp;
		bind x to (_, xnext) in {
			tmp = split1(xnext, a);
		}
		return tmp;
	}
}

/*****************************************/
/*********SMALLROOT EXAMPLES*************/
relation TRAV(int k, int m).
void list_traverse(node x)
  infer[TRAV]
  requires x::ll<n> //0<=n
  ensures x::ll<m> & TRAV(m,n); //m>=0 & m=n
{
  node t;
  if(x != null) {
    t = x;
    //process t
    list_traverse(x.next);
  }
}

relation CPY(int k, int m).
node list_copy(node x)
  infer[CPY]
  requires x::ll<n> //0<=n
  ensures x::ll<n> * res::ll<m> & CPY(m,n); //m>=0 & m=n
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}

/*function to remove the first node which has value v in singly linked list*/
relation RMV(int k, int m).
void list_remove(node x, int v)
  infer[RMV,x]
  requires x::ll<n> //& x!=null & 1<=n
  ensures x::ll<m> & RMV(m,n); // m>=1 & (m+1)>=n & n>=m
{
  if(x.next != null) {
    if(x.next.val == v) {
      node tmp = x.next;
      x.next = x.next.next;
      dispose(tmp);
    }
    else {
      list_remove(x.next, v);
    }
  }
}

/*function to remove the first node which has value v in nullable singly linked list*/
relation RMV2(int k, int m).
node list_remove2(node x, int v)
  infer[RMV2]
  requires x::ll<n> //n>=0
  ensures res::ll<m> & RMV2(m,n); //m+1)>=n & m>=0 & n>=m
{
  node tmp;
  if(x != null) {
    if(x.val == v) {
      tmp = x;
      x = x.next;
      dispose(tmp);
    }
    else {
      tmp = list_remove2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}

/*function to remove all nodes which have value v in nullable singly linked list*/
relation FIL(int k, int m).
node list_filter2(ref node x, int v)
  infer[FIL]
  requires x::ll<n> // n>=0
  ensures res::ll<m> & FIL(m,n); //m>=0 & n>=m
{
  node tmp;
  if(x != null) {
    if(x.val == v){
      tmp = x.next;
      dispose(x);
      x = tmp;
      x = list_filter2(x,v);
    }
    else{
      tmp = list_filter2(x.next, v);
      x.next = tmp;
    }
  }
  return x;
}
/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/
/* function to return the first node being greater than v*/
relation FGE(int k, int m).
node find_ge(node x, int v)
  infer[FGE]
  requires x::ll<n>
  ensures res = null or res::node<m,_> & FGE(m,v); // m>=(1+v)
{
  if(x == null)
    return null;
  else {
    if(x.val > v)
      return x;
    else
      return find_ge(x.next, v);
  }
}

/*function to splice 2 linked list*/
relation SPLICE (int a, int b, int c).
void splice (ref node x, node y)
  infer [SPLICE]
  requires x::ll<n> * y::ll<m> // 0<=m & 0<=n
  ensures x'::ll<t> & SPLICE(t,m,n); //' m>=0 & t>=m & t=n+m
{
  if(x == null)
    x = y;
  else {
    if(y != null){
      node nx = x.next;
      node ny = y.next;
      x.next = y;
      splice(nx, ny);
      y.next = nx;
    }
  }
}
