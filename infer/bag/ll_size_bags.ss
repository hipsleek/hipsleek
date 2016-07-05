/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n, S> == self = null & n = 0 & S = {}
	or self::node<v, q> * q::ll<n-1, S1> & S = union(S1, {v}) 
  inv n >= 0;
  
lseg<p, n, S> == self=p & n=0 & S = {}
	or self::node<v, q> * q::lseg<p, n-1, S1> & S = union(S1, {v})
	inv n>=0;

//recursive
node append3(node x, node y)
  requires x::lseg<null, n, S>
  ensures res::lseg<y, n, S>;
{
	if (x == null) 
		return y;
	else {
		//assume false;
		node tmp = x.next;
		x.next = append3(tmp, y);
		return x;
	}
}

//recursive
/* append two singly linked lists */
void append2(node x, node y)
  requires x::ll<n1, S1> * y::ll<n2, S2> & x!=null
  ensures x::ll<n1+n2, S> & S = union(S1, S2);
{
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

//recursive
void append(node x, node y)
  requires x::ll<n1, S1> * y::ll<n2, S2> & n1>0
  ensures x::ll<n1+n2, S> & S = union(S1, S2);
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the tail of a singly linked list */
//success
/*
NEW SPECS: EBase exists (Expl)(Impl)[n; S](ex)x::ll<n,S>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&(1<=n | n<=(0-1)) & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 10::
                   x::ll<flted_64_73,S1>@M[Orig][LHSCase] * 
                   res::ll<flted_64_72,S2>@M[Orig][LHSCase]&
                   tmp_74_991'=q_940_990 & res=q_940_990 & 
                   v_node_68_772_992'=q_940_990 & v_939_993=v_949_998 & 
                   next_67_771_995'=q_950_994 & S1_941_1003=S2_1002 & 
                   flted_64_73_999=1 & flted_64_72_1000=flted_14_938_1001 & 
                   n=1+flted_14_938_1001 & q_950_994=null & 
                   S=union(S1_941_1003,{v_939_993}) & S1_951_997= & 
                   S1_951_997= & S1_996=union(S1_951_997,{v_949_998}) & 0<=n&
                   {FLOW,(20,21)=__norm}
 */
node get_next(node x)
  infer[n,res]
  requires x::ll<n, S> //& n > 0
  ensures x::ll<1, S1> * res::ll<n-1, S2> ;//& S  = union(S1, S2);
{
	node tmp = x.next;
    x.next = null;
	return tmp;
}
/*
NEW SPECS: EBase x::node<inf_val_76_921,inf_next_76_922>@M[Orig]&MayLoop&
       {FLOW,(1,23)=__flow}
         EAssume 12::
           x::node<inf_val_76_921,next_77_753'>@M[Orig]&inf_ann_920<=0 & 
           res=inf_next_76_922 & next_77_753'=null&{FLOW,(20,21)=__norm}
 */
node get_next1(node x)
  infer[x,res]
  requires true//x::ll<n, S> & n > 0
  ensures true;//x::ll<1, S1> * res::ll<n-1, S2> ;//& S  = union(S1, S2);
{
	node tmp = x.next;
    x.next = null;
	return tmp;
}

/* function to set the tail of a list */
/*
NEW SPECS: EBase x::node<inf_val_87_921,inf_next_87_922>@M[Orig]&MayLoop&
       {FLOW,(1,23)=__flow}
         EAssume 14::
           x::node<inf_val_87_921,y>@M[Orig]&inf_ann_920<=0&
           {FLOW,(20,21)=__norm}
 */
 void set_next(node x, node y)
   infer[x,y]
   requires true//x::node<v, _> * y::ll<j, S1>
   ensures true;//x::ll<j+1, S> & S = union({v}, S2);
{
	x.next = y;
}


/* function to set null the tail of a list */
void set_null(node x)
	requires x::node<v, _>
	ensures x::ll<1, {v}>;
{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 
	requires x::ll<n, _> & n > 1
	ensures res::ll<n-2, _>;
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n, S> & n > 0 
	ensures x::ll<n+1, S1> & S1 = union(S, {a});
{

    node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
	requires x::ll<n, _> & n > a & a > 0 
	ensures x::ll<n-1, _>;
{
    if (a == 1)
	{
		x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}

node delete1(node x, int a)
	requires x::ll<n, S>  
	case {
		a notin S -> ensures res::ll<n, S>;
		a in S -> ensures res::ll<n-1, S1> & S = union(S1, {a});
	}
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a, S> & forall(x: (x notin S | x = 0));

{
	node tmp;

	if (a == 0) {
		return null;
	}
	else {    
		a  = a - 1;
		tmp = create_list(a);	
		return new node (0, tmp);
	}	
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n, S1> * ys::ll<m, S2> 
	ensures ys'::ll<n+m, S> & xs' = null & S = union(S1, S2);
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
