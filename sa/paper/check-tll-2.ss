// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b).

bool check_tll(node x,node t,ref node r)
   infer [H,G] requires H(x,t) ensures G(x,t) & res;
   //requires x::tll<t,ggg>@L ensures res & r'=ggg;
{
  if (x.right==null) 
  	{
                r = x.next;
  	  	return t==x && x.left==null;
  	}
  else 
  	{
  		node r_most;
                if (x.left==null) return false;
                bool b = check_tll(x.left, t, r_most);
  		return b && check_tll(x.right, r_most, r);
  	}
}

/*
# check-tll-2.ss --sa-dnc --pred-en-dangling

[ H(x_1075,t_1076) ::= x_1075::node<left_29_986,right_29_987,__DP_HP_991>@M
    * H(left_29_986,t_1076) * H(right_29_987,r_1074)&right_29_987!=null & left_29_986!=null
   \/  x_1075::node<left_29_986,right_29_987,__DP_HP_991>@M&right_29_987=null 
       & left_29_986=null,

G(x_1081,t_1082) ::= x_1081::node<left_29_986,right_29_987,__DP_HP_991>@M 
    * G(left_29_986,t_1082) * G(right_29_987,r_1058)&left_29_986!=null & right_29_987!=null
   \/  t_1082::node<left_29_986,right_29_987,__DP_HP_991>@M&t_1082=x_1081 
       & right_29_987=null & left_29_986=null]

*/
