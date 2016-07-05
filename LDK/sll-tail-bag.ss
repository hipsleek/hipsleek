/*
 * linked list with a dummy tail with bags (sets of values): ll_tb
 */

data node {
	int val; 
	node next;	
}

/* // increasingly sorted list with a dummy tail and a bag of values*/

sll_tb<n, t, sm, lg, S> ==
  self::node< _, null> & t=self & n=0 & sm<=lg & S={} //empty list
  or self::node<sm, r> * r::sll_tb<n-1, t, _, _, S1> & r!=null  & n=1 & sm=lg & S=union(S1,{sm})
  or self::node<sm, r> * r::sll_tb<n-1, t, sm1, lg, S1> & r!=null & sm<=sm1 & n>1 & S=union(S1,{sm})
  inv n>=0 & self!=null & sm<=lg & t!=null;

// linked list with dummy tail
ll_tb<n, t, S> ==
  self::node< _, null> & t=self & S ={} & n=0  //empty list
  or self::node<sm, r> * r::ll_tb<n-1, t, S1> & S= union(S1,{sm}) & r!=null
  & forall(x:(x notin S1 | sm<=x)) 
  inv n>=0 & self!=null & t!=null;

/*
 * Get the first node of a linked list with dummy tail node
 */

node get_head(node x)

  requires x::sll_tb<n, t, sm, lg, S>
 case {
  n<=0 -> ensures res=null;
  n>0 -> ensures x::node<v, _> & res=x & v in S;
  //n<0 -> ensures false;
 }

  /* requires x::ll_tb<n, t, S> */
  /* case{ */
  /*     n<=0 -> ensures res=null; */
  /*     n>0 -> ensures x::node<v, _> & res=x & v in S; */
  /* } */

{
  if (x.next==null){
    return null;
  }else{
    return x;
  }
}

/* /\* */
/*  * Get the tail of a linked list with dummy tail node */
/*  * exclude the head */
/*  *\/ */


node get_tail(node x)

  requires x::sll_tb<n, t, sm, lg, S>
 case {
  n<=0 -> ensures res=null;
  n=1 -> ensures x::node<sm, res> * res::sll_tb<n-1, t, _, _, S1> & sm=lg & S=union(S1,{sm});
  n>1 -> ensures x::node<sm, res> * res::sll_tb<n-1, t, sm1, lg, S1> & sm<=sm1 & S=union(S1,{sm});
  //n<0 -> ensures false;
 }

  /* requires x::ll_tb<n, t, S> */
  /* case{ */
  /*     n<=0 -> ensures res=null; */
  /*     n>0 -> ensures x::node<sm, res> * res::ll_tb<n-1, t, S1> & sm in S;  */
  /*     //& sm notin S1 is not true because we might have many same values in the list; */
  /* } */

{
  if (x.next==null){
    //assume false;
    // x is the dummy tail
    return null;
  }else{
    //assume false;
    //dprint;
    return x.next;
  }
}


/*
 * insert an element in a sorted list with a dummy tail
 */

node insert(node x, int v)

  requires x::sll_tb<n, t, sm, lg, S>
 case {
  n<=0 -> ensures res::sll_tb<1, t, v, v, S1> & S1=union(S,{v});
  n>=1 -> ensures res::sll_tb<n + 1, t, mi, ma, S1> & mi = min(v, sm) & ma = max(v, lg) & S1=union(S,{v});
  //n<0 -> ensures false;
} //NOTE: successful with "-tp om" but not "-tp mona"

/* // test shape and size of a link list */
/*   requires x::ll_tb<n, t, S> */
/*   ensures res::ll_tb<n+1, t, S1> & S1 = union(S, {v}); */

{
	node tmp;
    node z;

	if (x.next == null){
      //tail node, empty list
        z = new node(v,x);
		return z;
    }else{
      //assume false;
      if (v <= x.val){
        z = new node(v,x);
		return z;
      }else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}


/*
 * Delete a node from a sorted list with a dummy tail node
*/

node delete(node x, int v)

//shape, size and sortedness
  /* requires x::sll_tb<n, t, sm, lg, S> */
  /* case{ */
  /* n<=0 -> ensures res::sll_tb<n,t,sm,lg,S> & S={}; */
  /*     n=1 -> case { */
  /*       v=sm -> ensures res::sll_tb<0,t,_,_,S> & S={}; */
  /*       v!=sm -> ensures res::sll_tb<n,t,sm,lg, S1> & S1=S; */
  /*        } */
  /*     //??? fail */
  /*     n>1 -> ensures res::sll_tb<m, t, sm1, lg1, S1> & n-1<=m<=n & sm1 >= sm & lg1 <= lg & (v notin S & S = S1 | S = union(S1, {v})); */

  /*     // ??? mona failed  */
  /*     //n>1 -> ensures res::sll_tb<m, t, sm1, lg1, S1> & sm1 >= sm & lg1 <= lg & (m=n & v notin S & S = S1 | m=n-1 & S = union(S1, {v})); */

  /*     //n<0 -> ensures false; */
  /* } */

// test shape and size of a link list
  requires x::ll_tb<n, t, S>
  case{
  n<=0 -> ensures res::ll_tb<n,t,S>;
  n>0 -> case {
    v in S -> ensures res::ll_tb<m,t,S1> & S=union(S1,{v}) & m=n-1;
    v notin S -> ensures res::ll_tb<n,t,S>;
  }
}
{
  //return x;
	node tmp;
	if (x.next != null){
        //assume false;
		if (v < x.val) {
			return x;
		} else{
          //assume false;
		  if (v == x.val){
            //assume false;
            return x.next;
          }else{
            tmp = x.next;
            node tmp1 = delete(tmp, v);
			x.next =tmp1;
            //assume false;
 			return x;
		  }
        }
    }else
      return x; //dummy tail
}

/* /\* */
/*  * Test linked lists with a dummy tail */
/*  *\/ */

/* global node y=null; */
/* void test() */

/*  ensures y'::sll_tail<_, _, _, _>; */
/* //  ensures y'::node<_, _>; */

/* { */
/*   node z = new node(100,null); */
/*   node z2 = new node (10,z); */
/*   node z3 = new node (9, z2); */
/*     y = z; */
/*     //y = z2; */
/*     // y = new node(2,z); */
/*     //y = new node(1, z2); */
/*     y = new node(8,z3); //8 -> 9 -> 10  */
/*   //y = new node(1,null); */

/*     node z4=y.next; // 9 */
/*     node z5=new node(9,z4); // 8<= 9 <=9 */
/*     y.next=z5; */

/*   //y=null; */
/* } */
