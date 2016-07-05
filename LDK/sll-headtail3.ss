/*
 * linked list with 2 dummy nodes head and tail: ll_ht
 */

data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/*
// sorted linked list
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;
*/



// increasingly sorted list with dummy tail

sll_tail<n, t, sm, lg> ==
  self::node< _, null> & t=self & n=0 & sm<=lg //empty list
  or self::node<sm, r> * r::sll_tail<n-1, t, _, _> & r!=null  & n=1 & sm=lg
  or self::node<sm, r> * r::sll_tail<n-1, t, sm1, lg> & r!=null & sm<=sm1 & n>1
  inv n>=0 & self!=null & sm<=lg & t!=null;


/*
sll_tail<n, t, sm, lg> == 
  self::node< _, null> & t=self & n=0 & sm=lg //empty list
  /* or self::node<sm, r> * r::sll_tail<n-1, t, sm, lg> & r!=null & sm=lg & n=1 */
  or self::node<sm, r> * r::sll_tail<n-1, t, sm1, lg> & r!=null & sm<=sm1
  inv n>=0 & self!=null & sm<=lg & t!=null;
*/


/*
// decreasingly sorted list with dummy tail
sll_tail2<n, t, lg, sm> == self::node< _, null> & t=self & n=0 & lg=sm //empty list
  or self::node<lg, r> * r::sll_tail<n-1, t, lg, sm> & r!=null & lg=sm & n=1
  or self::node<lg, r> * r::sll_tail<n-1, t, lg1, sm> & r!=null & lg>=lg1
  inv n>=0 & self!=null;

*/

/*
sll_tail<n, t, sm, lg> == self::node<sm, t> * t::node< _, null> & n=1 & sm=lg
		or self::node<sm, r> * r::sll_tail<n-1, t, sm1, lg> & r!=null & sm<=sm1
	inv n>=0 & self!=null;
*/

/*
sll_tail<n, t, sm, lg> == self::node<sm, t> * t::node< _, null> & n=1 & sm=lg
  or (exists qs, ql: self::node<qmin, r> * r::sll_tail<n-1, t, qs, ql> & r!=null & qmin <= qs & ql <= lg & sm <= qmin )
	inv n>=0 & self!=null;
*/

// increasingly sorted list with dummy head and tail
sll_ht<n, h, t, sm, lg> == self::node<_, r> * r::sll_tail<n, t, sm, lg> & self=h
  inv n>=0 & self!=null;

/*
// decreasingly sorted list with dummy head and tail
sll_ht2<n, h, t, lg, sm> == self::node<_, r> * r::sll_tail2<n, t, lg, sm> & self=h
  inv n>=0 & self!=null;
*/

/*
// bounded list with tail, not sorted
bnd_tail<n, t, sm, lg> ==  self::node< _, null> & t=self & n = 0 & sm <= lg
	or self::node<v, t> * t::node< _, null> & n = 1 & sm <= v <= lg
    or self::node<d, p> * p::bnd_tail<n-1, t, sm, lg> & sm <= d <= lg & p!=null
inv n >= 0 & self!=null;

// bounded list with dummy head and tail
bnd_ht<n, h, t, sm, lg> == self::node<_, r> * r::bnd_tail<n, t, sm, lg> & self=h
  inv n>=0 & self!=null;
*/

coercion "tail2ll" self::sll_tail<n, t, sm, lg> -> self::ll<n+1>;
coercion "ht2ll" self::sll_ht<n, h, t, sm, lg> -> self::ll<n+2>;

//coercion "tail22ll" self::sll_tail2<n, t, sm, lg> -> self::ll<n+1>;
//coercion "ht22ll" self::sll_ht2<n, h, t, sm, lg> -> self::ll<n+2>;

/*
 * Get the head node of a linked list with dummy tail node
 */

node get_head(node x)

//  requires x::sll_tail<n, t, sm, lg>
//  ensures (n=0 & res=null) or (res!=null & n>0);
//  ensures n=0 & res=null
//  or res::node<v, p> & n>0;
 requires x::sll_tail<n, t, sm, lg>
 case {
  n=0 -> ensures res=null;
  n>0 -> ensures res::node<v, p>;
  n<0 -> ensures false;
 }

{
  if (x.next==null){
    return null;
  }else{
    return x;
  }
}

/*
 * Get the head node of a linked list with dummy tail and head nodes
 */

node get_head2(node x)

//  requires x::sll_tail<n, t, sm, lg>
//  ensures (n=0 & res=null) or (res!=null & n>0);
//  ensures n=0 & res=null
//  or res::node<v, p> & n>0;
  requires x::sll_ht<n, h, t, sm, lg>
 case {
  n=0 -> ensures res=null;
  n>0 -> ensures res::node<v, _> * h::node<_, p> & p!=null & res = p;
  //  n>0 -> ensures res::node<_, _>;
  n<0 -> ensures res=null;
 }

{
  if (x.next.next==null){
    return null;
  }else{
    return x.next;
  }
}


/*
 * Get the tail of a linked list with dummy tail node
 * exclude the head
 */

node get_tail(node x)

  requires x::sll_tail<n, t, sm, lg>
 case {
  n=0 -> ensures res=null;
  n=1 -> ensures x::node<sm, res> * res::sll_tail<n-1, t, _, _> & sm=lg;
  n>1 -> ensures x::node<sm, res> * res::sll_tail<n-1, t, sm1, lg> & sm<=sm1;
  //or  n>=1 -> ensures x::node<sm, res> * res::sll_tail<n-1, t, _, _>;
  n<0 -> ensures false;
 }
// or res::sll_tail<n-1, t, sm1, lg> & sm<=sm1;
//  or res::sll_tail<n-1, t, sm1, lg1> & n>0 & sm<=sm1<=lg1 & lg1<=lg;

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
 * Get the tail of a linked list with dummy tail and head nodes
 * exclude the head
 */

node get_tail2(node x)

  requires x::sll_ht<n, h, t, sm, lg>
  ensures res=null & n = 0
  or h::node<_, p> * res::sll_ht<n-1, p , t, sm1, lg> & sm<=sm1 & n>0;

{
  //return new node(1,null);
  if (x.next.next==null){
    return null;
  }else{
    return x.next;
  }
}



global node y=null;

/*
 * Test linked lists with a dummy tail
 */

void test()

 ensures y'::sll_tail<_, _, _, _>;
//  ensures y'::node<_, _>;

{
  node z = new node(100,null);
  node z2 = new node (10,z);
  node z3 = new node (9, z2);
    y = z;
    //y = z2;
    // y = new node(2,z);
    //y = new node(1, z2);
    y = new node(8,z3); //8 -> 9 -> 10 
  //y = new node(1,null);

    node z4=y.next; // 9
    node z5=new node(9,z4); // 8<= 9 <=9
    y.next=z5;

  //y=null;
}
/*
 * Test linked lists with dummy tail and head
 */
void test2()

//  ensures y'!=null;
//  ensures y'::sll_tail<_, _, _, _>;
  ensures y'::sll_ht<_, _, _, _, _>;

{
  node z = new node(100, null);
  node z1 = new node(10,z);
  node z2 = new node(9,z1);
  node z3 = new node(8,z2);
  //y = z;
  y = z1;
  //y = z2;
  //y = z3;
  //y = new node(100,z3);
  //y = null;
}

/* 'insert an element in a sorted list with a dummy tail*/
//???

node insert(node x, int v)

  requires x::sll_tail<n, t, sm, lg>
 case {
  n=0 -> ensures res::sll_tail<1, t, v, v>;
  n>=1 -> ensures res::sll_tail<n + 1, t, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 
  n<0 -> ensures false;
 }

// other, not tested
//  requires x::sll_tail<n, t, sm, lg>
//  ensures res::sll_tail<n + 1, t, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 
//  requires x::sll_tail<n, _, _, _>
//  ensures res::sll_tail<n + 1, _, _, _>;
//    requires x::ll<n> & n>0
//    ensures res::ll<n+1>;

{
//    return new node(v, x);

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


/* insert an element in a sorted list with dummy head and tail nodes*/

/*
node insert2(node x, int v)

  requires x::sll_ht<n, h, t, sm, lg>
  ensures res::sll_ht<n + 1, h, t, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 

{
	node tmp;
    node node;

	if (x.next.next == null){
      //empty list
		tmp = x.next;
        node = new node(v,tmp);
		x.next = node;
		return x;
    }else{
      if (v <= x.next.val){
   		tmp = x.next;
        node = new node(v,tmp);
		x.next = node;
		return x;
      }else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}
*/

/* delete a node from a sorted list with a dummy tail node */

node delete(node x, int v)

  requires x::node<sm,r>
  case{
  r=null -> ensures res::sll_tail<0,_,_,_> & res=x;
    r!=null -> requires r::sll_tail<n,t,sm1,lg1>//ensures true; //res=x;
 case{
      v<sm -> case{
        n=0 -> ensures x::sll_tail<n+1,t,sm,lg> & sm=lg & res=x;
        n>0 -> requires sm<=sm1 & sm1<=lg1
               ensures x::sll_tail<n+1,t,sm,lg1> & res=x;
        n<0 -> ensures true;
      }
      v=sm -> //ensures res=r;
    case{
        n=0 -> ensures x::sll_tail<n+1,t,sm,lg> & sm=lg & res=r;
        n>0 -> requires sm<=sm1 & sm1<=lg1
               ensures x::sll_tail<n+1,t,sm,lg1> & res=r;
        n<0 -> ensures true;
      }
    /* case{ */
    /*     n=0 -> ensures res::sll_tail<0,_,_,_>; */
    /*     n>0 -> ensures res=r; */
    /*     n<0 -> ensures true; */
    /*   } */
      v>sm ->
    case{
        n=0 -> ensures x::sll_tail<n+1,t,sm,lg> & sm=lg & res=x;
        n>0 -> ensures true;//requires sm<=sm1 & sm1<=lg1
               //ensures  x::sll_tail<n+1,t,sm,lg1> * res::sll_tail<n1,t,sm2,lg2> & n<=n1 & n1<=n+1 & sm<=sm2 & lg2<=lg1;
        n<0 -> ensures true;
      }
    }
  }
  /* requires x::sll_tail<n, t, sm, lg> */
  /* case{ */
  /*     n=0 -> ensures res=x; */
  /*     n>0 -> ensures res::sll_tail<_, t, _, _>; // & sm1 >= sm & lg1 <= lg; // & n-1 <= n1 <= n;; */
  /*     n<0 -> ensures false; */
  /* } */
//ensures res::sll_tail<n1, t, sm1, lg1> ;//&  n-1 <= n1 <= n; // & sm1 >= sm & lg1 <= lg; // & n-1 <= n1 <= n;

{
  //return x;
	node tmp; 
	if (x.next != null){
      //assume false;
		if (v < x.val)
			return x;
		else{
          //assume false;
		  if (v == x.val){
            //assume false;
            return x.next;
            //return x;
          }else{
            //assume false;
            tmp = x.next;
            node tmp1 = delete(tmp, v);
			x.next =tmp1;
			return x;
		  }
        }
    }else
      return x; //dummy tail
}

/* delete a node from a sorted list with dummy head and tail nodes */

node delete2(node x, int v)

  requires x::sll_ht<n, h, t, xs, xl>
  ensures res::sll_ht<nres, hres, t, sres, lres> & sres >= xs & lres <= xl & n-1 <= nres <= n; //Note: head node can be changed

{
	node tmp; 

	if (x.next.next != null)
		if (v < x.next.val)
			return x;
		else
			if (v == x.next.val)
              return x.next; // advance the head node to delele an element
			else
			{
				tmp = x.next;
				x.next = delete(tmp, v);
				return x.next;
			}
	else
      return x; //dummy head
}

/* function to reverse a singly linked list with dummy head and tail
 * from increasing to decreasing 
 */
//???
/*
node reverse(node x)
//  requires x=null
//  ensures res=null;

//  requires x::node<v,null>
//  ensures res::node<v, null> & res = x;

//  requires x::sll_tail<n ,t, sm, lg>
//  ensures res::ll<n+1>;

//  requires x::sll_ht<n, h, t, sm, lg>
//  ensures res::ll<n+2>;

//  requires x::sll_ht2<n, h, t, sm, lg>
//  ensures res::ll<n+2>;

//  requires x::sll_ht<n, h, t, sm, lg>
//  ensures res::sll_ht2<n, t, h, lg, sm>;

  requires x::ll<n>
  ensures res::ll<n>;

{
  node curr = x;
  node hd = null;
  node tmp = hd;

  while (curr !=null)

      ensures curr=null & tmp'=hd'
      or curr::node<v, p> * tmp'::node<v,hd> &hd'=tmp' & curr'=p;

  { //
    tmp=curr;
    curr = curr.next;
    tmp.next = hd;
    hd = tmp;
  }
  return hd;
}
*/
