/*
 * linked list with 2 dummy nodes head and tail: ll_ht
 * 
 * NOT working. There is something wrong with transitivity of emtailment
 * See sll-ht.slk for more detail
 */

data node {
	int val; 
	node next;	
}
/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/
/*
// sorted linked list
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;
*/


ll_tail<n, t> ==
  self::node< _, null> & t=self & n=0  //empty list
  or self::node<sm, r> * r::ll_tail<n-1, t> & r!=null  
  inv n>=0 & self!=null & t!=null;




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

ll_ht<n, h, t> == self::node<_, r> * r::ll_tail<n, t> & self=h
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

//coercion "tail2ll" self::sll_tail<n, t, sm, lg> -> self::ll<n+1>;
//coercion "ht2ll" self::sll_ht<n, h, t, sm, lg> -> self::ll<n+2>;

//coercion "tail22ll" self::sll_tail2<n, t, sm, lg> -> self::ll<n+1>;
//coercion "ht22ll" self::sll_ht2<n, h, t, sm, lg> -> self::ll<n+2>;

coercion "ht22tail" self::ll_ht<n, h, t> <-> self::ll_tail<n+1,t>;
coercion "stail2sht" self::sll_tail<n+1,t, sm, lg> -> self::sll_ht<n,_,t,sm1,lg1>;

node delete2(node x, int v)

  requires x::sll_ht<n, h, t, sm, lg>
  case{
      n=0 -> ensures res::sll_ht<n,h,t,sm,lg>;
      n=1 -> case {
        v=sm -> ensures res::sll_ht<0,_,t,_,_>;
        v!=sm -> ensures res::sll_ht<n,h,t,sm,lg>;
         }
      n>1 -> ensures true; //res::sll_ht<m,_,t, sm1, lg1> & n-1<=m<=n & sm1 >= sm & lg1 <= lg;
      n<0 -> ensures false;
  }

/* //TRUE */
/*   requires x::ll_ht<n, _, t> */
/*   case{ */
/*     n=0 -> ensures res::ll_ht<n, _, t>; */
/*     n>0 -> ensures res::ll_ht<m, _, t> & n-1<=m<=n; */
/*     n<0 -> ensures false; */
/*   } */

{
	node tmp; 

	if (x.next.next != null){
      //assume false;
      if (v < x.next.val){
        //assume false;
		return x;
      }else
          if (v == x.next.val){
            //assume false;
            return x.next; // advance the head node to delele an element
          }
			else
			{
              //assume false;
			  tmp = x.next;
              node tmp1 = delete2(tmp, v);
              x.next = tmp1; 
              //assume false;
			  return x;
            }
    }
	else
      return x; //dummy head
}
