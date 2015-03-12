/*
 * linked list with 2 dummy nodes head and tail: ll_ht
 */

data node {
	int val; 
	node next;	
}

// increasingly sorted list with dummy tail

sll_tail<n, t, sm, lg> ==
  self::node< _, null> & t=self & n=0 & sm<=lg //empty list
  or self::node<sm, r> * r::sll_tail<n-1, t, _, _> & r!=null  & n=1 & sm=lg
  or self::node<sm, r> * r::sll_tail<n-1, t, sm1, lg> & r!=null & sm<=sm1 & n>1
  inv n>=0 & self!=null & sm<=lg & t!=null;

ll_tail<n, t> ==
  self::node< _, null> & t=self & n=0  //empty list
  or self::node<sm, r> * r::ll_tail<n-1, t> & r!=null  
  inv n>=0 & self!=null & t!=null;


/* delete a node from a sorted list with a dummy tail node */

node delete(node x, int v)

  /* requires x::node<sm,r> */
  /* case{ */
  /*   r=null -> ensures res::sll_tail<0,_,_,_> & res=x; */
  /*   r!=null -> requires r::sll_tail<n,t,sm1,lg1>//ensures true; //res=x; */
  /*   case{ */
  /*     v<sm -> ensures res=x; */
  /*     /\*  case{ *\/ */
  /*     /\*   n=0 -> ensures x::sll_tail<n+1,t,sm,lg> & sm=lg & res=x; *\/ */
  /*     /\*   n>0 -> requires sm<=sm1 & sm1<=lg1 *\/ */
  /*     /\*          ensures x::sll_tail<n+1,t,sm,lg1> & res=x; *\/ */
  /*     /\*   n<0 -> ensures true; *\/ */
  /*     /\* } *\/ */
  /*     v=sm -> ensures res=r; */
  /*      /\* case{ *\/ */
  /*      /\*  n=0 -> ensures x::sll_tail<n+1,t,sm,lg> & sm=lg & res=r; *\/ */
  /*      /\*  n>0 -> requires sm<=sm1 & sm1<=lg1 *\/ */
  /*      /\*         ensures x::sll_tail<n+1,t,sm,lg1> & res=r; *\/ */
  /*      /\*  n<0 -> ensures true; *\/ */
  /*      /\* } *\/ */
  /*     v>sm -> */
  /*      case{ */
  /*       n=0 -> ensures res::sll_tail<n+1,t,sm,sm>; */
  /*       n>0 -> ensures true; */
  /*         //requires sm<=sm1 */
  /*         ensures res::node<sm,r1> * r1::sll_tail<n1,t,sm2,lg2> & n-1<=n1<=n & sm1<=sm2 & lg2<=lg1; */

  /*         //requires sm<=sm1 & sm1<=lg1 */
  /*         //ensures  x::sll_tail<n+1,t,sm,lg1> * res::sll_tail<n1,t,sm2,lg2> & n<=n1 & n1<=n+1 & sm<=sm2 & lg2<=lg1;  */
  /*       n<0 -> ensures true; */
  /*      } */
  /*    } */
  /* } */

  requires x::sll_tail<n, t, sm, lg>
  case{
      n<=0 -> ensures res::sll_tail<n,t,sm,lg>;
      n=1 -> case {
         v=sm -> ensures res::sll_tail<0,t,_,_>;
         v!=sm -> ensures res::sll_tail<n,t,sm,lg>;
         }
      n>1 -> ensures res::sll_tail<m, t, sm1, lg1> & n-1<=m<=n
        & sm1 >= sm & lg1 <= lg; // & n-1 <= n1 <= n;;
      //n<0 -> ensures false;
  }
  /* ensures res::sll_tail<n1, t, sm1, lg1> &  n-1 <= n1 <= n & sm1 >= sm & lg1 <= lg; // & n-1 <= n1 <= n; */

/*
  requires x::ll_tail<n, t>
  case{
      n<=0 -> ensures res::ll_tail<n,t>;
      n>0 -> ensures res::ll_tail<m, t> & n-1<=m<=n;
  }
*/
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
