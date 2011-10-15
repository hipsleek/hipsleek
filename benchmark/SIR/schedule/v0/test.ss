
data node2 {
	int val;
    int priority;
    node2 prev;
	node2 next;
}

dll<p,n> == self = null & n = 0 
  or self::node2<_ ,_,p , q> * q::dll<self, n-1> // = q1 
  inv n >= 0;

coercion self::dll<p,n> & a>=0 & b>=0 & n=a+b 
  <-> self::dll<q,a>*q::dll<p,b>;

dll2<p,r,l,n> == self=r & p=l & n=0 
  or self::node2<_,_,p,q> * q::dll2<self,r,l,n-1> // = q1 
  inv n >= 0;

/*
coercion self::dll2<p,r,l,n> & a>=0 & b>=0 & n=a+b 
  <- self::dll2<p,q,l1,a>*q::dll2<l1,r,l,b>;
*/

node2 get_first(node2 x)
  requires x::dll<p, n>//::node2<a,b,p,q> * p
  ensures x::dll<p, n> & res=x;
{
  return x;
}

int get_mem_count(node2 x)
  requires x::dll<q,n>
  ensures x::dll<q,n> & res=n;
{
  if (x==null) return 0;
  else {
    return (1+ get_mem_count(x.next));
  }
}

/*-----------------------------------------------------------------------------
  find_nth
        fetches the nth element of the list (count starts at 1)
 -----------------------------------------------------------------------------*/
node2 find_nth_helper(node2 l, int j)
/*
  requires l::dll<p, n> & n >= j & j>=1
  case {
    j=1 -> ensures res::dll<p,n> ;
    j!=1 -> ensures res::dll<_,m> & (m = n - j + 1) ;
  }
*/
/*
  requires l::dll2<p,r,z,n> & n >= j & j>=1
  case {
   j=1 -> ensures  res::dll2<p,r,z,n> & res=l;
  j!=1 -> ensures l::dll2<p,res,z1,j-1>
               *res::dll2<z1,r,z,m> & (m = n - j + 1) ; //'
  }
*/
  requires l::dll2<p,r,z,n> & n>=j & j>=1
  ensures res::dll2<z1,r,z,m> * l::dll2<p,res,z1,j-1>  & (m=n-j+1)
    & res!=null; 
  requires l::dll2<p,r,z,n>@I & n>=j & j>=1
  ensures res!=null; 

{
  if (j>1){
    //assume false;
    //j = j -1;
    node2 r2=find_nth_helper(l.next, j-1);
    //dprint;
    return r2;
  }
  else {
    //assume false;
     return l;
  }
}

node2 find_nth(node2 f_list, int j)
/*
  requires f_list::dll<p, n> & j<=n & j >=1
  ensures res::node2<_,_,_,_>;
*/
/*
  requires f_list::dll2<p,r,z,n> & n>=j & j>=1
  ensures res::dll2<z1,r,z,m> * f_list::dll2<p,res,z1,j-1>  & (m=n-j+1)
    & res!=null; 
*/
  requires f_list::dll2<p,r,z,n> & n>=j & j>=1
  ensures res::node2<_,_,z1,q>* q::dll2<res,r,z,m-1> 
    * f_list::dll2<p,res,z1,j-1>  & (m=n-j+1)
    & res!=null; 

{
  node2 f_ele;

  //f_ele = get_first(f_list);
  f_ele = find_nth_helper(f_list,j);
  return f_ele;
}


/*-----------------------------------------------------------------------------
  del_ele
        deletes the old_ele from the list.
        Note: even if list becomes empty after deletion, the list
	      node is not deallocated.
-----------------------------------------------------------------------------*/
node2 delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
	ensures x::dll<p, n-1> & res=x;
{
	node2 tmp;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		else
			x.next = null;
            }
	else {
		 tmp = delete(x.next, a-1);
         x.next = tmp;
         tmp.prev = x;
	}
    return x;
}

node2 del_ele(node2 x, int a)
	requires x::dll<p, n> & n > a & a >= 0 
	ensures res::dll<p, m> & m = n-1;
{
  if (a == 0){
    node2 tmp = x.next;
    if (tmp == null) return null;
    else {
      tmp.prev = x.prev;
      x = x.next;
      return tmp;
    }
  } else
    return delete(x,a);
}

void schedule(ref node2 prio_queue1, ref node2 cur_proc)
  requires  prio_queue1::dll<p1,n1>
 case{
  n1 > 0 -> ensures  prio_queue1'::dll<p1,n1> * cur_proc'::dll<_, _>;
  n1<=0 -> ensures prio_queue1'=null & cur_proc' = null;
    }
{
    int n;
    cur_proc = null;
    n = get_mem_count(prio_queue1);
    if (n > 0){
      assert(prio_queue1 != null);
      cur_proc = find_nth(prio_queue1, 1);
      assert(prio_queue1 != null);
      //dprint;
      prio_queue1 = del_ele(prio_queue1, 0);
      return;
    }
}
