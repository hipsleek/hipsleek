data node {
  int val;
  node next;
}
             
bigint<b, v> == self = null & v = 0 & b>1 or
                 self::node<p, q> * q::bigint<b, v1> & 0 <= p < b & v = b*v1 + p & v1>0 & b>1
                 inv v >= 0 & b>1;


bool is_zero(node x)
  requires x::bigint<b, v>
  ensures x::bigint<b, v> & res & v = 0 or x::bigint<b, v> & !res & v > 0;
/*
  requires x::bigint<b, v>
   case {
       v=0 -> ensures res;
       v!=0 -> ensures !res;
   }    
*/
{
  if (x == null) {
    return true;
  }
  else {
     
      return false;
  }
  /*
  if (x.val == 0 && is_zero(x.next)) return true;
  return false;
  */
}

bool is_equal(node x, node y)
 
requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & res;
  v1>v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & !res;
  v1<v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & !res;
 }



/*
 requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures  res;
  v1!=v2 -> ensures  !res;
  }

2 false contexts at: ( (113,8)  (113,15) )

Total verification time: 7.44 second(s)
        Time spent in main process: 3.83 second(s)
        Time spent in child processes: 3.61 second(s)

  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures res & v1 = v2 or !res & v1 != v2;

0 false contexts at: ()

Total verification time: 13.51 second(s)
        Time spent in main process: 7.82 second(s)
        Time spent in child processes: 5.69 second(s)

  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures res & v1 = v2 or !res & v1 != v2;

  ==> takes 12.3 s

  requires x::bigint<b, v1> * y::bigint<b, v2> & b>1
  ensures x::bigint<b, v1> * y::bigint<b, v2> & res & v1 = v2 
    or x::bigint<b, v1> * y::bigint<b, v2> & !res & v1 != v2;

  ==> takes 92s
fails-->

requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures  res;
  v1!=v2 -> ensures  !res;
  }

  requires x::bigint<b, v1> * y::bigint<b, v2> & v1=v2
  ensures res;
  requires x::bigint<b, v1> * y::bigint<b, v2> & v1!=v2
  ensures !res;

requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures  res;
  v1>v2 -> ensures  !res;
  v1<v2 -> ensures !res;
 }
 requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & res;
  v1>v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & !res;
  v1<v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & !res;
 }

2 false contexts at: ( (132,8)  (132,15) )

Total verification time: 24.75 second(s)
        Time spent in main process: 16.92 second(s)
        Time spent in child processes: 7.83 second(s)

  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures x::bigint<b, v1>* y::bigint<b, v2> & res & v1 = v2 or 
        x::bigint<b, v1>* y::bigint<b, v2> & !res & v1 != v2;

Total verification time: 89.28 second(s)
        Time spent in main process: 66.99 second(s)
        Time spent in child processes: 22.29 second(s)

*/
{

  if (x == null || y == null) {
    //assert y'!=null; //'
    //assert y'!=null; //'
    assume false;
    return is_zero(x) && is_zero(y);
  } else {
    bool bb=is_equal(x.next, y.next);
    int m=x.val; int n=y.val;
    //assume n<m or n=m or n>m;
    if (m == n) {
       assume false;
        return bb;
      }
    else 
      { //assert false;
        //assume false;
        return false;
      }
  }

}

 
