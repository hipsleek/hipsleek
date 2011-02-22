data node {
  int val;
  node next;
}
             
bigint<b, v> == self = null & v = 0 & b>1 or
                 self::node<p, q> * q::bigint<b, v1> & 0 <= p < b 
                 & v = b*v1 + p & v>0 & b>1
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
 
  requires [b] x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures  res;
  v1!=v2 -> ensures  !res;
  }

/*
 requires x::bigint<b, v1> * y::bigint<b, v2>
 case {
  v1=v2 -> ensures  res;
  v1!=v2 -> ensures  !res;
  }

 false contexts at: ( (139,8)  (139,15) )

Total verification time: 6.5 second(s)
	Time spent in main process: 3.7 second(s)
	Time spent in child processes: 2.8 second(s)

  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures true & (res & v1 = v2 | !res & v1 != v2);

otal verification time: 9.11 second(s)
	Time spent in main process: 5.25 second(s)
	Time spent in child processes: 3.86 second(s)

  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures res & v1 = v2 or !res & v1 != v2;

0 false contexts at: ()

otal verification time: 13.03 second(s)
	Time spent in main process: 7.85 second(s)
	Time spent in child processes: 5.18 second(s)

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
  v1!=v2 -> ensures x::bigint<b, v1>* y::bigint<b, v2> & !res;
 }


2 false contexts at: ( (136,8)  (136,15) )

Total verification time: 22.62 second(s)
	Time spent in main process: 16.17 second(s)
	Time spent in child processes: 6.45 second(s)


  requires x::bigint<b, v1> * y::bigint<b, v2>
  ensures x::bigint<b, v1>* y::bigint<b, v2> & res & v1 = v2 or 
        x::bigint<b, v1>* y::bigint<b, v2> & !res & v1 != v2;

Total verification time: 94.23 second(s)
	Time spent in main process: 69.51 second(s)
	Time spent in child processes: 24.72 second(s)


*/
{

  if (x == null || y == null) {
    //assert y'!=null; //'
    //assert y'!=null; //'
    //assume false;
    return is_zero(x) && is_zero(y);
  } else {
    bool bq = (x.val==y.val);
    //assume n<m or n=m or n>m;
    dprint;
    node xn=x.next; node yn=y.next;
    if (bq) {
        //assume false;
      return is_equal(xn, yn);
      }
    else 
      { //assert false;
        //assume false;
        //dprint;
        assert xn'::bigint<b, v1a> * yn'::bigint<b, v2a> & (v1a=v2a | v1a!=v2a) assume xn'::bigint<b, v1a> * yn'::bigint<b, v2a> ;
        return false;
      }
  }

}

 
