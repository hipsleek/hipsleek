data node {
	int val;
	node next;
}

/*
ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;
*/


node tail2(node x)
  requires x::node<a,b> 
  ensures x::node<a,b> & res=b;
{
  dprint;
  int v1; node n2;
  //x.val = x.val+1;
  tail_acc(x,v1,n2);
  //assert x'::node<aa,bb> assume v1'=aa & n2'=bb; //'
    dprint;
    node tmp = n2;
    dprint;
  assume x'::node<v1',n2'>; //'
  dprint;
  return tmp;
}


/*
  assert-spec 
    case {
    x'=null  -> ensures flow __NullPtrExc;
    x'!=null -> requires x'::node<aa,bb> 
                ensures v1'=aa & n2'=bb;
   } ;
*/


void tail_acc(node x, ref int v, ref node n)
  case {
    x=null  -> ensures true & flow __Exc; 
    x!=null ->  requires x::node<aa,bb> 
                ensures v'=aa & n'=bb;
    //requires true
    //ensures true;
   } 
/*
  requires x::node<a,b> 
  ensures v'=a & n'=b;
*/
{
  v=x.val;
  n=x.next;
}
