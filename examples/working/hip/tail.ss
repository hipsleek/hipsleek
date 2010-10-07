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
  bind_node_spec(x,v1,n2);
  //assert x'::node<aa,bb> assume v1'=aa & n2'=bb; //'
    dprint;
    node tmp = n2;
    dprint;
    form_node(x,v1,n2); // assume x'::node<v1',n2'>; //'
  dprint;
  return tmp;
}
/*
 bind x to (v1,n2)
 in e
 ==> 
 int v1; node n2;
 bind_node(x,v1,n2);
 e;
 form_node(x,v1,n2);
 */

void bind_node(node x, ref int v1, ref node n2)
  requires x::node<a,b>
  ensures v1'=a & n2'=b;

void bind_node_spec(node x, ref int v1, ref node n2)
    case {
    x'=null  -> ensures true & flow __Exc; //'
    x'!=null -> requires x::node<aa,bb> //'
                ensures v1'=aa & n2'=bb; //
   }

void form_node(node x, int v1, node n2)
  requires true
  ensures  x::node<v1,n2>;

 
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
