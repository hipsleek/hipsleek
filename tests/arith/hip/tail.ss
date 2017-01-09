data node {
	int val;
	node next;
}

data node2 {
  int val;
  int h;
  node2 left;
 node2 right;
}

avl<h> == self=null & h=0
  or self::node2<_,h,lt,rt> * lt::avl<h1> * rt::avl<h2> & h=1+max(h1,h2)
     & -1<=h1-h2<=1
	inv h>=0;

tree<h> == self=null & h=0
  or self::node2<_,h,lt,rt> * lt::tree<h1> * rt::tree<h2> & h=1+max(h1,h2)
	inv h>=0;

/*
ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;
*/

int hei(node2 x)
  requires x::tree<h>
  ensures x::tree<h>;
    /*
  requires x::avl<h>
  ensures x::avl<h>; */
{ 
  //assume x'=null or x'!=null;
   return height(x);
}

// x::avl<h> |- x=null or x::node2<v,h,lt,rt>

int height(node2 x) 
/*
 requires x=null
 ensures res=0;
 requires x::node2<v,h,lt,rt>
 ensures x::node2<v,h,lt,rt> & res=h;

 requires x=null or x::node2<v,h,lt,rt>
 ensures x=null & res=0 or x::node2<v,h,lt,rt> & res=h;
*/

 case {
   x=null -> ensures res=0;
  x!=null -> requires x::node2<v,h,lt,rt>
             ensures x::node2<v,h,lt,rt> & res=h;
    }

{
  if (x==null) return 0;
  else return x.h;
}

node tail2(node x)
  requires x::node<a,b> 
  ensures x::node<a,b> & res=b;
{
  //dprint;
  int v1; node n2;
  bind_node_spec(x,v1,n2);
  //assert x'::node<aa,bb> assume v1'=aa & n2'=bb; //'
  //dprint;
    node tmp = n2;
    //dprint;
    form_node(x,v1,n2); // assume x'::node<v1',n2'>; //'
    //dprint;
  return tmp;
}
/*
 bind x to (v1,n2)
 in e
 ==> 
 int v1; node n2;
 bind_node(x,v1,n2);
 try {
   e;
 } catch (Exc e)
   form_node(x,v1,n2);
   raise e;
 }
 */

void bind_node(node x, ref int v1, ref node n2)
  requires x::node<a,b>
  ensures v1'=a & n2'=b;

void bind_node_spec(node x, ref int v1, ref node n2)
    case {
    x=null  -> ensures true & flow __Exc; //' should be Error
    x!=null -> requires x::node<aa,bb> //'
               ensures v1'=aa & n2'=bb & glob=0; //
               requires true
               ensures true & glob=1; //
   }

void form_node(node x, int v1, node n2)
  requires glob=0
  ensures  x::node<v1,n2>;
  requires glob=1
  ensures  true;
 
/*
  assert-spec 
    case {
    x'=null  -> ensures flow __NullPtrExc;
    x'!=null -> requires x'::node<aa,bb> 
                ensures v1'=aa & n2'=bb;
   } ;
*/

/*
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
*/
