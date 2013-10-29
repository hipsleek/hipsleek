// star_fields
data node {
  int x;
  node next;
}

data node__star {
  node deref;
}

ll<n> == self=null & n=0
   or self::node<_,q>*q::ll<n-1>
   inv n>=0;

/*
   node* q  ==> node q_ptr
   q^       ==> q_ptr
   q        ==> q_ptr
   q->field ==> q_ptr.field
   q = ..   ==> q_ptr = ..
*/
int foo(node q_ptr)
  requires q_ptr::ll<n>
  ensures q_ptr::ll<n> & res=n;
{
  if (q_ptr==null) return 0;
  else return 1+foo(q_ptr.next);
}


void main() 
/*@
 requires true
 ensures true;
*/
{
  node q=new node(0,null);
  int t1 = foo(q);  //foo(*&q) ==> foo(q)
  node__star qq = new node__star(null);
  int t2 = foo(qq.deref);//foo(*qq) ==> foo(qq.deref)
}
/*
   mn(e) ==> mn(deref(e))

      deref(&p) ==> p
      deref(v)  ==> v.deref
      deref(v.field)  ==> v.(deref(field))

*/


