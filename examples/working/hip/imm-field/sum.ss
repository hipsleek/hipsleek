data node{
 int val;
 node next;
}

ll<n,a1,a2> == self=null & n=0 or
  self::node<_@a1,q@a2>*q::ll<n-1,a1,a2>
  inv n>=0;

node sum_insert(node p, node x, node y)
  requires p::ll<n,@A,@L> * (y::node<b@L,_@A> & x::node<a@L,_@M>)
  ensures  res::node<_@A,p@A> * p::ll<n,@A,@A>;  //* x::node<a@A,_@M>; 

{
  int sum;
  dprint;
  sum = x.val + y.val;
  dprint;
  if (sum < 10) {
    x.next = p;
    return x;
    }else{
    node tmp = new node(sum,p);
  dprint;
    return tmp;
  dprint;
      }
}

void call_insert(node p)
  requires p::ll<n,@A,@M> 
  ensures  p::ll<n,@A,@A> ; 
{
  node tmp;
  node x = new node(0,null);
  node y = new node(10,null);
  tmp = sum_insert(p,x,y);
  //  tmp = sum_insert(p,x,x);
}


int sum(node x, node y)
  requires (y::node<b@L,_@A> & x::node<a@L,_@M>)
  ensures  (y::node<b@A,_@A> & x::node<a@A,_@M>) & res=a+b;
{
  dprint;
  int s;
  s = x.val + y.val;
  x.next = null;
  return s;
  dprint;
}



int sum_check(node x, node y, node z, node w)
  requires  w::ll<m,@A,@A> * z::ll<n,@A,@A> * (y::node<b@L,_@A> & x::node<a@L,_@M>)
  ensures   x::node<a@A,_@M> & res=a+b;
{
  int s;
  s = x.val + y.val;
  if (s < 0)  x.next = q;
  else x.next = null;
  return s;
}



void call_sum()
  requires true
  ensures true;
{
  node x = new node(10,null);
  node y = new node(0,null);
  int s;// = sum (x,y);
  s = sum (x,x);
}





