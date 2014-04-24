data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;



void insert(node2 x, int a)
  requires H(x)
  ensures G(x,x'); //'
{
  bool l = x.next == null;
  if (l)
	x.next = new node2(a, x, null);
  else 
        insert(x.next, a);
}

//for x.next
 infer [H,G] H(x) |- x::node<a,p,n>@L
  --> [H,G,H1] x::node<a,p,n>*H1(p,n)
   with H(x) -> x::node<a,p,n>*H1(p,n)

//function call on l!=null
 [H,G,H1] x::node<a,p,n>*H1(p,n) |- true --* l & n=null \/ !(l) & n!=null
  -->  x::node<a,p,n>*H1(p,n) &  l & n=null
       or x::node<a,p,n>*H1(p,n) &  !(l) & n!=null

//state after then branch
[H,G,H1] x::node<a,p,n>*H1(p,n) & n=null

//x.next = new node2(a, x, null);
[H,G,H1] x'::node<a,p,n'> * H1(p,n') * n'::node<a,x,null> &x = x'

//post cond then branch
[H,G,H1] x'::node<a,p,n'> * H1(p,n') * n'::node<a,x,null> & x = x' |- G(x,x')
with H1(p,n') * x'::node<a,p,n'> * n'::node<a,x',null>  & x' = x-> G(x,x')

//state after else branch
[H,G,H1] x::node<a,p,n>*H1(p,n) & n!=null

//recursive call
[H,G,H1] x::node<a,p,n>*H1(p,n) & n!=null & n' = n |- H(n') --* G(n',n'')
[H,G,H1]  G(n0,n') * x::node<a,p,n>  * H1(p,n) & n!=null & n' = n
with x::node<a,p,n> * H1(p,n) & n!=null -> H(n)

//post cond after else branch

[H,G,H1]  G(n0,n') * x::node<a,p,n> * H1(p,n) & n!=null & n' = n |- G(x,x')
 	with x::node<a,p,n> * G(n0,n') * H1(p,n) & n!=null & x' = x & n' = n -> G(x,x')


Constrains

(1) H(x) -> x::node<a,p,n>*H1(p,n)
(2) x::node<a,p,n> * H1(p,n) * x'::node<a,p,n'> * n'::node<a,x,null> & n=null -> G(x,x')
(2') H1(p,n') * x'::node<a,p,n'> * n'::node<a,x',null> & n=null & x' =x-> G(x,x')

(3) x::node<a,p,n> * H1(p,n) & n!=null -> H(n)
(4) x::node<a,p,n> * G(n0,n') * H1(p,n) & n!=null & x' = x & n' = n -> G(x,x')

H(x) -> x::node<a,p,n>*H1(p,n) -> n!=null -> H(n)

H(x) -> x::node<a,p,n> * H1(p,n)

H1(p,n) ->  n= null v H(n) & n!=null 

=> H(x) -> x::node<a,p,n> & ( n= null v H(n) & n!=null)
 

 (2) x'::node<a,p,n'> * n'::node<a,x,null> -> G(x')
 (4) x'::node<a,p,n'> * G(n') * H1(p,n') & n'!=null  -> G(x')

H1(x',p,n') * G(n') -> G(x')





//x.next = new node2(a, x, null);
[H,G,H1] x::node<a,p,n'> * H1(p,n) * n'::node<a,x,null> & n=null

//x.next = new node2(a, x, null);
[H,G,H1] x::node<a,p,n> * x'::node<a,p,n'> * H1(x,p,n) * n'::node<a,x,null> & n=null


