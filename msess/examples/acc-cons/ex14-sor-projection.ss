hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/*
G<A,B,C> == A->B: id;; ((B->C: id#id >10;; C->B:price#price>0) or (B->D: id#id <=10;; D->B:price#price>0)) ;; B->A: price#price>0


G@A(B) == !id ;; ?price#price>0
G@B(A) == ?id ;; !price#price>0
G@B(C) ==  !id#id >10 ;; ?price#price>0 or emp
G@C(B) == ?id#id >10 ;; !price#price>0 or emp
G@B(D) ==  emp or !id#id <=10 ;; ?price#price>0 
G@D(B) ==  emp or ?id#id <=10 ;; !price#price>0

*/


void B(Channel a, Channel c, Channel d)
 requires a::Chan{@S ?id ;; !price#price>0}<> * c::Chan{@S !id#id >10 ;; ?price#price>0 or emp}<> * d::Chan{@S emp or !id#id <=10 ;; ?price#price>0 }<>
 ensures  a::Chan{emp} *  c::Chan{emp} * d::Chan{emp}
{
  int price;
  int id = receive(a);
  if(id > 10) {
    /* id belongs to a category which can only be solved by process C */
    send(c,id);
    price = receive(c); 
  } else {
    /* id belongs to a category which can only be solved by process D */
    send(d,id);
    price = receive(d); 
  }
  send(c,price);  
}
