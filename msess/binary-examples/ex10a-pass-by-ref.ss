hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/*

Below is from Actris's benchmarks:

P == ! l x ⟨l⟩ { l |-> x } . ? ⟨l⟩ { l |-> x + 2 } . end

let (c,c') := new_chan () in
fork { let l := recv(c') in l <- (!l + 2) ; send (c', l) }
send(c,ref 40); !(recv(c))

*/

data cell{
  int val;
}

int clientservice(Channel c1, Channel c2)
  /***** SPEC *****/
  requires c1::Chan{@S ?v#v::cell<x>;;!v#v::cell<x+2>}<> *
           c2::Chan{@S !v#v::cell<x>;;?v#v::cell<x+2>}<> * @full[c1,c2]
  ensures  c1::Chan{emp}<> * c2::Chan{emp}<> & res=42;
  /***** end of SPEC *****/
{
 cell l;
 par{c1,c2,l}
 {
  /* spec of service */
  case {c1} c1::Chan{@S ?v#v::cell<x>;;!v#v::cell<x+2>}<> ->
       /* code of thread service*/
       cell i =  receive(c1)[cell];
       i.val = i.val + 2;
       send(c1,i)[cell];
  ||
  /* spec of client */
  case {c2,l} c2::Chan{@S !v#v::cell<x>;;?v#v::cell<x+2>}<> ->
       /* code of thread client */
       l = new cell(40); // create l
       send(c2,l)[cell];
       l = receive(c2)[cell];
 }
 return l.val; //dereference l
}
