hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


/*

Below is from Actris's benchmarks:

        prot := !x<x>. ?<x+2>. end
   prot_dual := ?x<x>. !<x+2>. end

*/

data cell{
  int val;
}

int service(Channel c)
   requires  c::Chan{@S ?v#v::cell<x>;;!v#v::cell<x+2>}<>
   ensures   c::Chan{emp}<> & res=x+2; // x is ghost variable!
{
  cell z = receive(c)[cell];
  z.val = z.val+2;
  int y = z.val;
  send(c,z)[cell];
  dprint;
  return y;
}

void client(Channel c, ref cell i, int id)
  requires  c::Chan{@S !v#v::cell<x>;;?v#v::cell<x+2>}<> * i::cell<id> * @full[i]
  ensures   c::Chan{emp}<> * i'::cell<id+2> ; // id is fixed!
{
  send(c,i)[cell];
  i = receive(c)[cell];
  dprint;
}
