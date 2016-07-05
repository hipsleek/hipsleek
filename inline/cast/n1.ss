data node {
  int val; 
 node next;	
}


int count_rest(node rest, node h)

  requires rest::node<_,_> & h = rest
  ensures rest::node<_,_> & h = rest & res=0;

{
  if (rest == h){
    // dprint;
    return 0;
  }
  // dprint;
   return 1;
}
