
data node {
  //int val;
  node next;
}

ll<> == self = null
	or self::node<q> * q::ll<> 
  inv true;

node append(node x, node y)
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;
{
  //___sl_plot("simple1");
  node curr;
  curr = x;
  while (curr.next != null) 
  requires curr::node<_>
  ensures curr::node<null>;
  {
    curr = curr.next;
  } 
  curr.next = y;
  return x;
}

node create_list()
requires true
ensures res::ll<> & res != null;
{
   node curr;
   node h = null;
   int i = 1;
   dprint;
   while(i<=10) 
   requires h::ll<> & i <=10
   ensures h::ll<> & i > 10;
   {
      curr = malloc();
      //curr->val = i;
      curr.next = h;
      h = curr;
dprint;
      i = i + 1;
   }
   dprint;
   node tmp = h.next;
   free(h);
   h = tmp;
   return h;
}

void main() 
   requires true
   ensures x::ll<>;
{
   node x, y;
   x = create_list();
   y = create_list();
   //___sl_plot("pre");
   //___sl_summary("infer/shape/demo/ll-app-0000");
   x = append(x, y);
   //___sl_plot("post");
   //___sl_summary("infer/shape/demo/ll-app-0000");
}

node malloc ()
 requires true
 ensures res::node<null>;

void free(node a)
  requires a::node<_>
  ensures a = null;

void form_node(node x, node n2)
  requires true
  ensures  x::node<n2>;


