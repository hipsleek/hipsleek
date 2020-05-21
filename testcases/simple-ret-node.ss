data node{
  int val;
}

node main1() {
  return new node(1);
  dprint;
}

/*
pip:
node main1()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{(98, ):return new node(1)
dprint}
}
void free(node p)[]
static EBase: [][](emp ; (emp ; (p::node{}<Anon_11>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)


pcp:
node main1$()
static (stk) EBase
   emp&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{((node v_node_6_1857;
(v_node_6_1857 = {((int v_int_6_1856;
v_int_6_1856 = 1);
new node(v_int_6_1856))};
ret# v_node_6_1857));
dprint)}

{(5,0),(0,-1)}

void free$node(  node p)
static (stk) EBase
   exists (Impl)[Anon_11]p::node<Anon_11>@M&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,22)}


dprint(simpl): testcases/simple-ret-node.ss:7: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
 Escaped States:
 [

  Try-Block:0::
  [
   Path: []
   State:  (exists v_int_6_1856': v_node_6_1857'::node<v_int_6_1856'>@M&
MayLoop[] & v_int_6_1856'=1 & res=v_node_6_1857'&{FLOW,(20,21)=__Return#E}[])
          es_gen_impl_vars(E): []
          es_heap(consumed): emp
   ]
  ]
*/