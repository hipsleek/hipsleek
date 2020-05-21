data node{
  int val;
}

node main4() {
  while(true) {
    return new node(1);
    dprint;
  }
  return new node(2);
}

/*
pip:
node main4()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{ while (true)
EList
{
{(99, ):return new node(1)
dprint}
}
(100, ):return new node(2)}
}
void free(node p)[]
static EBase: [][](emp ; (emp ; (p::node{}<Anon_11>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)


pcp:
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

node main4$()
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
try
{({while_6_2$()};
(node v_node_10_1902;
(v_node_10_1902 = {((int v_int_10_1901;
v_int_10_1901 = 2);
new node(v_int_10_1901))};
ret# v_node_10_1902)))}
 catch (23,24)=ret_node#E ret_node:f_r_1891 )
        (node v_node_5_1893;
(v_node_5_1893 = bind f_r_1891 to (val_5_1892) [read] in
val_5_1892;
ret# v_node_5_1893))

{(5,0),(0,-1)}

void while_6_2$() rec
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
{(boolean v_bool_6_1900;
(v_bool_6_1900 = true;
if (v_bool_6_1900) [{({((ret_node v_ret_node_7_1899;
(v_ret_node_7_1899 = {((node v_node_7_1898;
v_node_7_1898 = {((int v_int_7_1897;
v_int_7_1897 = 1);
new node(v_int_7_1897))});
new ret_node(v_node_7_1898))};
throw v_ret_node_7_1899:{,(23,24)=ret_node#E}));
dprint)};
{while_6_2$() rec})}]
else []
))}

{(6,2),(9,3)}


before equality fix:
dprint(simpl): bugs/bug-while-return.ss:27: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
 Escaped States:
 [

  Try-Block:0::
  [
   Path: [(,1 )]
   State:  (exists v_int_26_2059',
v_node_26_2060': v_node_26_2060'::node<v_int_26_2059'>@M *
                 v_ret_node_26_2061'::ret_node<v_node_26_2060'>@M&
v_bool_25_2062' & MayLoop[] & v_int_26_2059'=1 & eres=v_ret_node_26_2061'&
{FLOW,(29,30)=ret_node#E}[])
          es_gen_impl_vars(E): []
          es_heap(consumed): emp
   ]
  ]

after equality fix:
dprint(simpl): loop-ret-node.ss:8: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
 Escaped States:
 [

  Try-Block:0::
  [
   Path: [(,1 )]
   State:  (exists v_int_7_1897',
v_node_7_1898': v_node_7_1898'::node<v_int_7_1897'>@M *
                v_ret_node_7_1899'::ret_node<v_node_7_1898'>@M&
v_bool_6_1900' & MayLoop[] & v_int_7_1897'=1 & v_node_7_1898'=res &
eres=v_ret_node_7_1899'&{FLOW,(23,24)=ret_node#E}[])
          es_gen_impl_vars(E): []
          es_heap(consumed): emp
   ]
  ]
*/