data node{
  int val;
}

class rexc extends __Exc{}
class rexc1 extends __Exc{ int z; }
class rexc2 extends __Exc{ int q; int w; int p; }

node main2() {
  raise new rexc1(1);
  dprint;
}

/*
pip:
node main2()[]
static EList
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)
{
{(101, ):raise EXPR:CF:new rexc1(1)

dprint}
}
void free(rexc2 p)[]
static EBase: [][](emp ; (emp ; (p::rexc2{}<Anon_11,Anon_12,Anon_13>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)

void free(rexc1 p)[]
static EBase: [][](emp ; (emp ; (p::rexc1{}<Anon_14>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)

void free(rexc p)[]
static EBase: [][](emp ; (emp ; (p::rexc{}<>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 3,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)

void free(node p)[]
static EBase: [][](emp ; (emp ; (p::node{}<Anon_15>[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 4,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false)


pcp:
void free$rexc1(  rexc1 p)
static (stk) EBase
   exists (Impl)[Anon_14]p::rexc1<Anon_14>@M&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,22)}

void free$node(  node p)
static (stk) EBase
   exists (Impl)[Anon_15]p::node<Anon_15>@M&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,22)}

void free$rexc(  rexc p)
static (stk) EBase
   p::rexc<>@M&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,22)}

void free$rexc2(  rexc2 p)
static (stk) EBase
   exists (Impl)[Anon_11; Anon_12;
   Anon_13]p::rexc2<Anon_11,Anon_12,Anon_13>@M&{FLOW,(4,5)=__norm#E}[]
   EBase
     emp&Term[]&{FLOW,(4,5)=__norm#E}[]
     EAssume
       emp&{FLOW,(4,5)=__norm#E}[]
       struct:EBase
                emp&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase
   hfalse&false&{FLOW,(4,5)=__norm#E}[]
{(1,0),(3,22)}

node main2$()
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
{((rexc1 v_rexc1_10_1963;
(v_rexc1_10_1963 = {((int v_int_10_1962;
v_int_10_1962 = 1);
new rexc1(v_int_10_1962))};
throw v_rexc1_10_1963:{,(25,26)=rexc1#E}));
dprint)}

{(9,0),(0,-1)}


dprint(simpl): testcases/excep-ret-node.ss:11: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]
 Escaped States:
 [

  Try-Block:0::
  [
   Path: []
   State:  (exists v_int_10_1962': v_rexc1_10_1963'::rexc1<v_int_10_1962'>@M&
MayLoop[] & v_int_10_1962'=1 & eres=v_rexc1_10_1963'&
{FLOW,(25,26)=rexc1#E}[])
          es_gen_impl_vars(E): []
          es_heap(consumed): emp
   ]
  ]
*/