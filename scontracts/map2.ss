data bnode{ int userid; int val; bnode next;}.

data message{
       int data_;
       int gas;
       int sender;
       int sig;
       int value;
       }.

// mapping(address => uint) private userBalances;
 pred Map<w> == self=w or
               self::bnode<_,_,t> * t::Map<w> & self!=t.

 pred_prim Entry<val,map>.

 pred MapE<key,val,q> == self::Map<key> * key::Entry<val,p> * p::Map<q>.

checkentail x::MapE<k,v,q> |- x::MapE<k,v,q>.

checkentail x::MapE<k,v,q> |- x::Map<k> * k::Entry<v,q>.

checkentail x::Map<q> * k::Entry<v,x> |- x::MapE<kk,vv,qq>.
