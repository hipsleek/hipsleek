/*
data mapping[t1,t2]{
 t1 key;
 t2 val;
 mapping next;
}

pred Map[t1,t2]<key0,val0> ==
   self=null or
   self::mapping[t1,t2]<key,val,t> * t::Map[t1,t2]<key0,val0> & key=key0 & val=val0 or
   self::mapping[t1,t2]<key,val,t> * t::Map[t1,t2]<key0,val0> & key!=key0.
*/

// mapping(address => uint) private userBalances;
// ====>
// mapping[address,uint] userBalances;

// access:
// userBalances[id]
// ====>
// getMap(userBalances,id)[t1,t2]

/*
  t2 getMap(mapping[t1,t2] map, t1 key)
     requires map::Map[t1,t2]<key,val>@L
     ensures  res = val;

  void setMap(mapping[t1,t2] ref map, t1 key, t2 val)
     requires map::Map[t1,t2]<key,_>
     ensures  map'::Map[t1,t2]<key,val>;
*/


// bind:
// userBalances[id]
// ====>
// setMap(userBalances,id,val)[t1,t2]

/*
 lemma self::Map<k1,v1> <-> self::Map<k2,v2>


 lemma x::Map<q> * q::mapping<k1,v1,t> * t::Map<w>

*/
 pred Map<w> = self=w or
               self::mapping<_,_,t> * t::Map<w> & self!=t.
/*
 pred MapE<r,k1,v1,w> = x::Map<q> * q::mapping<k1,v1,t> * t::Map<w>;

 lemma self::Map<q> & Entry(k,v,x) <-> exists t,w: self::Map<t> * t::mapping<k,v,w> * w::Map<q>.
*/
 prim_pred Entry<val,map>.



// fixed version
// should fail because of the recursive call
void withdrawBalance()
   //infer [@reentrancy]
   /*
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & n>=0 //& bal>=n
   ensures   userbal'::USERBALANCES<id,0>  & bal'=bal-n;
   */
   requires  msg::message<_,_,id,_,_>@L * userBalances::Map<q> * id::Entry<n,userBalances> & n>0 & bal>=n
   ensures   userBalances::Map<q> * id::Entry<0,userBalances>  & bal'=bal-n;
   requires  msg::message<_,_,id,_,_>@L * userBalances::Map<q>@L * id::Entry<n,userBalances>@L & n=0 & bal>=n
   ensures   bal'=bal & userbal'=userbal;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
     call(msg.sender,amountToWithdraw);                  // call(msg.sender,arg)             <- msg.sender.call(arg)
     withdrawBalance();
  }
}
