/*

contract Wallet {
 mapping(address => uint) private userBalances;

 function withdrawBalance() {
  uint amountToWithdraw = userBalances[msg.sender];
  if (amountToWithdraw > 0) {
    msg.sender.call(userBalances[msg.sender]);
    userBalances[msg.sender] = 0;
   }
  }
...
}


contract AttackerContract {
 function () {
  Wallet wallet;
  wallet.withdrawBalance();
 }
}
*/

/*
msg.data (bytes): complete calldata
msg.gas (uint): remaining gas - deprecated in version 0.4.21 and to be replaced by gasleft()
msg.sender (address): sender of the message (current call)
msg.sig (bytes4): first four bytes of the calldata (i.e. function identifier)
msg.value (uint): number of wei sent with the message
*/

/* data structures for the special variables */
data message{
       int data_;
       int gas;
       int sender;
       int sig;
       int value;
       }

/*********************/
/** contract Wallet **/
/*********************/
data bnode{ int userid; int val; bnode next;}

global message msg;
global bnode   userbal;
global int     bal;  //contract's balance

// mapping(address => uint) private userBalances;
pred USERBALANCES<userid,n> == self=null or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,n> & id=userid & n=val or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,n> & id!=userid
                            inv n>=0.


int getUserBalance(int userid)
   requires  userbal::USERBALANCES<userid,n>@L
   ensures   userbal=userbal' & res=n;

void setUserBalance(int userid, int amount)
   requires  userbal::USERBALANCES<userid,_>
   ensures   userbal'::USERBALANCES<userid,amount>;

/*******************************/
/**      generic fallback     **/
/*******************************/
void fallback(int userid, int arg)
   requires  true //bal>=arg
   ensures   bal'=bal-arg;

void call(int userid, int arg)
   requires  arg>0
   ensures   bal'=bal-arg;


// susceptible to re-entrancy
// should fail because of postcondition
void withdrawBalance_buggy()
     requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & n>=0 //& bal>=n
     ensures   userbal'::USERBALANCES<id,0> & bal'=bal-n;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     call(msg.sender,getUserBalance(msg.sender));        // call(msg.sender,arg)             <- msg.sender.call(arg)
     withdrawBalance_buggy();
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
  }
}


/**
 for the reentrancy check we should
 1. replace every occurrence of call with a call to all of the existing methods which adjust the current global state
            a. what should the parameters be instantiated to?
            b. how to identify the block that changes the program state? / or the specs which assert the state change
 2. (i)  a method is SAFE from reentrancy if verification fails for all cases in 1.
    (ii) a method is UNSAFE, susceptible to reentrancy, if at least one of the calls in 1 verifies.
*/

// fixed version
// should fail because of the recursive call
void withdrawBalance()
   //infer [@reentrancy]
   /*
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & n>=0 //& bal>=n
   ensures   userbal'::USERBALANCES<id,0>  & bal'=bal-n;
   */
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & n>0 & bal>=n
   ensures   userbal'::USERBALANCES<id,0>  & bal'=bal-n;
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n>@L & n=0 & bal>=n
   ensures   bal'=bal & userbal'=userbal;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
     call(msg.sender,amountToWithdraw);                  // call(msg.sender,arg)             <- msg.sender.call(arg)
     withdrawBalance();

}
}



 pred Map<w> == self=w or
               self::bnode<_,_,t> * t::Map<w> & self!=t;

 pred_prim Entry<val,map>;

// fixed version
// should fail because of the recursive call
void withdrawBalance_a()
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
     withdrawBalance_a();
  }
}
