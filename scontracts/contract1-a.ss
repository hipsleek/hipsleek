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
   requires  userbal::USERBALANCES<userid,n>@L & Term
   ensures   userbal=userbal' & res=n;

void setUserBalance(int userid, int amount)
   requires  userbal::USERBALANCES<userid,_> & Term
   ensures   userbal'::USERBALANCES<userid,amount>;

/*******************************/
/**      generic fallback     **/
/*******************************/
void fallback(int userid, int arg)
   requires  true //bal>=arg
   ensures   bal'=bal-arg;

void call(int userid, int arg)
   requires  arg>0 & Term
   ensures   bal'=bal-arg;


//susceptible to re-entrancy
void withdrawBalance_buggy()
     requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & Term[n]
     ensures   userbal'::USERBALANCES<id,0>;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     call(msg.sender,getUserBalance(msg.sender));        // call(msg.sender,arg)             <- msg.sender.call(arg)
     withdrawBalance_buggy();
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
  }
}

data nnode{ int val;}

// prim_pred GLOB{%P}<>.

void ccall(int userid, int arg)
   requires  arg>0 & Term
   ensures   bal'=bal-arg;
// {
//    withdrawBalance();
// }


//fixed version
void withdrawBalance()
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & Term[n] & n>=0
   ensures   userbal'::USERBALANCES<id,0>;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
     ccall(msg.sender,amountToWithdraw);                  // call(msg.sender,arg)             <- msg.sender.call(arg)
  }
}

// ########################################################

void call0(int userid, int arg)
   requires  arg>0
   ensures   bal'=bal-arg;
{
   foo();
}

//fixed version
void foo()
   requires  msg::message<_,_,id,_,_>@L * userbal::USERBALANCES<id,n> & n>=0
   ensures   userbal'::USERBALANCES<id,0>;
{
  int amountToWithdraw = getUserBalance(msg.sender);     // getUserBalance(msg.sender)       <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     setUserBalance(msg.sender,0);                       // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
     call0(msg.sender,amountToWithdraw);                 // call(msg.sender,arg)             <- msg.sender.call(arg)
  }
}
