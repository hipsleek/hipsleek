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

int getUserBalance(int userid)
   requires  true
   ensures   true;

int setUserBalance(int userid, int amount)
   requires  true
   ensures   true;

/*******************************/
/**      generic fallback     **/
/*******************************/
int fallback(int userid, int arg)
   requires  true
   ensures   true;

/*********************/
/** contract Wallet **/
/*********************/
data bnode{ int userid; int val; bnode next;}

global message msg;
global bnode   userbal;

// mapping(address => uint) private userBalances;
pred USERBALANCES<userid,b1,b2> == self=null or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,b1,b2> & id=userid & b1<=val & (val<=b2 & 0<=b2 | b2<0) or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,b1,b2> & id!=userid;

void withdrawBalance(// message msg
)
   requires  msg::message<_,_,id,_,_>@L //* userbal::USERBALANCES<id,0,0>
   ensures   true;
{
  dprint;
  int amountToWithdraw = getUserBalance(msg.sender);   // getUserBalance(msg.sender)   <- userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     fallback(msg.sender,getUserBalance(msg.sender));  // fallbackAttacker(msg.sender,arg) <- msg.sender.call(arg)
     setUserBalance(msg.sender,0);                     // setUserBalance(msg.sender,0)     <- userBalances[msg.sender] = 0;
  }
}
