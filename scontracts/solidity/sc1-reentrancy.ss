hip_include 'scontracts/mapprimitives.ss'

/* data structures for the special variables */
data message{
       int data_;
       int gas;
       address sender;
       int sig;
       int value;
       }

data address {
     int id;
}

global message msg;
global int     bal;  //contract's balance
global mapping(address => int) userBalances;

data uint {
     int val;
}

void call(address userid, int arg)
   requires  arg>0
   ensures   bal'=bal-arg;

void call_(address userid, int arg)
   requires  arg>0
   ensures   true;


/*
contract Wallet {
  mapping(address => uint) private userBalances;
  function withdrawBalance() {
    uint amountToWithdraw = userBalances[msg.sender];
    if (amountToWithdraw > 0) {
        msg.sender.call(userBalances[msg.sender]);
        userBalances[msg.sender] = 0;
 }}}

contract AttackerContract {
   function () {
     Wallet wallet;
     wallet.withdrawBalance();
 }}
*/

/*********************/
/** contract Wallet **/
/*********************/


void transfer(address dest, int amount)
 requires  [n,m,id] msg::message<_,_,id,_,_>@L
           * userBalances::Map<ub>
           & ub[id] = n
           & ub[dest] = m
           & n >= amount
           & id!=dest
           & amount>0
 ensures   (exists ub0: userBalances'::Map<ub0>
           & ub0[id] = n - amount
           & ub0[dest] = m + amount);
{
 if (userBalances[msg.sender] >= amount) {
    int x = userBalances[dest];
    int y = userBalances[msg.sender];
    dprint;
    userBalances[dest]       = x + amount;
    userBalances[msg.sender] = y - amount;
    dprint;
  }
}

// buggy version - should fail because of the recursive call
void withdrawBalance_b()
     infer [@reentrancy]
     requires  msg::message<_,_,id,_,_>@L * userBalances::Map<ub>
               & ub[id]=n & n>=0 & bal>=n
     ensures   (exists ub0: userBalances::Map<ub0> & ub0[id]=0 & bal'=bal-n);
{
  int amountToWithdraw = userBalances[msg.sender];
  if (amountToWithdraw > 0) {
     call(msg.sender,amountToWithdraw);
     userBalances[msg.sender] = 0;
  }
}
// ========================================================
// fixed version - gets verified
void withdrawBalance()
     infer [@reentrancy]
     requires  msg::message<_,_,id,_,_>@L * userBalances::Map<ub>
               & ub[id]=n & n>=0 & bal>=n
     ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id]=0 & bal'=bal-n);
{
  int amountToWithdraw = userBalances[msg.sender];
  if (amountToWithdraw > 0) {
      userBalances[msg.sender] = 0;
      call(msg.sender,amountToWithdraw);  //   <- msg.sender.call(arg)
  }
}
