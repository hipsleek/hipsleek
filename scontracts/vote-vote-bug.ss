hip_include 'scontracts/mapprimitives.ss'
//#include<stdio.h>  ->  sizeof
//This file should be named as Ballot.ss -> contract

data dat{int x;}

// Give your vote (including votes delegated to you)
// to proposal `proposals[proposal].name`.  ,vt1:    & fv=prps1[voteFor]
// don't have a smart inference?
void vote(mapping(int => int) pros, mapping(dat => int) voters)
     requires [prps0]
            pros::Map<prps0>
        * voters::Map<_>
     ensures  (exists prps1: pros::Map<prps1>);
{
  int x = 0 ;
}


// Withdraw a bid that was overbid.
// bool withdraw()
//      requires [ub0,pd0] balances::Map<ub0> * pendingReturns::Map<pd0> * msg::message<_,sender,value,_>@L & pd0[sender] != 0
//      ensures  (exists ub1,pd1: balances'::Map<ub1> * pendingReturns'::Map<pd1> & pd1[sender] = 0 & ub1[sender] = ub0[sender] + pd0[sender]);
// {
//   address sender;
//   sender = msg.sender;
//   int amount = pendingReturns[sender];
//   // It is important to set this to zero because the recipient
//   // can call this function again as part of the receiving call
//   // before `send` returns.

//     pendingReturns[sender] = 0;
//     //msg.sender.send(amount)
//     // 'send' process
//     //***************//
//     int old_balance;
//     old_balance = balances[sender];
//     balances[sender] += amount;
//     //***************//
//     if(balances[sender] != (old_balance + amount)) // sending process fails
//     {
//       pendingReturns[sender] = amount;
//       return false;
//     }
//   return true;
// }
