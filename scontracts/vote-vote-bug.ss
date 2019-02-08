hip_include 'scontracts/mapprimitives.ss'
//#include<stdio.h>  ->  sizeof
//This file should be named as Ballot.ss -> contract
data address {
     int id;
}

data message{
     //int data_;
     int gas;
     address sender;
     //int sig;
     //int vxalue;
     address receiver;
}

global message msg;
global bnode   userbal;
global int     bal;

// This declares a new complex type which will
// be used for variables later.
// It will represent a single voter.
data Voter {
     int weight;
     bool voted;
     address delegate;
     int vote;
}

data Proposal {
     int num;
     int voteCount;
}

global address chairperson;

// votes are mapping type but proposals are not
global mapping(address => Voter) voters;

// A dynamically-sized array of `Proposal` structures.
global mapping(int => int) pros;


// Give your vote (including votes delegated to you)
// to proposal `proposals[proposal].name`.  ,vt1:    & fv=prps1[voteFor]
// don't have a smart inference?
void vote(int voteFor)
     requires [prps0,vt0] pros::Map<prps0> * voters::Map<vt0>
              * msg::message<_,sender,_>@L * vtr::Voter<w0,false,_,_>
              & vtr=vt0[sender]
     ensures  (exists vt1,prps1: voters::Map<vt1> * props::Map<prps1>
              * vtr::Voter<w0,true,_,_> & vtr=vt1[sender] & prps1[voteFor]=prps0[voteFor]+w0);
{
     address tmp_sender = msg.sender;
     Voter sender = voters[tmp_sender];
     sender.voted = true;
     sender.vote = voteFor;
     voters[tmp_sender] = sender;
     int tmpv = pros[voteFor];
     tmpv += sender.weight;
     pros[voteFor] = tmpv;
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
