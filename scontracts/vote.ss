/*pragma solidity ^0.4.16;

/// @title Voting with delegation.
contract Ballot {
    // This declares a new complex type which will
    // be used for variables later.
    // It will represent a single voter.
    struct Voter {
        uint weight; // weight is accumulated by delegation
        bool voted;  // if true, that person already voted
        address delegate; // person delegated to
        uint vote;   // index of the voted proposal
    }

    // This is a type for a single proposal.
    struct Proposal {
        bytes32 name;   // short name (up to 32 bytes)
        uint voteCount; // number of accumulated votes
    }

    address public chairperson;

    // This declares a state variable that
    // stores a `Voter` struct for each possible address.
    mapping(address => Voter) public voters;

    // A dynamically-sized array of `Proposal` structs.
    Proposal[] public proposals;

    /// Create a new ballot to choose one of `proposalNames`.
    function Ballot(bytes32[] proposalNames) public {
        chairperson = msg.sender;
        voters[chairperson].weight = 1;

        // For each of the provided proposal names,
        // create a new proposal object and add it
        // to the end of the array.
        for (uint i = 0; i < proposalNames.length; i++) {
            // `Proposal({...})` creates a temporary
            // Proposal object and `proposals.push(...)`
            // appends it to the end of `proposals`.
            proposals.push(Proposal({
                name: proposalNames[i],
                voteCount: 0
            }));
        }
    }

    // Give `voter` the right to vote on this ballot.
    // May only be called by `chairperson`.
    function giveRightToVote(address voter) public {
        // If the argument of `require` evaluates to `false`,
        // it terminates and reverts all changes to
        // the state and to Ether balances. It is often
        // a good idea to use this if functions are
        // called incorrectly. But watch out, this
        // will currently also consume all provided gas
        // (this is planned to change in the future).
        require(
            (msg.sender == chairperson) &&
            !voters[voter].voted &&
            (voters[voter].weight == 0)
        );
        voters[voter].weight = 1;
    }

    // Delegate your vote to the voter `to`.
    function delegate(address to) public {
        // assigns reference
        Voter storage sender = voters[msg.sender];
        require(!sender.voted);

        // Self-delegation is not allowed.
        require(to != msg.sender);

        // Forward the delegation as long as
        // `to` also delegated.
        // In general, such loops are very dangerous,
        // because if they run too long, they might
        // need more gas than is available in a block.
        // In this case, the delegation will not be executed,
        // but in other situations, such loops might
        // cause a contract to get "stuck" completely.
        while (voters[to].delegate != address(0)) {
            to = voters[to].delegate;

            // We found a loop in the delegation, not allowed.
            require(to != msg.sender);
        }

        // Since `sender` is a reference, this
        // modifies `voters[msg.sender].voted`
        sender.voted = true;
        sender.delegate = to;
        Voter storage delegate_ = voters[to];
        if (delegate_.voted) {
            // If the delegate already voted,
            // directly add to the number of votes
            proposals[delegate_.vote].voteCount += sender.weight;
        } else {
            // If the delegate did not vote yet,
            // add to her weight.
            delegate_.weight += sender.weight;
        }
    }

    /// Give your vote (including votes delegated to you)
    /// to proposal `proposals[proposal].name`.
    function vote(uint proposal) public {
        Voter storage sender = voters[msg.sender];
        require(!sender.voted);
        sender.voted = true;
        sender.vote = proposal;

        // If `proposal` is out of the range of the array,
        // this will throw automatically and revert all
        // changes.
        proposals[proposal].voteCount += sender.weight;
    }

    /// @dev Computes the winning proposal taking all
    /// previous votes into account.
    function winningProposal() public view
            returns (uint winningProposal_)
    {
        uint winningVoteCount = 0;
        for (uint p = 0; p < proposals.length; p++) {
            if (proposals[p].voteCount > winningVoteCount) {
                winningVoteCount = proposals[p].voteCount;
                winningProposal_ = p;
            }
        }
    }

    // Calls winningProposal() function to get the index
    // of the winner contained in the proposals array and then
    // returns the name of the winner
    function winnerName() public view
            returns (bytes32 winnerName_)
    {
        winnerName_ = proposals[winningProposal()].name;
    }
}

*/

/********************/
/*Translated Version*/
/********************/
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

data string {
     int length;
}

global address chairperson;

// votes are mapping type but proposals are not
global mapping(address => Voter) voters;

// A dynamically-sized array of `Proposal` structures.
global mapping(int => int) proposals;
// global mapping(int => int) proposals_int;


Proposal new_proposal()
   requires true
   ensures  res::Proposal<_,_>;

data node{
   int val;
   node next;
}

// i - iterator
// m - length of proposals
// ll - length of proposalNames
void for_loop_ballot(mapping(int => int) propos, int i, int ll, int m)
     case {
       i<0         ->
          requires true
          ensures  true;
       i>=ll & i>=0 ->
          requires [prps0] propos::Map<prps0>
                     & forall(j: !(m<=j & j<m+ll) | prps0[j]=0)
          ensures  (exists prps1: propos::Map<prps1>
                     & forall(j: !(m<=j & j<m+ll) | prps1[j]=0));
       i<ll & i>=0  ->
          requires [prps0] propos::Map<prps0>
                     & forall(j: !(m<=j & j<m+i) | prps0[j]=0)
          ensures  (exists prps1: propos::Map<prps1>
                     & forall(j: !(m<=j & j<=m+i) | prps1[j]=0));
     //(exists prps1: proposals'::Map<prps1> * tmp1::Proposal<proNums[i],0> & prps1[i] = tmp1 & i' = i+1);
     }
{
     if(0<=i && i<ll){
         // dprint;
         // Proposal tmp = new_proposal();
         //int pronum = proNums[i];
         //tmp.num = pronum;
         // int nnnn = i + m;
         // tmp.num = i+m;//proNums[i];
         // tmp.voteCount = 0;
         propos[i+m] = 0;
         // dprint;
         for_loop_ballot(propos, i+1, ll, m);
     }
}

global   int n_ = 10;
global   int i_ = 0;
global   int m_ = 5;

// Create a new ballot to choose one of `proposalNames`.
// In the pre, vtr=vt0[sender] tells us that this voter should exist (not null), otherwise in line 256, the dereference will have an error
// @L means unchanged
void Ballot()
     requires [vt0] voters::Map<vt0> * msg::message<_,sender,_>@L * vtr::Voter<w0,_,_,_> & vtr=vt0[sender]
     ensures (exists vt1: voters'::Map<vt1> * vtr::Voter<1,_,_,_> & chairperson' = sender & vt1[sender] = vtr);
{
     chairperson = msg.sender;
     Voter v = voters[chairperson];
     v.weight = 1;
     voters[chairperson] = v;
     for_loop_ballot(proposals, i_, n_, m_);
}

// Give `voter` the right to vote on this ballot.
// Only be called by `chairperson`.
void giveRightToVote(address voter)
   requires  [vt0] voters::Map<vt0> * msg::message<_,sender,_>@L * vtr::Voter<w0,v0,_,_> & vtr=vt0[voter] & sender = chairperson & !v0 & w0 = 0
   ensures   (exists vt1: voters'::Map<vt1> * vtr::Voter<1,_,_,_> & vt1[voter] = vtr);
//(exists vt1: voters'::Map<vt1> * vtr::Voter<1,_,_,_> & vtr = vt1[voter]);
//(exists vt1: voters'::Map<vt1> * vtr'::Voter<1,_,_,_>) & vt1[voter] = vtr1);
{
     Voter v = voters[voter];
     v.weight = 1;
     voters[voter] = v;
}

void for_loop_winning(int p, int n, ref int winningVoteCount, ref int winningProposal_)
{
  if(p < n){
       int tmp_p = proposals[p];
      if (tmp_p > winningVoteCount){
           winningVoteCount = tmp_p;
           winningProposal_ = p;
      }
      for_loop_winning(p+1, n, winningVoteCount, winningProposal_);
  }
}

int winningProposal()
{
    int winningVoteCount = 0;
    int winningProposal_ = 0;

    //size_t n = sizeof(proposals)/sizeof(proposals[0]);
    int n = 10;
    int p = 0;
    for_loop_winning(p, n, winningVoteCount, winningProposal_);
    return winningProposal_;
}

// Calls winningProposal() function to get the index
// of the winner contained in the proposals array and then
// returns the name of the winner
int winnerNum()
{
    int winnerNum_;
    int num_of_win = winningProposal();
    // Proposal winner_proposal;
    // winner_proposal = proposals[num_of_win];
    // winnerNum_ = winner_proposal.num;
    return num_of_win;
}

void while_loop_delegate(ref address toWhom, address initAddress)
     requires [vt0] voters::Map<vt0>@L * msg::message<_,sender,_> * vtr::Voter<_,_,_,_> & toWhom != msg.sender & vt0[toWhom] = vtr
     ensures true;
{
    Voter tmp_voter;
    tmp_voter = voters[toWhom];
    if(tmp_voter.delegate != initAddress || tmp_voter.delegate != null)
    {
        toWhom = tmp_voter.delegate;
        while_loop_delegate(toWhom, initAddress);
    }
}

//Delegate your vote to the voter `to`.
// void delegate(address toWhom)
//      requires msg::message<_,sender,_> & toWhom != sender & !sender.voted
//      ensures  true;
// {
//      Voter tmp_voter_1 = voters[msg.sender];
//      tmp_voter_1.voted = true;
//      tmp_voter_1.delegate = toWhom;


//      Voter tmp_voter_2 = voters[toWhom];
//      if(tmp_voter_2.voted){
//          int voteNum = delegate_.vote;
//          int tmp_prp = proposals[voteNum];
//          tmp_prp += rmp_voter_1.weight;
//          proposals[voteNum] = tmp_prp;
//      } else {
//          tmp_voter_2.weight += sender.weight;
//      }
// }

 // function delegate(address to) public {
 //        // assigns reference
 //        Voter storage sender = voters[msg.sender];
 //        require(!sender.voted);

 //        // Self-delegation is not allowed.
 //        require(to != msg.sender);
 //        while (voters[to].delegate != address(0)) {
 //            to = voters[to].delegate;

 //            // We found a loop in the delegation, not allowed.
 //            require(to != msg.sender);
 //        }

 //        // Since `sender` is a reference, this
 //        // modifies `voters[msg.sender].voted`
 //        sender.voted = true;
 //        sender.delegate = to;
 //        Voter storage delegate_ = voters[to];
 //        if (delegate_.voted) {
 //            // If the delegate already voted,
 //            // directly add to the number of votes
 //            proposals[delegate_.vote].voteCount += sender.weight;
 //        } else {
 //            // If the delegate did not vote yet,
 //            // add to her weight.
 //            delegate_.weight += sender.weight;
 //        }



// Give your vote (including votes delegated to you)
// to proposal `proposals[proposal].name`.  ,vt1:    & fv=prps1[voteFor]
void vote(int voteFor)
     requires [prps,vt0] proposals::Map<prps> * voters::Map<vt0>
              * msg::message<_,sender,_> * vtr::Voter<w0,false,_,_>
              //& vtr=vt0[sender] & vc=prps[voteFor]
     ensures  (exists prps1,vt1: voters'::Map<vt1> * proposals'::Map<prps1>
              * vtr::Voter<w0,true,_,_> & vtr=vt1[sender] & fv=vc+w0);
{
     address tmp_sender = msg.sender;
     Voter sender = voters[tmp_sender];
     sender.voted = true;
     sender.vote = voteFor;
     int tmpv = proposals[voteFor];
     tmpv += sender.weight;
     proposals[voteFor] = tmpv;
}

// Give your vote (including votes delegated to you)
// to proposal `proposals[proposal].name`.
/*
void vote(int proposal)
     requires [vt0] voters::Map<vt0> * msg::message<_,sender,_> * vtr::Voter<w0,false,_,_> * prp::Proposal<_,vc> & vtr= vt0[sender] //& !vtr.voted
     ensures  vtr'::Voter<w0,true,_,_> * prps::proposals[] * prp'::Proposal<_,vc+w0> & prps[proposal] = prp & prp.vc;
{
     //The one written in Solidity has 'storage', so I don't know whether to use the pointer or not
     Voter* sender = voters[msg.sender];
     (*sender).voted = true; /*test*/
     (*sender).vote = proposal;
     Proposal tmp_p;
     tmp_p = proposals[proposal]
     tmp_p.voteCount += sender.weight;
}
*/
