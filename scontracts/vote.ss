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
     //char[] name;
     int voteCount;
}

data string {
     int length;
}

global address chairperson;

// votes are mapping type but proposals are not
global mapping(address => Voter) voters;

// A dynamically-sized array of `Proposal` structures.
global Proposal[] proposals;


void for_loop_ballot(ref int i, int n, int[] proNums)
     requires tmp::Proposal<_,_> & i <= n & proposals[0]=tmp
     ensures  i' = i+1;
{
     if(i < n){
         Proposal tmp_p;
         tmp_p = proposals[0];
         tmp_p.num = proNums[i];
         tmp_p.voteCount = 0;
         for_loop_ballot(i, n, proNums);
     }
}

// Create a new ballot to choose one of `proposalNames`.
// @L means unchanged
void Ballot(int[] proposalNums)
     requires [vt0] voters::Map<vt0>@L * vtr::Voter<w0,_,_,_> * msg::message<_,sender,_> //& vtr = vt0[sender]
     ensures  vtr::Voter<1,_,_,_> & vtr = vt0[sender] & sender = chairperson;
{
     chairperson = msg.sender;
     Voter v = voters[chairperson];
     v.weight = 1;

     //size_t n_ = sizeof(proposalNums)/sizeof(proposalNums[0]);
     int n_ = 10;

     int i_ = 0;
     for_loop_ballot(i_, n_, proposalNums);
}

// Give `voter` the right to vote on this ballot.
// Only be called by `chairperson`.
void giveRightToVote(address voter)
   requires  [vt0] voters::Map<vt0>@L * msg::message<_,sender,_>@L * vtr::Voter<w0,v0,_,_> & vtr=vt0[voter] & sender = chairperson & !v0 & w0 = 0
   ensures   vtr::Voter<1,_,_,_> & vtr = vt0[voter];
//(exists vt1: voters'::Map<vt1> * vtr::Voter<1,_,_,_> & vtr = vt1[voter]);
//(exists vt1: voters'::Map<vt1> * vtr'::Voter<1,_,_,_>) & vt1[voter] = vtr1);
{
     Voter v = voters[voter];
     v.weight = 1;
}

void for_loop_winning(ref int p, int n, ref int winningVoteCount, ref int winningProposal_)
     requires p<=n
     ensures  p' = p+1;
{
  if(p < n){
      Proposal tmp_p = proposals[p];
      if (tmp_p.voteCount > winningVoteCount){
           winningVoteCount = tmp_p.voteCount;
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
    int winner_proposal = proposals[num_of_win];
    winnerNum_ = winner_proposal.num;
    return winnerNum_;
}

void while_loop_delegate(ref address toWhom, address initAddress)
     requires msg::message<_,sender,_> & toWhom != msg.sender
     ensures true;
{
    Voter tmp_voter;
    tmp_voter = voters[toWhom];
    if(tmp_voter.delegate != initAddress)
    {
        toWhom = tmp_voter.delegate;
        while_loop_delegate(toWhom, initAddress);
    }
}

// Delegate your vote to the voter `to`.
void delegate(address toWhom)
     requires msg::message<_,sender,_> & toWhom != sender & !sender.voted
     ensures  true;
{
     Voter sender =  voters[msg.sender];
     address init_addr;
     init_addr.id = 0;

     while_loop_delegate(toWhom, init_addr);

     Voter tmp_voter_1 = voters[msg.sender];
     tmp_voter_1.voted = true;
     tmp_voter_1.delegate = toWhom;
     Voter delegate_ = voters[toWhom];

     Voter tmp_voter_2 = voters[toWhom];
     if(tmp_voter_2.voted){
         int voteNum = delegate_.vote;
         Proposal tmp_prp;
         tmp_prp = proposals[voteNum];
         tmp_prp.voteCount += sender.weight;
     } else {
         delegate_.weight += sender.weight;
     }
}

// Delegate your vote to the voter `to`.
/*void delegate(address toWhom)
     requires msg::message<_,sender,_> & toWhom != sender & !sender.voted
     ensures  true;
{
     Voter* sender =  voters[msg.sender];
     address init_addr;
     init_addr.id = 0;

     while_loop_delegate(toWhom, init_addr);

     Voter tmp_voter_1 = voters[msg.sender];
     tmp_voter.voted = true;
     tmp_voter.delegate = toWhom;
     Voter* delegate_ = voters[toWhom];

     Voter tmp_voter_2 = voters[toWhom];
     if(tmp_voter_2.voted){
         int voteNum = (*delegate_).vote;
         Proposal tmp_prp;
         tmp_prp = proposals[voteNum];
         tmp_prp.voteCount += (*sender).weight;
     } else {
         (*deleg  ate_).weight += (*sender).weight;
     }
}*/

// Give your vote (including votes delegated to you)
// to proposal `proposals[proposal].name`.
void vote(int proposal)
     requires [vt0,prp]
           voters::Map<vt0> * msg::message<_,sender,_>
           * vtr::Voter<w0,false,_,_> * prp::Proposal<_,vc>
           & vtr= vt0[sender] & proposals[proposal] = prp //& !vtr.voted
//*************************************\\
     ensures  vtr::Voter<w0,true,_,_> * prp::Proposal<_,vc+w0>;
//*************************************\\

//vtr'::Voter<w0,true,_,_> * prp'::Proposal<_,vc+w0> & prps[proposal] = prp & prp.vc;//prps::Proposal<>[]
{
     Voter sender = voters[msg.sender];
     sender.voted = true;
     sender.vote = proposal;
     Proposal tmp_p;
     tmp_p = proposals[proposal];
     tmp_p.voteCount += sender.weight;
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
     (*sender).voted = true;
     (*sender).vote = proposal;
     Proposal tmp_p;
     tmp_p = proposals[proposal]
     tmp_p.voteCount += sender.weight;
}
*/
