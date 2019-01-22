/*pragma solidity ^0.4.22;

contract SimpleAuction {
    // Parameters of the auction. Times are either
    // absolute unix timestamps (seconds since 1970-01-01)
    // or time periods in seconds.
    address public beneficiary;
    uint public auctionEnd;

    // Current state of the auction.
    address public highestBidder;
    uint public highestBid;

    // Allowed withdrawals of previous bids
    mapping(address => uint) pendingReturns;

    // Set to true at the end, disallows any change
    bool ended;

    // Events that will be fired on changes.
    event HighestBidIncreased(address bidder, uint amount);
    event AuctionEnded(address winner, uint amount);

    // The following is a so-called natspec comment,
    // recognizable by the three slashes.
    // It will be shown when the user is asked to
    // confirm a transaction.

    /// Create a simple auction with `_biddingTime`
    /// seconds bidding time on behalf of the
    /// beneficiary address `_beneficiary`.
    constructor(
        uint _biddingTime,
        address _beneficiary
    ) public {
        beneficiary = _beneficiary;
        auctionEnd = now + _biddingTime;
    }

    /// Bid on the auction with the value sent
    /// together with this transaction.
    /// The value will only be refunded if the
    /// auction is not won.
    function bid() public payable {
        // No arguments are necessary, all
        // information is already part of
        // the transaction. The keyword payable
        // is required for the function to
        // be able to receive Ether.

        // Revert the call if the bidding
        // period is over.
        require(
            now <= auctionEnd,
            "Auction already ended."
        );

        // If the bid is not higher, send the
        // money back.
        require(
            msg.value > highestBid,
            "There already is a higher bid."
        );

        if (highestBid != 0) {
            // Sending back the money by simply using
            // highestBidder.send(highestBid) is a security risk
            // because it could execute an untrusted contract.
            // It is always safer to let the recipients
            // withdraw their money themselves.
            pendingReturns[highestBidder] += highestBid;
        }
        highestBidder = msg.sender;
        highestBid = msg.value;
        emit HighestBidIncreased(msg.sender, msg.value);
    }

    /// Withdraw a bid that was overbid.
    function withdraw() public returns (bool) {
        uint amount = pendingReturns[msg.sender];
        if (amount > 0) {
            // It is important to set this to zero because the recipient
            // can call this function again as part of the receiving call
            // before `send` returns.
            pendingReturns[msg.sender] = 0;

            if (!msg.sender.send(amount)) {
                // No need to call throw here, just reset the amount owing
                pendingReturns[msg.sender] = amount;
                return false;
            }
        }
        return true;
    }

    /// End the auction and send the highest bid
    /// to the beneficiary.
    function auctionEnd() public {
        // It is a good guideline to structure functions that interact
        // with other contracts (i.e. they call functions or send Ether)
        // into three phases:
        // 1. checking conditions
        // 2. performing actions (potentially changing conditions)
        // 3. interacting with other contracts
        // If these phases are mixed up, the other contract could call
        // back into the current contract and modify the state or cause
        // effects (ether payout) to be performed multiple times.
        // If functions called internally include interaction with external
        // contracts, they also have to be considered interaction with
        // external contracts.

        // 1. Conditions
        require(now >= auctionEnd, "Auction not yet ended.");
        require(!ended, "auctionEnd has already been called.");

        // 2. Effects
        ended = true;
        emit AuctionEnded(highestBidder, highestBid);

        // 3. Interaction
        beneficiary.transfer(highestBid);
    }
}
*/


/********************/
/*Translated Version*/
/********************/
hip_include 'scontracts/mapprimitives.ss'
//This file should be named as SimpleAuction.ss -> contract
data address {
     int id;
}

data message{
     //int data_;
     int     gas;
     address sender;
     //int sig;
     int     value;
     address receiver;
}

global message msg;
global bnode   userbal;
global int     bal;

// Parameters of the auction. Times are either
// absolute unix timestamps (seconds since 1970-01-01)
// or time periods in seconds.
// and time now.
global address beneficiary;
global int     auctionEnd;
global int     now;
// Current state of the auction.
global address highestBidder;
global int     highestBid;

// Allowed withdrawals of previous bids
global mapping(address => int) pendingReturns;

// Set to true at the end, disallows any change
global bool    ended;

global mapping(address => int) balances;

/*
    // Events that will be fired on changes.
    event HighestBidIncreased(address bidder, uint amount);
    event AuctionEnded(address winner, uint amount);
*/

void SimpleAuction(int _biddingTime, address _beneficiary)
     requires _biddingTime > 0
     ensures  auctionEnd' = now + _biddingTime & beneficiary' = _beneficiary;
{
  beneficiary = _beneficiary;
  auctionEnd = now + _biddingTime;
}

// No arguments are necessary, all
// information is already part of
// the transaction.
// Revert the call if the bidding
// period is over.
void bid()
     requires [pd0] pendingReturns::Map<pd0> * msg::message<_,sender,value,_>@L & now <= auctionEnd & value > highestBid
     ensures  (exists pd1: pendingReturns'::Map<pd1> & pd1[highestBidder] = pd0[highestBidder] + highestBid & highestBidder' = sender & highestBid' = value);
{
  if (highestBid != 0)
  {
    int tmp_pending;
    tmp_pending = pendingReturns[highestBidder];
    pendingReturns[highestBidder] = tmp_pending + highestBid;
  }
  highestBidder = msg.sender;
  highestBid = msg.value;
}

//Withdraw a bid that was overbid.
bool withdraw()
     requires [ub0,pd0] balances::Map<ub0> * pendingReturns::Map<pd0> * msg::message<_,sender,value,_>@L & pd0[sender] != 0
     ensures  (exists ub1,pd1: balances'::Map<ub1> * pendingReturns'::Map<pd1> & pd1[sender] = 0 & ub1[sender] = ub0[sender] + pd0[sender]);
{
  address sender;
  sender = msg.sender;
  int amount = pendingReturns[sender];
  // It is important to set this to zero because the recipient
  // can call this function again as part of the receiving call
  // before `send` returns.

    pendingReturns[sender] = 0;
    //msg.sender.send(amount)
    // 'send' process
    //***************//
    int old_balance;
    old_balance = balances[sender];
    balances[sender] += amount;
    //***************//
    if(balances[sender] != (old_balance + amount)) // sending process fails
    {
      pendingReturns[sender] = amount;
      return false;
    }
  return true;
}

// End the auction and send the highest bid
// to the beneficiary.
void auctionEnd()
requires [ub0] balances::Map<ub0> & now >= auctionEnd & !ended
ensures  (exists ub1: balances'::Map<ub1> & ub1[beneficiary] = ub0[beneficiary] + highestBid);
{
        // It is a good guideline to structure functions that interact
        // with other contracts (i.e. they call functions or send Ether)
        // into three phases:
        // 1. checking conditions
        // 2. performing actions (potentially changing conditions)
        // 3. interacting with other contracts
        // If these phases are mixed up, the other contract could call
        // back into the current contract and modify the state or cause
        // effects (ether payout) to be performed multiple times.
        // If functions called internally include interaction with external
        // contracts, they also have to be considered interaction with
        // external contracts.
/*
        // 1. Conditions
        require(now >= auctionEnd, "Auction not yet ended.");
        require(!ended, "auctionEnd has already been called.");
*/
        // 2. Effects
        ended = true;
//        emit AuctionEnded(highestBidder, highestBid);

        // 3. Interaction
//        beneficiary.transfer(highestBid);
        balances[beneficiary] += highestBid;
    }
