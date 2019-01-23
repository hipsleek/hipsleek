
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
//global bnode   userbal;
//global int     bal;

/* Fill in the keyword. Hint: We want to protect our users balance from other contracts*/
// mapping (address => uint) private balances;
global mapping(address => int) balances;
global mapping(address => int) localBalances;

/* Let's make sure everyone knows who owns the bank. Use the appropriate keyword for this*/
global address owner;

// Events - publicize actions to external listeners
/* Add 2 arguments for this event, an accountAddress and an amount */
// event LogDepositMade(address accountAddress, uint amount);

// Constructor, can receive one or many variables here; only one allowed
void SimpleBank()
    requires msg::message<_,sender,_,_>@L
    ensures  owner' = sender;
{
/* Set the owner to the creator of this contract */
    owner = msg.sender;
}

// Enroll a customer with the bank, giving them 1000 tokens for free
// Return The balance of the user after enrolling
int enroll()
    requires [bb0] balances::Map<bb0> * msg::message<_,sender,_,_>@L
    ensures  (exists bb1: balances'::Map<bb1> & bb1[sender] = 0);
{
    address user = msg.sender;

    balances[user] = 0;
    return balances[user];
}

// Deposit ether into bank
// Return The balance of the user after the deposit is made
int deposit()
    requires [bb0] balances::Map<bb0> * msg::message<_,sender,value,_>@L
    ensures  (exists bb1: balances'::Map<bb1> & bb1[sender] = bb0[sender] + value);
{
/* Add the amount to the user's balance, call the event associated with a deposit,
          then return the balance of the user */
    address user = msg.sender;

    balances[user] += msg.value;

    //emit LogDepositMade(user, msg.value);

    return balances[user];
}

// Withdraw ether from bank
// Return The balance remaining for the user
int withdraw(int withdrawAmount)
    requires [bb0,lb0] balances::Map<bb0> * localBalances::Map<lb0> * msg::message<_,sender,value,_>@L & balances[user] >= withdrawAmount
    ensures  (exists bb1,lb1: balances'::Map<bb1> * localBalances'::Map<lb1> & bb1[sender] = bb0[sender] - withdrawAmount & lb1[sender] = lb0[sender] + withdrawAmount);
{
    address user = msg.sender;
    balances[user] -= withdrawAmount;

    //user.transfer(withdrawAmount);
    localBalances[user] += withdrawAmount;

    return balances[user];
}


// Return The balance of the user
// allows function to run locally/off blockchain
int balance()
{
    address user = msg.sender;

    return balances[user];
}



/*pragma solidity ^0.4.13;
contract SimpleBank
{

    /* Fill in the keyword. Hint: We want to protect our users balance from other contracts*/
    mapping (address => uint) private balances;

    /* Let's make sure everyone knows who owns the bank. Use the appropriate keyword for this*/
    address public owner;

    // Events - publicize actions to external listeners
    /* Add 2 arguments for this event, an accountAddress and an amount */
    event LogDepositMade(address accountAddress, uint amount);

    // Constructor, can receive one or many variables here; only one allowed
    function SimpleBank() public {
        /* Set the owner to the creator of this contract
         */
        owner = msg.sender;
    }

    /// @notice Enroll a customer with the bank, giving them 1000 tokens for free
    /// @return The balance of the user after enrolling
    function enroll() public returns (uint){
      /* Set the sender's balance to 1000, return the sender's balance */
        address user = msg.sender;

        balances[user] = 1000;
        return user.balance;
    }

    /// @notice Deposit ether into bank
    /// @return The balance of the user after the deposit is made
    // Add the appropriate keyword so that this function can receive ether
    function deposit() public payable returns (uint) {
        /* Add the amount to the user's balance, call the event associated with a deposit,
          then return the balance of the user */
        address user = msg.sender;

        balances[user] += msg.value;

        emit LogDepositMade(user, msg.value);

        return balances[user];
    }

    /// @notice Withdraw ether from bank
    /// @dev This does not return any excess ether sent to it
    /// @param withdrawAmount amount you want to withdraw
    /// @return The balance remaining for the user
    function withdraw(uint withdrawAmount) public returns (uint remainingBal) {
        /* If the sender's balance is at least the amount they want to withdraw,
           Subtract the amount from the sender's balance, and try to send that amount of ether
           to the user attempting to withdraw. IF the send fails, add the amount back to the user's balance
           return the user's balance.*/
        address user = msg.sender;

        // require(withdrawAmount >= owner.balance);
        require(balances[user] >= withdrawAmount);

        balances[user] -= withdrawAmount;

        user.transfer(withdrawAmount);

        return balances[user];
    }

    /// @notice Get balance
    /// @return The balance of the user
    // A SPECIAL KEYWORD prevents function from editing state variables;
    // allows function to run locally/off blockchain
    function balance() public view returns (uint) {
        /* Get the balance of the sender of this transaction */
        address user = msg.sender;

        return balances[user];
    }

    // Fallback function - Called if other functions don't match call or
    // sent ether without data
    // Typically, called when invalid data is sent
    // Added so ether sent to this contract is reverted if the contract fails
    // otherwise, the sender's money is transferred to contract
    function () public {
        revert();
    }
}
*/
