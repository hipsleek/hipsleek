pragma solidity ^0.4.0;
import "remix_tests.sol"; // this import is automatically injected by Remix.
import "./ballot.sol";

// file name has to end with '_test.sol'
contract test_1 {

    A a;

    function beforeAll () {
      // here should instanciate tested contract
      a = new A();
    }

    function check1 () public {
      // this function is not constant, use 'Assert' to test the contract
      //Assert.equal(uint(2), uint(1), "error message");
      //Assert.equal(uint(a1), uint(a2)), "error message");
      //Assert.equal((a.select(uint(7))), uint(0), "initialized to 0");
      Assert.equal((a.select(uint(7))), uint(1), "initialized to 1");
      a.zeros(7);
      Assert.equal((a.select(uint(7))), uint(0), "initialized to 0");
    }

    function check2 () public constant returns (bool) {
      // this function is constant, use the return value (true or false) to test the contract
      return true;
    }
}

contract test_2 {

    function beforeAll () {
      // here should instanciate tested contract
    }

    function check1 () public {
      // this function is not constant, use 'Assert' to test the contract
      Assert.equal(uint(2), uint(1), "error message");
      Assert.equal(uint(2), uint(2), "error message");
    }

    function check2 () public constant returns (bool) {
      // this function is constant, use the return value (true or false) to test the contract
      return true;
    }
}