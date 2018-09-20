pragma solidity ^0.4.0;

contract A{

   mapping(uint => uint) public users;

   constructor() public {
        ones(7);
   }

   function ones(uint key) public {
       users[key]=1;
   }

   function zeros(uint key) public  {
       users[key]=0;
   }

   function update1(uint key, uint val) public {
       uint aa = users[key];
       aa = val;
   }

   function update2(uint key, uint val) public {
       users[key] = val;
   }

   function select(uint key) public returns(uint){
       return users[key];
   }

   function del(uint key) public{
       delete(users[key]);
   }
}
