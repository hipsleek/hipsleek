//pragma solidity ^0.4.0;
//contract A

// global mapping(uint => uint) public users;

void select [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key, `T2 val)
   requires true
   ensures  map'[key]=val;

`T2 select [T1,T2] (mapping(`T1 => `T2) map, `T1 key)
   requires map[key]=val
   ensures  res = val;

void delete [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key)
   requires true
   ensures  map'[key]=ZERO;


/*
void constructor(){
        ones(7);
}

void ones(int key){
       users[key]=1;
}

void zeros(int key){
       users[key]=0;
}

void update1(int key, int val){
     uint aa = users[key];
     aa = val;
}

void update2(int key, int val){
     users[key] = val;
}

int select(int key){
     return users[key];
}

void del(int key)
   requires true
   ensures  users'[key]=ZERO;
{
     delete(users[key]);
}
*/
