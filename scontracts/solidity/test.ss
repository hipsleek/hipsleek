//pragma solidity ^0.4.0;
//contract A

global mapping(int => int) users;

void foo()
{
 int x = users[1];
 users[2] = 5;
}

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
