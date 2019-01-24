
/********************/
/*Translated Version*/
/********************/

//#include<stdio.h>  ->  sizeof
//This file should be named as Ballot.ss -> contract
/*
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
global mapping(int => Proposal) proposals;

Proposal new_proposal()
   requires true
   ensures  res::Proposal<_,_>;


void for_loop_ballot(int i, int n, int[] proNums)
   // case
   // { i<n ->
       requires [prps0] proposals::Map<prps0> //& i < n //& proposals[0]=tmp
       ensures  (exists prps1: proposals'::Map<prps1> * tmp1::Proposal<proNums[i],0>
               & Store(prps0,prps1,i,tmp1) // prps1[i] = tmp1
               );
   //   i>=n -> ensures true;
   // }
{
//     if(i < n){
         Proposal tmp = new_proposal();
         tmp.num = proNums[i];
         tmp.voteCount = 0;
         proposals[i] = tmp;
         dprint;
         for_loop_ballot(i+1, n, proNums);
         dprint;
//     }
}




void goo(int i)
       requires [prps0] proposals::Map<prps0>
       ensures  (exists prps1: proposals'::Map<prps1> * tmp1::Proposal<7,0>
               & Store(prps0,prps1,i,tmp1) );
{
         Proposal tmp = new_proposal();
         tmp.num = 7;
         tmp.voteCount = 0;
         proposals[i] = tmp;
         dprint;
         goo(i+1);
         dprint;
}

*/

data node{
   int val;
   node next;
}

pred ll<n> == self = null & n = 0 or
             self::node<_,zz> * zz::ll<n-1>.

global node lns;

void update(ref node x)
     case {
      x!=null ->
        requires x::ll<m> //& x!=null
        ensures  x'::node<0,tt> * tt::ll<m-1>;
      x=null ->
        requires true
        ensures  true;
     }
{
 if(x == null) return;
 else {
    x.val = 0;
    dprint;
    update(x.next);
 }
 dprint;
}

/*
void update(ref node x)
     case {
      x!=null ->
        requires x::ll<>
        ensures  x'::node<0,t> * t::ll<>;
      x=null ->
        requires true
        ensures  true;
     }
{// x::ll<> & x!= null
 if(x == null) return;  // x::ll<> & x != null & x = null  ===>  false
// (1)  x::ll<> & x != null |- x::node<_,_>  DEREFERENCE
 else {
    x.val = 0;  // x::node<p,q> * q::ll<> & x != null & p = a = 0 & q = b
    update(x.next);  // x::node<p,q> * q::ll<> & x != null & p = 0 |- x != null & x::ll<>      pre-con
                     // x::node<p,q> * q::node<0,z> * z::ll<> & p = 0                          fr-call
                     // x::node<0,q> * q::node<0,z> * z::ll<> & p = 0 |- x::node<0,t> * t::ll<>
 }
}
*/

/*
Prove Tree(1)
        q::ll<> & x != null & p = a & q = b |- true
----------------------------------------------------------------
       x::<p,q> * q::ll<> & x != null |- x::node<a,b>
--------------------------------------------------------------- MATCH
      x::node<_,q> * q::ll<> & x != null |- x::node<_,_>
-------------------------------------------------------------   UNFOLD
          x::ll<> & x != null |- x::node<_,_>


Prove Tree(2) The first case
first it is also a dereference and then there is a method call

                       q::ll<> & j = p = 0 & q = b |- true
--------------------------------------------------------------------------------
            x::node<p,q> * q::ll<> & p = 0 & q = b |- x::node<j,k>
--------------------------------------------------------------------------------MATCH
              x::node<p,q> * q::ll<> & p = 0 & q = b |- x::node<_,_>
------------------------------------------------------------------------------
              x::node<p,q> * q::ll<> & x != null & p = 0 & q = b |- x::node<_,_> & x != null
---------------------------------------------------------------------------------------------UNFOLD
      x::node<p,q> * q::ll<> & x != null & p = 0 & q = b |- x::ll<> & x != null



Prove Tree(3)

                       x::node<p,q> & p = 0  |- true
----------------------------------------------------------------------------------
       x::node<p,q> * q::ll<> & x != null & p = 0 |- x != null & (x->next)::ll<>
*/
