hip_include 'scontracts/mapprimitives.ss'
/* data structures for the special variables */
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

/*********************/
/** contract Wallet **/
/*********************/
data bnode{ int userid; int val; bnode next;}

global message msg;
global bnode   userbal;
global int     bal;  //contract's balance

// mapping(address => uint) private userBalances;
pred USERBALANCES<userid,n> == self=null or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,n> & id=userid & n=val or
                            self::bnode<id,val,t> * t::USERBALANCES<userid,n> & id!=userid
                            inv n>=0.


int getUserBalance(int userid)
   requires  userbal::USERBALANCES<userid,n>@L
   ensures   userbal=userbal' & res=n;

void setUserBalance(int userid, int amount)
   requires  userbal::USERBALANCES<userid,_>
   ensures   userbal'::USERBALANCES<userid,amount>;

global mapping(address => int) balances;
global address minter;


      void coin()
             requires true
             ensures  true;

      {
             minter = msg.sender;
      }


      void mint(address receiver, int amount)
             requires [ub0] balances::Map<ub0> //& msg.sender != minter
             ensures (exists ub1: balances'::Map<ub1> & ub1[receiver] = ub0[receiver] + amount);
      {
            //if(msg.sender != minter) return;
            //int b = balances[receiver];
            balances[receiver] += amount;
      }

      //global address tmp = msg.sender;
      void send(address tmp, address receiver, int amount)
             requires [ub0] balances::Map<ub0>
             ensures (exists ub1: balances'::Map<ub1> & ub1[receiver] = ub0[receiver] + amount & ub1[tmp] = ub0[tmp] - amount);
      {
            //if(balances[tmp] < amount) return;
            balances[tmp] -= amount;
            //int b1 = balances[tmp];
            //balances[tmp] = b1 - amount;
            balances[receiver] += amount;
            //int b2 = balances[receiver];
            //balances[receiver] = b2 + amount;
      }
