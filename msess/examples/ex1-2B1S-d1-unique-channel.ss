/* model the communication instrument as a unique channel between one pair of processes */
/*  B1<->B2
    B1<->S
    B2<->S  */

multi_buy(B1,S,B2) ==
   B1 -> S : string ;
   (S  -> B1 : int ; B1 -> B2 : int)
   * S  -> B2 : int ;
   (B2 -> S : 1 ; B2 -> S : Addr ; S -> B2 : Date 
    \/ B2 -> S : 0)

===============================================

pred_prim Sess <id: string, prot: formula>
// pred_prim Sess <id: string, name: string, prot: formula>
pred_prim Chan <id: string, sess: formula>

msg has form k /\ \pi
1   ~  emp /\ r:int /\ r=1
int ~  emp /\ r:int 

  /* role or communication instrument? */
  //S_role
  pred_msess sell = B1?String;B1!Int;B2!Int;(B2?1;B2?Addr;B2!Date \/ B2?0)
  //B1_role
  pred_msess buy1 = S!String;S?Int;B2!Int
  //B2_role
  pred_msess buy2 = B1?int * S?int ; (S!1; S!Addr ; S?Date \/ S!0).
                  |
                  |
                  V
  //S_role
  pred_msess sell(a,b) = a?String;a!Int;b!Int;(b?1;b?Addr;b!Date \/ b?0)
  //B1_role
  pred_msess buy1(a,b) = a!String;a?Int;b!Int
  //B2_role
  pred_msess buy2(a,b) = a?int * b?int ; (b!1; b!Addr ; b?Date \/ b!0).


void Buyer1(Channel sb1, Channel b1b2)
  requires Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,buy1(sb1,b1b2)>
  ensures  Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,emp>
{
  /* Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,buy1(sb1,b1b2)> */
  string book = getTitle();
  /* Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,sb1!String;sb1?Int;b1b2!Int> 
   ==================== ent check =================
  Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,b1b2!Int> */
  send(sb1, book);
  /* Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,sb1?Int;b1b2!Int> */
  int y1 = receive(sb1);
  /* Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,b1b2!Int> */
  send(b1b2, contrib(y1));
  /* Chan(sb1, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,emp> */
}

void Buyer2(Channel sb2, Channel b1b2)
  requires Chan(sb2, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,buy2>
  ensures  Chan(sb2, multi-s) * Chan(b1b2, multi-s) * Sess<multi-s,emp>
{
  int budget = getBudget();
  string address = getAddress();
  int z1 = receive(b1b2);
  int z2 = receive(sb2);
  if (z1 - z2 <= budget){
    send (sb2,1); //ok
    send(sb2, address);
    receive(sb2, date);
  } else {
    send(sb2, 0); //quit
  }
}

void Seller(Channel sb1, Channel sb2)
  requires Chan(sb1, multi-s) * Chan(sb2, multi-s) * Sess<multi-s,sell>
  ensures  Chan(sb1, multi-s) * Chan(sb2, multi-s) * Sess<multi-s,emp>
{
  string x1 = receive(sb1);
  send(sb1,quote(x1));
  send(sb2,quote(x1));
  int answer = receive(sb2);
  if (answer == 1) {
 	string x2 = receive(sb2);
 	send(sb2, getDate(x2,x1)); 
 }
}

void main ()
{
  //multi-s::Sess<buy1> * multi-s::Sess<buy2> * multi-s::Sess<sell>
  Channel sb1, sb2, b1b2;
  sb1 = new Channel();
  //sb1::Chan<multi-s>{S,B1}
  sb2 = new Channel();
  //sb2::Chan<multi-s>{S,B2}
  b1b2 = new Channel();
  //b1b2::Chan<multi-s>{B1,B2}

  Buyer1(sb1,b1b2) | Buyer2(sb1,b1b2) | Seller(sb1,sb2)
}



