void inf_loop()
  requires cx::cex[] & Loop 
  ensures false; // []

bool randbool()
  requires Term[]
  ensures true;


void loop(int x, int y, int k)
  requires cex{[if#1,inf_loop]} & Loop
  ensures false; // cex{[if#1,inf_loop],if#2,inf_loop}
// ensures false {cex{[if#1,inf_loop],if#2,inf_loop}}
{
  if (randbool()) inf_loop(); // cex[if#1,inf_loop]
  else inf_loop(); // cex[if#2,inf_loop]
}

void foo() 
  requires cex{[if#1,inf_loop]} & Loop
  ensures true;
{
  loop(x,y,k);
}

void loop(int x, int y, int k)
  requires  Loop 
  ensures false; // cex{[if#1,inf_loop]}
{
  if (randbool()) inf_loop(); // cex[if#1,inf_loop]
  else return; // cex[]
}



void loop(int x, int y, int k)
  requires Loop * cex{[if#1,inf_loop],if#2,inf_loop}
  ensures false; 
  // cex{[if#1,inf_loop],if#2,inf_loop}
{
  if (rand) inf_loop(); // cex[if#1,inf_loop]
  else inf_loop(); // cex[if#2,inf_loop]
}


 cex[] \/ cex[if#1,inf_loop] |- cex[if#1,inf_loop]


  cex[if#1,inf_loop] \/ cex[if#2,inf_loop]
  |- cex[if#1,inf_loop] 


  LHS |- RHS

=================================================================

void loop(int x, int y, int k)
  requires Loop
 ensures (exist. cex{[]})
  // cex{[if#1,inf_loop],if#2,inf_loop}
{
  if (rand) inf_loop(); // cex[if#1,inf_loop]
  else inf_loop(); // cex[if#2,inf_loop]
}


 cex[] \/ cex[if#1,inf_loop] |- cex[if#1,inf_loop]


  cex[if#1,inf_loop] \/ cex[if#2,inf_loop]
  |- cex[if#1,inf_loop] 


  LHS |- RHS
