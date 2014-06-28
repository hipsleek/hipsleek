data cell {
  int x;
}

data chann {
  int y;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

pred_prim MSG2<c:cell>
inv c!=null;

int create_msg (int x)
  requires true
  ensures (exists v: res::MSG{v::cell<1> & true}<v>);

void send(int ch, cell c)
    requires ch::MSG{%P}<c>@L * %P
    ensures  emp;

 void receive(int ch, ref cell c)
    requires ch::MSG{%P}<c>@L // do we use c or c'??
    ensures  %P & c'=c;


/*
# msg.ss

parser problem with "chann as result"

P should be free:
         EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists P: HVar P&{FLOW,(24,25)=__norm})[]
                    



*/
