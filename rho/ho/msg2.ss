
data chan {
  int y;
}

data cell {
  int x;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

chan create_msg (int n)
  requires true
  ensures (exists v: res::MSG{v::cell<n> & true}<v>);

void send(chan ch, cell c)
    requires ch::MSG{%P}<c>@L * %P
    ensures  emp;

 void receive(chan ch, ref cell c)
    requires ch::MSG{%P}<a>@L // use an implicit var a
    ensures  %P & c'=a;


/*
# msg2.ss

static  :EBase exists (Expl)[](Impl)[a](ex)[]ch::MSG{ HVar P&{FLOW,(24,25)=__norm}[]}<a>@L&
        {FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume ref [c]
                    (exists P: HVar P&c'=a&{FLOW,(24,25)=__norm})[]

%P need to be made implicit on the pre-condition


*/
