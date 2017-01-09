
data chan {
  int y;
}

data cell {
  int x;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

 void receive(chan ch, ref cell c)
    requires ch::MSG{%PPP}<a>@L // use an implicit var a
    ensures  %PPP & c'=a;


/*
# msg2.ss

static  :EBase exists (Expl)[](Impl)[a](ex)[]ch::MSG{ HVar P&{FLOW,(24,25)=__norm}[]}<a>@L&
        {FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume ref [c]
                    (exists P: HVar P&c'=a&{FLOW,(24,25)=__norm})[]

%P need to be made implicit on the pre-condition


*/
