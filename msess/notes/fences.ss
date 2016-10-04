pred_prim Fc<id:int,p:float>; //consumer
pred_prim Fa<id:int,p:float>; //accumulator

pred_prim Fc2<id:int,p:float,var>; //consumer
pred_prim Fa2<id:int,p:float,var>; //accumulator


lemma_norm "ACC"  self::Fa<id,aa> * self::Fa<id,bb> & aa+bb<=1.0-> self::Fa<id,aa+bb>.
lemma_norm "FULL" self::Fa<id,aaa> & aaa=1.0 -> self::Fc<id,1.0>.
lemma_norm "REL"  self::Chan{@S Fa2<id,ppp,qq>;;%R}<> -> self::Chan{@S %R}<> * qq::Fa<id,ppp>.
lemma_norm "CON"  self::Chan{@S Fc2<id,ppp1,qq> ;; %R}<> * qq::Fc<id,ppp2> & ppp2>=ppp1 -> self::Chan{@S %R}<> * qq::Fc<id,ppp2-ppp1>.
lemma_norm "REM"  self::Fc<id,aaa> & aaa=0.0 -> emp.
