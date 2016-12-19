pred_prim Fp<id:int,p:int>; //accumulator
pred_prim Fm<id:int,p:int,n:float>; //consumer

pred_prim Fp2<id:int,p:int,var>; //accumulator
pred_prim Fm2<id:int,p:int,var,n:float>; //consumer
  
//lemma_norm "ACC"  self::Fp<id,aa> * self::Fp<id,bb> & aa>=0 & bb>=0-> self::Fp<id,aa+bb>.
lemma_norm "ACC"  self::Fp<id1,aa> * self::Fp<id2,bb> & id1=id2 -> self::Fp<id,aa+bb>.
lemma_norm "REL"  self::Chan{@S Fp2<id,ppp,qq>;;%R}<> -> self::Chan{@S %R}<> * qq::Fp<id,ppp>.
/* lemma_norm "CONi" self::Chan{@S Fm2<id,pppp1,qq,mm> ;; %R}<> * qq::Fp<id,ppp2> & pppp1=ppp2 & mm<=1.0 -> self::Chan{@S %R}<> * qq::Fm<id,pppp1,1.0-mm>. */
lemma_norm "CONi" self::Chan{@S Fm2<id1,pppp1,qq,mm> ;; %R}<> * qq::Fp<id2,ppp2> & pppp1=ppp2 & id1=id2-> self::Chan{@S %R}<> * qq::Fm<id,pppp1,1.0-mm>.
/* lemma_norm "CON"  self::Chan{@S Fm2<id,ppp1,qq,mm> ;; %R}<> * qq::Fm<id,ppp1,nn> & nn>=mm-> self::Chan{@S %R}<> * qq::Fm<id,ppp1,nn-mm>. */
lemma_norm "CON"  self::Chan{@S Fm2<id1,ppp1,qq,mm> ;; %R}<> * qq::Fm<id2,ppp1,nn> & id1=id2-> self::Chan{@S %R}<> * qq::Fm<id,ppp1,nn-mm>.
lemma_norm "REM"  self::Fm<id,_,aaa> & aaa=0.0 -> emp.
