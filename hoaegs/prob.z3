  PINE 4.64   MESSAGE TEXT                                      Folder: INBOX  Message 1 of 52,615 60%           

We need to think or preprocessing to make z3 perform
more better.

For example, it cannot handle existential below:

(assert (not (exists (?l_345 Int) (exists (?h_346 Int) (bnd a' t_41' j ?l_345 ?h_346)))))

and I get the following outcome:

z3 -smt2 x0.z3
unknown
(error "WARNING: For problems containing quantifiers, the model finding capabilities of Z3 work better when
the formula does not contain nested quantifiers. You can use PULL_NESTED_QUANTIFIERS=true to eliminate nested
quantifiers.")

Could you see how the suggested config PULL_NESTED_QUANTIFIERS=true works?

However, after explicit instantiation to below, the prover works!

(assert (not (bnd a' t_41' j (+ 1 x_42') h_298)))

as shown below:

z3 -smt2 x2.z3
unsat
(error "WARNING: For problems containing quantifiers, the model finding capabilities of Z3 work better when
the formula does not contain nested quantifiers. You can use PULL_NESTED_QUANTIFIERS=true to eliminate nested
quantifiers.")


However, when I wrote it as below:

 (assert (not (bnd a' t_41' j (+ x_42' 1) h_298)))

it fails...

z3 -smt2 x1.z3
unknown


