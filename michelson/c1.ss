/*
# NONE if user wants to get the value
# SOME (signed hash of the string, string)
parameter (option (pair signature (pair string nat)));
return string;
storage (pair (pair key nat) string);
code { DUP; CAR; DIP{CDR; DUP};
       IF_NONE { AMOUNT; PUSH tez "1.00"; # The fee I'm charging for queries
                 CMPLE; IF {} {FAIL};
                 CDR; PAIR}
               { SWAP; DIP{DUP}; CAAR; DIP{DUP; CAR; DIP{CDR; H}; PAIR};
                 CHECK_SIGNATURE; ASSERT; DUP; CDDR; DIIP{DUP; CADR};
                 DIP{SWAP}; ASSERT_CMPEQ;
                 CDR; DUP; DIP{CAR; DIP{CAAR}}; CDR; PUSH nat 1; ADD;
                 DIP{SWAP}; SWAP; PAIR; PAIR; PUSH string ""; PAIR}}
*/

data Storage {
	int key;
	int nat;
	int value;
}

data Parameter {
	int option; // Boolean
	int signature;
	int value;
	int nat;
}

data Transfer {
	int from;
	int amount;
	int result; // Boolean starts from 0
}

int code(Parameter p, Storage s, Transfer t)
	requires p::Parameter<option, signature, value1, nat1> * s::Storage<key, nat2, value2> * t::Transfer<from, amount, 0>
	ensures true;
{
	// DUP; CAR; DIP{CDR; DUP); IF_NONE
	if (p.option == 0) 
	{ // GET Part
		// AMOUNT; PUSH tez "1.00";
		int amount = t.amount;
		int tez = 1;
		// CMPLE; IF {} {FAIL};
		if (amount <= tez) {
			t.result = 0;
			return 0;
		}
		// CDR; PAIR
		t.result = 1;
		return s.value;
	}
	else
	{ // UPDATE Part
		// SWAP; DIP{DUP}; CAAR; DIP{DUP; CAR; DIP{CDR; H}; PAIR};
		int s_key = s.key;
		int p_sign = p.signature;
		int p_str = p.value;
		int p_nat = p.nat;
		int p_hash = p_str + p_nat; // HASHED p_str, p_nat (Take it as plus for now)
                // CHECK_SIGNATURE; ASSERT; DUP; CDDR; DIIP{DUP; CADR};
		if (s_key + p_hash != p_sign) { t.result = 0; return 0; }
                //  DIP{SWAP}; ASSERT_CMPEQ;
		if (s.nat != p.nat) { t.result = 0; return 0; }
                // CDR; DUP; DIP{CAR; DIP{CAAR}}; CDR; PUSH nat 1; ADD;
		s.nat = s.nat + 1;
		s.value = p.value;
                // DIP{SWAP}; SWAP; PAIR; PAIR; PUSH string ""; PAIR}
		t.result = 1;
		return 0;
	}
}
