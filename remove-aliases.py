#!/usr/bin/env python3

# Entailments are of the form `[e|A * B & C |- D * E & F|e]`, where `A,B,C,D,E,F` are predicates, `*,&` are operators, and `|-` is the entailment symbol.
# It is assumed that all variables in the entailment have unique names.
# Aliases are predicates of the form `alias=value`.
# This script has three steps:
# 1. Read line from input.
# 2. Go to step 3 if line is not an entailment. Else, replace in `line` all occurences of `alias` with `value`, and remove from `line` all aliases.
# 3. Print line (possibly with aliases removed) to output.

import sys

entailSymbol=' |- '
aliasSymbol='='
operatorSymbols=['*', '&']

if __name__ == '__main__':

    # Step 1.
    for line in sys.stdin:

        # Step 2.
        if entailSymbol in line:

            # Replace all occurences of `alias` with `value`.
            tokens = line.split(' ')
            for i in range(len(tokens)):
                token = tokens[i]
                if aliasSymbol in token:
                    (alias, value) = token.split(aliasSymbol)

                    # Although all variables have unique names, the following is not correct,
                    # since variables `b` and `b_107` have unique names, but with an alias `b=a`,
                    # then string replacement will convert the variable `b_107` into `a_107`.
                    # But to avoid parsing, this is the best solution.
                    line = line.replace(alias, value)

            # Remove all aliases.
            # Remove an alias, and also remove the operator before (if available).
            tokens = line.split(' ')
            tokensNoAliases = []
            for i in range(len(tokens)):
                token = tokens[i]
                if aliasSymbol in token:
                    (alias, value) = token.split(aliasSymbol)
                    if alias == value:
                        # Do not add to tokensNoAliases.
                        # Try to remove operator before.
                        if i-1 >= 0 and tokens[i-1] in operatorSymbols:
                            tokensNoAliases.pop()
                    else:
                        tokensNoAliases.append(token)
                else:
                    tokensNoAliases.append(token)

            # Collect tokensNoAliases.
            line = ' '.join(tokensNoAliases)

        # Step 3.
        print(line, end='')
