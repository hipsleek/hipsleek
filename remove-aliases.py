#!/usr/bin/env python3

# Entailments are of the form `[e|A * B & C |- D * E & F|e]`, where `A,B,C,D,E,F` are predicates, `*,&` are operators, and `|-` is the entailment symbol.
# It is assumed that all variables in the entailment have unique names.
# Aliases are predicates of the form `alias=value`.
# This script has three steps:
# 1. Read line from input.
# 2. Go to step 3 if line is not an entailment. Else, replace in `line` all occurences of `alias` with `value`, and remove from `line` all aliases.
# 3. Print line (possibly with aliases removed) to output.

from sys import stdin
from parsimonious.grammar import Grammar
from parsimonious.exceptions import ParseError

# `handside` stands for both "left hand side" and "right hand side".
grammar = Grammar(
    r"""
    entailment = space? handside proves handside space?
    handside = (boolExp handsideRest?) / (heapPred handsideRest?)
    handsideRest = (and boolExp handsideRest*) / (star heapPred handsideRest*)
    boolExp = alias / boolPred / (exp"<"exp) / (exp">"exp) / (exp"<="exp) / (exp">="exp)
    alias = exp"="exp
    boolPred = exp"("exp")"
    heapPred = (space? "emp" space?) / (exp"::"exp"<"exp">@M")
    exp = (var times exp) / (var plus exp) / var
    var = ~r"[a-zA-Z0-9_]+"
    proves = space? "|-" space?
    star = space? "*" space?
    and = space? "&" space?
    times = space? "*" space?
    plus = space? "+" space?
    space = ~r"\s+"
    """)

openSymbol='[e|'
closeSymbol='|e]'

def get_indexes(line, symbol):
    indexes = []
    index = line.find(symbol)
    if index != -1:
        while index != -1:
            indexes.append(index)
            index = line.find(symbol, index+1)
    return indexes

if __name__ == '__main__':

    # Step 1.
    for line in stdin:

        # Although get multiple index of `openSymbol` and `closeSymbol` with intention to iterate through all combinations,
        # assume for now that `openSymbol` and `closeSymbol` are unique to entailments, and not used anywhere else.
        # That is, between an `openSymbol` and a `closeSymbol` must lie an entailment (and nothing else).
        # This assumption is useful for parsing entailments that span many lines.
        indexesOpen = get_indexes(line, openSymbol)
        indexesClose = get_indexes(line, closeSymbol)

        isNotEntailment = len(indexesOpen) == 0 and len(indexesClose) == 0
        isSpanOne = len(indexesOpen) == 1 and len(indexesClose) == 1
        isSpanMany = len(indexesOpen) == 1 and len(indexesClose) == 0
        if isNotEntailment:

            # Step 3.
            print(line, end='')

        else:

            # Extract entailments that possibly span multiple lines.
            entailmentChunks = []

            if isSpanOne:
                entailmentChunks.append(line[indexesOpen[0]+len(openSymbol):indexesClose[0]])

            elif isSpanMany:

                entailmentChunks.append(line[indexesOpen[0]+len(openSymbol):])
                for line in stdin:
                    indexesOpen = get_indexes(line, openSymbol)
                    indexesClose = get_indexes(line, closeSymbol)
                    isIllegal = len(indexesOpen) == 1
                    isSpanEnd = len(indexesOpen) == 0 and len(indexesClose) == 1
                    if isIllegal:
                        raise Exception('Nested openSymbols are illegal')
                    elif isSpanEnd:
                        entailmentChunks.append(line[:indexesClose[0]])
                        break
                    else:
                        entailmentChunks.append(line)

            else:
                raise Exception('Unhandled case')

            entailment = ''.join(map(lambda x: x.strip(), entailmentChunks))

            # Step 2.
            # TODO
            print(entailment)
            print(grammar.parse(entailment))
