#!/usr/bin/env python3

# Entailments are of the form `[e|A * B & C |- D * E & F|e]`, where `A,B,C,D,E,F` are either boolean expressions or predicates, `*,&` are operators, and `|-` is the entailment symbol.
# It is assumed that all variables in the entailment have unique names.
# Aliases are boolean expressions of the form `alias=value`.
# This script has three steps:
# 1. Read line from input, and print same line to output.
# 2. Go to step 3 if line is not an entailment. Else, replace in `line` all occurences of `alias` with `value`, and remove from `line` all aliases.
# 3. Maybe print line (possibly with aliases removed) to output.

from sys import stdin
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor
from parsimonious.exceptions import ParseError

# `handside` stands for both "left hand side" and "right hand side".
grammar = Grammar(
    r"""
    entailment = space? handside proves handside space?
    handside = handsideHead handsideRest?
    handsideHead = boolExp / heapPred
    handsideRest = handsideRestHead handsideRest*
    handsideRestHead = (and boolExp) / (star heapPred)
    boolExp = "true" / "false" / alias / notAlias / boolPred / (exp ("<"/">"/"<="/">=") exp)
    alias = exp"="exp
    notAlias = "!("exp"="exp")"
    boolPred = exp"("exp")"
    heapPred = (space? "emp" space?) / (exp"::"exp"<"exp">@M")
    exp = (var (times/plus) exp) / ("(" var (times/plus) exp ")") / var
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

class AliasCollector(NodeVisitor):
    """Collect all occurences of `alias` with `value`.
    """

    def visit_alias(self, node, visited_children):
        alias, _, value = node.children
        return [(alias, value)]

    def generic_visit(self, node, visited_children):
        return [alias for child in visited_children for alias in child]

class VarReplacer(NodeVisitor):
    """Replace all occurences of `alias` with `value`.
    """

    def __init__(self, aliases):
        self.aliases = aliases

    def visit_var(self, node, visited_children):
        for (alias, value) in self.aliases:
            if alias.text == node.text:
                return value.text
        return node.text

    def generic_visit(self, node, visited_children):
        return ''.join(visited_children) if visited_children else node.text

class AliasRemover(NodeVisitor):
    """Remove a trivial alias, and also remove the operator before (if available).
    """

    def visit_handsideHead(self, node, visited_children):
        operand = node.children[0]
        if operand.expr_name == 'boolExp':
            child = operand.children[0]
            if child.expr_name == 'alias':
                alias, _, value = child
                if alias.text == value.text:
                    return ''
                else:
                    return ''.join(visited_children)
        return ''.join(visited_children)

    def visit_handsideRestHead(self, node, visited_children):
        _, operand = node.children[0]
        if operand.expr_name == 'boolExp':
            child = operand.children[0]
            if child.expr_name == 'alias':
                alias, _, value = child
                if alias.text == value.text:
                    return ''
                else:
                    return ''.join(visited_children)
        return ''.join(visited_children)

    def generic_visit(self, node, visited_children):
        return ''.join(visited_children) if visited_children else node.text

if __name__ == '__main__':

    # Step 1.
    for line in stdin:
        print(line, end='')

        # Although get multiple index of `openSymbol` and `closeSymbol` with intention to iterate through all combinations,
        # assume for now that `openSymbol` and `closeSymbol` are unique to entailments, and not used anywhere else.
        # That is, between an `openSymbol` and a `closeSymbol` must lie an entailment (and nothing else).
        # This assumption is useful for parsing entailments that span many lines.
        indexesOpen = get_indexes(line, openSymbol)
        indexesClose = get_indexes(line, closeSymbol)

        isNotEntailment = len(indexesOpen) == 0 and len(indexesClose) == 0
        isSpanOne = len(indexesOpen) == 1 and len(indexesClose) == 1
        isSpanMany = len(indexesOpen) == 1 and len(indexesClose) == 0
        if not isNotEntailment:

            # Extract entailments that possibly span multiple lines.
            entailmentChunks = []

            if isSpanOne:
                entailmentChunks.append(line[indexesOpen[0]+len(openSymbol):indexesClose[0]])

            elif isSpanMany:

                entailmentChunks.append(line[indexesOpen[0]+len(openSymbol):])

                # Step 1.
                for line in stdin:
                    print(line, end='')
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
            # Repeat until fixpoint.
            entailmentOld = entailment
            while True:
                tree = grammar.parse(entailment)
                ac = AliasCollector()
                aliases = ac.visit(tree)
                vr = VarReplacer(aliases)
                entailment = vr.visit(tree)
                if entailmentOld == entailment:
                    break
                entailmentOld = entailment

            tree = grammar.parse(entailment)
            ar = AliasRemover()
            entailment = ar.visit(tree)

            # Step 3.
            print(entailment)
