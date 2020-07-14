#!/usr/bin/env python3

# Aliased statements are of the form `[f| A * B & C |f]`, where `A,B,C` are operands, and `*,&` are operators.
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

grammar = Grammar(
    r"""
    entailment = space? head rest? space?
    head = heapPred / boolExp
    rest = space? restHead space? rest*
    restHead = operatorsTop (heapPred / boolExp)
    heapPred = "emp" / (exp "::" exp "<" exp? ">@M")
    boolExp = "true" / "false" / alias / notAlias / boolPred / boolCompare / quantifierPred
    alias = exp "=" exp
    notAlias = "!(" exp "=" exp ")"
    boolPred = exp "(" exp ")"
    boolCompare = exp operatorsCompare exp
    quantifierPred = exp "(" exp ":" entailment ")"
    exp = (var (operatorsExp exp)*) / (expEnclosed (operatorsExp exp)*)
    expEnclosed = "(" exp ")"
    operatorsTop = space? ("|-" / "*" / "&") space?
    operatorsCompare = space? ("<=" / ">=" / "<" / ">") space?
    operatorsExp = space? ("*" / "+" / "-") space?
    var = ~r"[a-zA-Z0-9_]+"
    space = ~r"\s+"
    """)

openSymbol='[f|'
closeSymbol='|f]'

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

    def visit_head(self, node, visited_children):
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

    def visit_restHead(self, node, visited_children):
        _, operand = node.children
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
            entailment = entailment.split('&{FLOW,(20,21)=__norm#E}[]', 1)[0]

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
